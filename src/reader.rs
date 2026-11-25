//! Streaming reader for Lean's NDJSON kernel export, format version 3.
//!
//! The format is the one written by `leanexport` (Lean's `src/LeanExport`,
//! format 3.1.0 as of Lean v4.36.0; it descends from `lean4export`). Each
//! line is one JSON object:
//!
//! * the first line is `{"meta": {...}}`, carrying `format.version`;
//! * `{"in": i, "str"|"num": {...}}` binds name id `i` (0 is anonymous);
//! * `{"il": i, "succ"|"max"|"imax"|"param": ...}` binds level id `i`
//!   (0 is `Level.zero`);
//! * `{"ie": i, "bvar"|"sort"|"const"|"app"|"lam"|"forallE"|"letE"|"proj"|
//!   "natVal"|"strVal"|"mdata": ...}` binds expression id `i`;
//! * `{"axiom"|"def"|"thm"|"opaque"|"quot"|"inductive": {...}}` declares
//!   constants, and `inductive` carries a whole mutual block: its types,
//!   constructors and recursors.
//!
//! Records may only refer to ids bound on earlier lines. Ids need not be
//! dense or in order (the lean-kernel-arena tests check this), but each id
//! is bound once. Key order inside objects is irrelevant.
//!
//! The reader works one line at a time with a reused buffer, so memory is
//! bounded by the arenas, never by the file. Every structural problem is
//! reported with its line number; the reader does not panic on bad input.

use std::fmt;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Read};
use std::path::Path;
use std::sync::mpsc::{self, Receiver, SyncSender};

use hashbrown::HashMap;
use num_bigint::BigUint;

use crate::env::{
    Block, BlockKind, Decl, DeclKind, Env, Hints, LAZY_BASE, Meta, NameList, QuotKind, RecRule,
    Safety, is_lazy,
};
use crate::expr::{BinderInfo, ExprError, ExprId, ExprNode, LetBinder};
use crate::idmap::IdMap;
use crate::json::{Doc, Member, Tape, Val};
use crate::level::{LevelId, LevelNode};
use crate::name::{NameId, NameNode};
use crate::strings::Overflow;

mod fast;
mod lazy;
mod run;
mod scan;

/// The format major version this reader understands.
pub const FORMAT_MAJOR: &str = "3";

/// How a read failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorClass {
    /// The file could not be read.
    Io,
    /// The export declares a format version this reader does not support.
    Unsupported,
    /// The file is not a well-formed export (bad JSON, undefined or
    /// duplicate ids, missing fields, unknown record kinds, ...).
    Malformed,
    /// The file is well-formed, but no kernel would accept it as an
    /// environment (for now: a constant declared twice).
    Rejected,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReadError {
    /// 1-based line number, or 0 if not tied to a line.
    pub line: u64,
    pub class: ErrorClass,
    pub msg: String,
}

impl fmt::Display for ReadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.line > 0 {
            write!(f, "line {}: {}", self.line, self.msg)
        } else {
            f.write_str(&self.msg)
        }
    }
}

impl std::error::Error for ReadError {}

/// Line-level statistics of a read.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ReadStats {
    pub lines: u64,
    pub bytes: u64,
    /// Expression records that hash-consed onto an existing node (or were
    /// `mdata`, which maps to its inner expression).
    pub shared_exprs: u64,
    /// Heap bytes of the export-id maps at the end of the read (zero when
    /// ids were dense and in order). They are freed with the reader.
    pub id_map_bytes: usize,
}

struct Fail {
    class: ErrorClass,
    msg: String,
}

type R<T> = Result<T, Fail>;

fn bad<T>(msg: impl Into<String>) -> R<T> {
    Err(Fail {
        class: ErrorClass::Malformed,
        msg: msg.into(),
    })
}

impl From<Overflow> for Fail {
    fn from(o: Overflow) -> Self {
        Fail {
            class: ErrorClass::Malformed,
            msg: format!("capacity exceeded: {}", o.0),
        }
    }
}

impl From<ExprError> for Fail {
    fn from(e: ExprError) -> Self {
        match e {
            ExprError::Overflow(o) => o.into(),
            ExprError::BVarTooLarge(i) => Fail {
                class: ErrorClass::Malformed,
                msg: format!("bvar index {i} is too large"),
            },
        }
    }
}

/// Read an export from a file.
pub fn read_file(path: &Path) -> Result<(Env, ReadStats), ReadError> {
    read_file_with(path, &Options::default())
}

/// How to read an export.
#[derive(Clone, Copy, Debug, Default)]
pub struct Options {
    /// Leave theorem values unbuilt, to be built when checked (see
    /// [`crate::env::Env::value_into`]).
    pub lazy_proofs: bool,
    /// Threads for parsing a regular file (0: all cores; 1: one thread
    /// parses while another interns, as for a stream).
    pub threads: usize,
}

/// Read an export from a file, with options.
pub fn read_file_with(path: &Path, opts: &Options) -> Result<(Env, ReadStats), ReadError> {
    let f = File::open(path).map_err(|e| io_error(path, e))?;
    read_open_file(f, opts)
}

/// Read an export from standard input. When it is redirected from a
/// regular file, its size is used to pre-size the tables.
pub fn read_stdin() -> Result<(Env, ReadStats), ReadError> {
    read_stdin_with(&Options::default())
}

/// Read an export from standard input, with options.
pub fn read_stdin_with(opts: &Options) -> Result<(Env, ReadStats), ReadError> {
    use std::os::fd::AsFd;
    match io::stdin().as_fd().try_clone_to_owned() {
        Ok(fd) => read_open_file(File::from(fd), opts),
        Err(_) => read(io::stdin()),
    }
}

fn read_open_file(f: File, opts: &Options) -> Result<(Env, ReadStats), ReadError> {
    // Only a regular file's length says anything about its contents.
    let size = match f.metadata() {
        Ok(m) if m.is_file() => m.len(),
        _ => 0,
    };
    let threads = match opts.threads {
        0 => std::thread::available_parallelism().map_or(1, |n| n.get()),
        n => n,
    };
    if size == 0 {
        let r = run(
            state(opts, size, false),
            BufReader::with_capacity(1 << 20, f),
        )?;
        return Ok((r.env, r.stats));
    }
    // A regular file is read optimistically: names and expressions are
    // added without hash-consing (an export lists each once) and indexed
    // at the end. If two turn out equal after all, the file is read again
    // with hash-consing.
    let t0 = std::time::Instant::now();
    let mut st = state(opts, size, true);
    st.index_threads = Some(threads);
    let r = read_regular(&f, size, threads, st)?;
    if std::env::var_os("NITROLEAN_READ_PROFILE").is_some() {
        let index = INDEX_NS.load(std::sync::atomic::Ordering::Relaxed) as f64 / 1e9;
        eprintln!(
            "read {:.3} s (interning thread waited {:.3} s), index {:.3} s, duplicate {:?}",
            t0.elapsed().as_secs_f64() - index,
            WAIT_NS.load(std::sync::atomic::Ordering::Relaxed) as f64 / 1e9,
            index,
            r.dup
        );
    }
    match r.dup {
        None => Ok((r.env, r.stats)),
        Some(_) => {
            drop(r);
            let r = read_regular(&f, size, threads, state(opts, size, false))?;
            Ok((r.env, r.stats))
        }
    }
}

fn state(opts: &Options, size: u64, append: bool) -> State {
    let mut st = State::new();
    st.append = append;
    if opts.lazy_proofs {
        st.lazy = Some(Box::new(lazy::Builder::with_capacity(size)));
        // Export ids map to references (about one expression per 56
        // bytes of a real export).
        st.expr_ids.reserve((size / 56).min(1 << 31) as usize);
    }
    if !append {
        // About one name per 1 KiB of a real export.
        st.env.names.reserve((size / 1024).min(1 << 31) as usize);
        // About 94% of the lines of a real export are expressions, and a
        // line averages 55 bytes; reserving up front avoids rehashing the
        // big table. With lazy proofs, about a third of them are interned.
        let per = if opts.lazy_proofs { 192 } else { 64 };
        st.env.exprs.reserve((size / per).min(1 << 31) as usize);
    }
    st
}

fn read_regular(f: &File, size: u64, threads: usize, st: State) -> Result<Done, ReadError> {
    if threads > 1 {
        // The interning stage runs on this thread.
        let parsers = threads - 1;
        return run_with(st, |full, empty| {
            produce_parallel(f, size, parsers, full, empty)
        });
    }
    if threads == 1 {
        return read_single(f, st);
    }
    use std::io::{Seek, SeekFrom};
    let mut f = f.try_clone().map_err(|e| ReadError {
        line: 0,
        class: ErrorClass::Io,
        msg: format!("read error: {e}"),
    })?;
    f.seek(SeekFrom::Start(0)).map_err(|e| ReadError {
        line: 0,
        class: ErrorClass::Io,
        msg: format!("read error: {e}"),
    })?;
    run(st, BufReader::with_capacity(1 << 20, f))
}

fn io_error(path: &Path, e: io::Error) -> ReadError {
    ReadError {
        line: 0,
        class: ErrorClass::Io,
        msg: format!("{}: {e}", path.display()),
    }
}

/// Read an export from a byte stream.
pub fn read<Rd: Read + Send>(r: Rd) -> Result<(Env, ReadStats), ReadError> {
    read_buffered(BufReader::with_capacity(1 << 20, r))
}

/// Read an export held in memory (mainly for tests).
pub fn read_str(s: &str) -> Result<Env, ReadError> {
    read_buffered(s.as_bytes()).map(|(env, _)| env)
}

/// Read an export from a buffered stream, line by line.
pub fn read_buffered<B: BufRead + Send>(r: B) -> Result<(Env, ReadStats), ReadError> {
    run(State::new(), r).map(|r| (r.env, r.stats))
}

// The read is a two-stage pipeline. A parsing thread reads lines, parses
// the JSON and checks the shape of each name, level and expression record,
// turning it into a compact `Item` that still holds export ids. The calling
// thread resolves those ids and hash-conses the nodes, whose cost is mostly
// cache misses in the big tables. Declaration records (about 1% of lines)
// and the meta record travel as raw text and are parsed by the second
// stage. Items move in batches whose buffers are recycled, so neither stage
// allocates per line.

/// Lines per batch handed from the parsing thread to the interning thread.
const BATCH_LINES: usize = 8192;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Comp {
    /// Byte range in the batch text.
    Str(u32, u32),
    Num(u64),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RawLevel {
    Succ(u64),
    Max(u64, u64),
    IMax(u64, u64),
    Param(u64),
}

/// An expression record with its references still export ids.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RawExpr {
    BVar(u64),
    Sort(u64),
    /// Name, then a range of level ids in the batch's `us` list.
    Const(u64, u32, u32),
    App(u64, u64),
    Binder {
        pi: bool,
        bi: BinderInfo,
        name: u64,
        ty: u64,
        body: u64,
    },
    Let {
        name: u64,
        ty: u64,
        value: u64,
        body: u64,
        nondep: bool,
    },
    Proj(u64, u32, u64),
    /// Decimal digits, as a byte range in the batch text.
    Nat(u32, u32),
    Str(u32, u32),
    MData(u64),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Item {
    Name {
        id: u64,
        pre: u64,
        comp: Comp,
    },
    Level {
        id: u64,
        node: RawLevel,
    },
    Expr {
        id: u64,
        node: RawExpr,
    },
    /// A whole line (the meta record or a declaration), as a byte range in
    /// the batch text.
    Raw(u32, u32),
}

#[derive(Default)]
struct Batch {
    items: Vec<Item>,
    /// Line number of each item.
    lines: Vec<u64>,
    text: String,
    us: Vec<u64>,
    /// Scratch space for [`scan::line`].
    scratch: Vec<u64>,
    /// Set on the last batch: how the input ended, and the totals.
    end: Option<Result<(), ReadError>>,
    lines_read: u64,
    bytes_read: u64,
}

impl Batch {
    fn clear(&mut self) {
        self.items.clear();
        self.lines.clear();
        self.text.clear();
        self.us.clear();
    }

    fn push_text(&mut self, s: &str) -> R<(u32, u32)> {
        let start = self.text.len();
        let end = start + s.len();
        if end > u32::MAX as usize {
            return bad("line too long");
        }
        self.text.push_str(s);
        Ok((start as u32, end as u32))
    }

    fn text(&self, a: u32, b: u32) -> &str {
        &self.text[a as usize..b as usize]
    }

    fn src(&self) -> Src<'_> {
        Src {
            text: self.text.as_bytes(),
            us: &self.us,
        }
    }

    /// Add an item read by [`scan::line`] from `line`, copying its text
    /// into the batch.
    fn push_scanned(&mut self, line: &[u8], item: Item) -> R<()> {
        let mut copy = |a: u32, b: u32| -> R<(u32, u32)> {
            match std::str::from_utf8(&line[a as usize..b as usize]) {
                Ok(t) => self.push_text(t),
                Err(_) => bad("internal error: scanned text is not UTF-8"),
            }
        };
        let item = match item {
            Item::Name {
                id,
                pre,
                comp: Comp::Str(a, b),
            } => {
                let (a, b) = copy(a, b)?;
                Item::Name {
                    id,
                    pre,
                    comp: Comp::Str(a, b),
                }
            }
            Item::Expr {
                id,
                node: RawExpr::Nat(a, b),
            } => {
                let (a, b) = copy(a, b)?;
                Item::Expr {
                    id,
                    node: RawExpr::Nat(a, b),
                }
            }
            Item::Expr {
                id,
                node: RawExpr::Str(a, b),
            } => {
                let (a, b) = copy(a, b)?;
                Item::Expr {
                    id,
                    node: RawExpr::Str(a, b),
                }
            }
            other => other,
        };
        self.items.push(item);
        Ok(())
    }
}

/// Adds scanned records to a batch.
struct ToBatch<'a>(&'a mut Batch, Option<Fail>);

impl scan::Sink for ToBatch<'_> {
    fn app(&mut self, id: u64, f: u64, a: u64) -> R<()> {
        let node = RawExpr::App(f, a);
        self.0.items.push(Item::Expr { id, node });
        Ok(())
    }

    fn binder(
        &mut self,
        id: u64,
        pi: bool,
        bi: BinderInfo,
        name: u64,
        ty: u64,
        body: u64,
    ) -> R<()> {
        let node = RawExpr::Binder {
            pi,
            bi,
            name,
            ty,
            body,
        };
        self.0.items.push(Item::Expr { id, node });
        Ok(())
    }

    fn item(&mut self, item: Item, line: &[u8], us: &[u64]) -> R<()> {
        let item = match item {
            Item::Expr {
                id,
                node: RawExpr::Const(n, a, b),
            } => {
                let start = self.0.us.len();
                self.0.us.extend_from_slice(&us[a as usize..b as usize]);
                let Ok(end) = u32::try_from(self.0.us.len()) else {
                    return bad("too many universe levels in one batch");
                };
                Item::Expr {
                    id,
                    node: RawExpr::Const(n, start as u32, end),
                }
            }
            other => other,
        };
        self.0.push_scanned(line, item)
    }

    #[cold]
    fn fail(&mut self, f: Fail) {
        self.1 = Some(f);
    }
}

/// Applies scanned records at once.
impl scan::Sink for State {
    #[inline(never)]
    fn app(&mut self, id: u64, f: u64, a: u64) -> R<()> {
        if self.mdata.is_empty()
            && let Some(b) = self.lazy.as_deref_mut()
        {
            if b.app(id, f, a) {
                return Ok(());
            }
            self.eager()?;
        }
        let src = Src { text: &[], us: &[] };
        self.apply_expr(src, id, RawExpr::App(f, a))
    }

    #[inline(never)]
    fn binder(
        &mut self,
        id: u64,
        pi: bool,
        bi: BinderInfo,
        name: u64,
        ty: u64,
        body: u64,
    ) -> R<()> {
        if self.mdata.is_empty()
            && let Some(b) = self.lazy.as_deref_mut()
        {
            if let Some(n) = self.name_ids.get(name)
                && b.binder(id, pi, bi, NameId(n), ty, body)
            {
                return Ok(());
            }
            self.eager()?;
        }
        let src = Src { text: &[], us: &[] };
        let node = RawExpr::Binder {
            pi,
            bi,
            name,
            ty,
            body,
        };
        self.apply_expr(src, id, node)
    }

    fn item(&mut self, item: Item, line: &[u8], us: &[u64]) -> R<()> {
        self.apply(Src { text: line, us }, item)
    }

    fn decl(&mut self, d: &scan::Decl, us: &[u64]) -> Option<R<()>> {
        Some(self.scanned_decl(d, us))
    }

    #[cold]
    fn fail(&mut self, f: Fail) {
        self.failed = Some(f);
    }
}

/// Where the text and level ranges of an item point: a batch's buffers,
/// or (for [`scan::line`]) the input line and a level list.
#[derive(Clone, Copy)]
struct Src<'a> {
    text: &'a [u8],
    us: &'a [u64],
}

impl<'a> Src<'a> {
    fn text(&self, a: u32, b: u32) -> R<&'a str> {
        match std::str::from_utf8(&self.text[a as usize..b as usize]) {
            Ok(t) => Ok(t),
            Err(_) => bad("internal error: item text is not UTF-8"),
        }
    }
}

fn run<B: BufRead + Send>(st: State, r: B) -> Result<Done, ReadError> {
    run_with(st, |full, empty| produce(r, full, empty))
}

fn run_with(
    st: State,
    produce: impl FnOnce(SyncSender<Batch>, Receiver<Batch>) + Send,
) -> Result<Done, ReadError> {
    finish(st, |st| {
        let (full_tx, full_rx) = mpsc::sync_channel::<Batch>(4);
        let (empty_tx, empty_rx) = mpsc::sync_channel::<Batch>(8);
        std::thread::scope(|s| {
            s.spawn(move || produce(full_tx, empty_rx));
            st.consume(full_rx, empty_tx)
        })
    })
}

/// What [`finish`] gives: the environment, the totals, and (when the
/// read added names and expressions without hash-consing them) a pair of
/// equal ones that indexing them found.
struct Done {
    env: Env,
    stats: ReadStats,
    dup: Option<(u32, u32)>,
}

/// Run `read` on `st`, then complete the environment and the totals (and
/// index it, if `st` says so).
fn finish(
    mut st: State,
    read: impl FnOnce(&mut State) -> Result<ReadStats, ReadError>,
) -> Result<Done, ReadError> {
    let res = read(&mut st);
    let id_map_bytes =
        st.name_ids.heap_bytes() + st.level_ids.heap_bytes() + st.expr_ids.heap_bytes();
    // The id maps are done with: free them before the lazy values are
    // put together.
    for m in [&mut st.name_ids, &mut st.level_ids, &mut st.expr_ids] {
        *m = IdMap::new(0);
    }
    if let Some(b) = st.lazy.take() {
        st.env.lazy = b.finish();
    }
    let mut stats = res?;
    stats.shared_exprs = st.shared_exprs;
    stats.id_map_bytes = id_map_bytes;
    let mut dup = None;
    if let Some(threads) = st.index_threads {
        let t = std::time::Instant::now();
        dup = match st.env.names.index(threads) {
            Err((a, b)) => Some((a.0, b.0)),
            Ok(()) => st.env.exprs.index(threads).err().map(|(a, b)| (a.0, b.0)),
        };
        INDEX_NS.store(
            t.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
    }
    Ok(Done {
        env: st.env,
        stats,
        dup,
    })
}

/// Read a regular file on this thread alone: blocks of whole lines are
/// read into one buffer, and each line is scanned and applied at once.
fn read_single(f: &File, st: State) -> Result<Done, ReadError> {
    use std::os::unix::fs::FileExt;
    const BLOCK: usize = 1 << 20;
    if let Some(m) = crate::olean::Mapped::new(f) {
        return finish(st, |st| map_lines(st, &m));
    }
    finish(st, |st| {
        let mut lines = Lines::default();
        let mut buf = vec![0u8; BLOCK];
        // Bytes in `buf`, and the file offset after them.
        let (mut have, mut off) = (0usize, 0u64);
        loop {
            if have == buf.len() {
                // A line longer than the buffer.
                buf.resize(buf.len() * 2, 0);
            }
            let n = loop {
                match f.read_at(&mut buf[have..], off) {
                    Ok(n) => break n,
                    Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                    Err(e) => {
                        return Err(ReadError {
                            line: lines.lines + 1,
                            class: ErrorClass::Io,
                            msg: format!("read error: {e}"),
                        });
                    }
                }
            };
            have += n;
            off += n as u64;
            if n == 0 {
                st.lines(&mut lines, &buf[..have])?;
                return st.end_lines(lines);
            }
            // Apply the whole lines, and keep the start of the last one.
            if let Some(p) = buf[..have].iter().rposition(|&b| b == b'\n') {
                st.lines(&mut lines, &buf[..p + 1])?;
                buf.copy_within(p + 1..have, 0);
                have -= p + 1;
            }
        }
    })
}

/// Apply the lines of a mapped file, a step of whole lines at a time; the
/// pages of each step go back after it.
fn map_lines(st: &mut State, m: &crate::olean::Mapped) -> Result<ReadStats, ReadError> {
    const STEP: usize = 16 << 20;
    let b = m.bytes();
    let mut lines = Lines::default();
    let mut pos = 0;
    while b.len() - pos > STEP {
        // The whole lines that start in the step (a line longer than the
        // step goes with them).
        let end = match memchr_from(b, pos + STEP) {
            Some(p) => p + 1,
            None => break,
        };
        st.lines(&mut lines, &b[pos..end])?;
        // The step's last page may hold the start of the next one: it is
        // read back from the page cache.
        m.release(pos, end);
        pos = end;
    }
    st.lines(&mut lines, &b[pos..])?;
    m.release(pos, b.len());
    st.end_lines(lines)
}

/// The first newline at or after `from`.
fn memchr_from(b: &[u8], from: usize) -> Option<usize> {
    b[from..].iter().position(|&c| c == b'\n').map(|p| from + p)
}

/// Time the index at the end of a read took (for
/// `NITROLEAN_READ_PROFILE`).
static INDEX_NS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Time the interning stage waited for batches (for
/// `NITROLEAN_READ_PROFILE`).
static WAIT_NS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Bytes of a file each parsing thread reads at a time.
const CHUNK: u64 = 4 << 20;

/// The parsing stage for a regular file, on `threads` threads: thread `t`
/// parses chunks `t`, `t + threads`, ... (each the whole lines that start
/// in it), and this thread forwards their batches in file order, with
/// line numbers made absolute.
fn produce_parallel(
    f: &File,
    size: u64,
    threads: usize,
    full: SyncSender<Batch>,
    empty: Receiver<Batch>,
) {
    let chunks = size.div_ceil(CHUNK).max(1) as usize;
    let threads = threads.clamp(1, chunks);
    // Batches the interning stage is done with, for the parsers to reuse
    // (so that their buffers are not freed and allocated again).
    let pool = std::sync::Mutex::new(Vec::<Batch>::new());
    std::thread::scope(|s| {
        let mut rxs = Vec::new();
        for t in 0..threads {
            let (tx, rx) = mpsc::sync_channel::<Batch>(1);
            rxs.push(rx);
            let pool = &pool;
            s.spawn(move || {
                let mut tape = Tape::new();
                let mut buf = Vec::new();
                for c in (t..chunks).step_by(threads) {
                    let b = pool.lock().unwrap_or_else(|e| e.into_inner()).pop();
                    let b = parse_chunk(f, size, c as u64, &mut tape, &mut buf, b);
                    let stop = b.end.as_ref().is_some_and(|e| e.is_err());
                    if tx.send(b).is_err() || stop {
                        return;
                    }
                }
            });
        }
        let (mut lines, mut bytes) = (0u64, 0u64);
        for c in 0..chunks {
            while let Ok(mut b) = empty.try_recv() {
                b.clear();
                b.end = None;
                pool.lock().unwrap_or_else(|e| e.into_inner()).push(b);
            }
            let Ok(mut b) = rxs[c % threads].recv() else {
                return;
            };
            for l in &mut b.lines {
                *l += lines;
            }
            let err = match b.end.take() {
                Some(Err(mut e)) => {
                    e.line += lines;
                    Some(e)
                }
                _ => None,
            };
            lines += b.lines_read;
            bytes += b.bytes_read;
            let last = err.is_some() || c + 1 == chunks;
            if last {
                b.end = Some(err.map_or(Ok(()), Err));
                b.lines_read = lines;
                b.bytes_read = bytes;
            }
            if full.send(b).is_err() || last {
                // Unblock the parsers before the scope joins them.
                drop(rxs);
                return;
            }
        }
    });
}

/// Parse chunk `c` of a file: the lines that start in bytes
/// `[c * CHUNK, (c + 1) * CHUNK)`. Line numbers are relative to the
/// chunk; `lines_read` and `bytes_read` are the chunk's.
fn parse_chunk(
    f: &File,
    size: u64,
    c: u64,
    tape: &mut Tape,
    buf: &mut Vec<u8>,
    batch: Option<Batch>,
) -> Batch {
    use std::os::unix::fs::FileExt;
    let mut batch = batch.unwrap_or_default();
    let (lo, hi) = (c * CHUNK, ((c + 1) * CHUNK).min(size));
    // Read the chunk, one byte before it (to see whether a line starts at
    // `lo`), and on until the end of its last line.
    let from = lo.saturating_sub(1);
    buf.clear();
    let mut end = hi;
    let res: io::Result<()> = (|| {
        buf.resize((hi - from) as usize, 0);
        f.read_exact_at(buf, from)?;
        while end < size && buf.last() != Some(&b'\n') {
            let n = (64 << 10).min(size - end) as usize;
            let k = buf.len();
            buf.resize(k + n, 0);
            f.read_exact_at(&mut buf[k..], end)?;
            end += n as u64;
            // Keep only up to the first newline of what was added.
            if let Some(p) = buf[k..].iter().position(|&b| b == b'\n') {
                end -= (n - p - 1) as u64;
                buf.truncate(k + p + 1);
            }
        }
        Ok(())
    })();
    if let Err(e) = res {
        batch.end = Some(Err(ReadError {
            line: 1,
            class: ErrorClass::Io,
            msg: format!("read error: {e}"),
        }));
        return batch;
    }
    // Skip the line that started before `lo`.
    let mut pos = if c == 0 {
        0
    } else {
        match buf.iter().position(|&b| b == b'\n') {
            Some(p) => p + 1,
            None => buf.len(),
        }
    };
    let mut seen_first = c != 0;
    let mut lines = 0u64;
    let mut bytes = 0u64;
    while pos < buf.len() {
        if seen_first {
            let mut us = std::mem::take(&mut batch.scratch);
            let mut sink = ToBatch(&mut batch, None);
            let got = scan::line(&buf[pos..], &mut us, &mut sink);
            let failed = sink.1;
            batch.scratch = us;
            if let Some((n, took)) = got {
                lines += 1;
                bytes += n as u64;
                if !took {
                    let f = failed.expect("a failure");
                    batch.end = Some(Err(ReadError {
                        line: lines,
                        class: f.class,
                        msg: f.msg,
                    }));
                    break;
                }
                batch.lines.push(lines);
                pos += n;
                continue;
            }
        }
        let next = match buf[pos..].iter().position(|&b| b == b'\n') {
            Some(p) => pos + p + 1,
            None => buf.len(),
        };
        let line = &buf[pos..next];
        lines += 1;
        bytes += line.len() as u64;
        let before = batch.items.len();
        if let Err(f) = parse_line(tape, line, &mut batch, &mut seen_first) {
            batch.end = Some(Err(ReadError {
                line: lines,
                class: f.class,
                msg: f.msg,
            }));
            break;
        }
        if batch.items.len() > before {
            batch.lines.push(lines);
        }
        pos = next;
    }
    batch.lines_read = lines;
    batch.bytes_read = bytes;
    batch
}

/// The parsing stage. Stops at the end of input, at the first error (which
/// it forwards), or when the consumer hangs up.
fn produce<B: BufRead>(mut r: B, full: SyncSender<Batch>, empty: Receiver<Batch>) {
    let mut tape = Tape::new();
    let mut buf = Vec::new();
    let (mut lines, mut bytes) = (0u64, 0u64);
    let mut seen_first = false;
    let mut batch = Batch::default();
    let end = loop {
        buf.clear();
        let n = match r.read_until(b'\n', &mut buf) {
            Ok(n) => n,
            Err(e) => {
                break Err(ReadError {
                    line: lines + 1,
                    class: ErrorClass::Io,
                    msg: format!("read error: {e}"),
                });
            }
        };
        if n == 0 {
            break Ok(());
        }
        lines += 1;
        bytes += n as u64;
        let before = batch.items.len();
        if let Err(f) = parse_line(&mut tape, &buf, &mut batch, &mut seen_first) {
            break Err(ReadError {
                line: lines,
                class: f.class,
                msg: f.msg,
            });
        }
        if batch.items.len() > before {
            batch.lines.push(lines);
        }
        if batch.items.len() >= BATCH_LINES {
            let next = empty.try_recv().unwrap_or_default();
            if full.send(std::mem::replace(&mut batch, next)).is_err() {
                return;
            }
        }
    };
    batch.end = Some(end);
    batch.lines_read = lines;
    batch.bytes_read = bytes;
    let _ = full.send(batch);
}

/// Parse one line into at most one item.
fn parse_line(tape: &mut Tape, buf: &[u8], batch: &mut Batch, seen_first: &mut bool) -> R<()> {
    if *seen_first {
        let mut us = std::mem::take(&mut batch.scratch);
        let mut sink = ToBatch(batch, None);
        let got = scan::line(buf, &mut us, &mut sink);
        let failed = sink.1;
        batch.scratch = us;
        if let Some((n, took)) = got {
            debug_assert_eq!(n, buf.len());
            return match failed {
                Some(f) if !took => Err(f),
                _ => Ok(()),
            };
        }
    }
    let line = match std::str::from_utf8(buf) {
        Ok(s) => s,
        Err(e) => return bad(format!("invalid UTF-8 at column {}", e.valid_up_to() + 1)),
    };
    if line.trim_ascii().is_empty() {
        return Ok(());
    }
    if !*seen_first {
        // The meta record; the second stage checks it.
        *seen_first = true;
        let (a, b) = batch.push_text(line)?;
        batch.items.push(Item::Raw(a, b));
        return Ok(());
    }
    if let Some(item) = fast::parse(line, batch) {
        batch.items.push(item);
        return Ok(());
    }
    let (doc, members) = parse_object(tape, line)?;
    let item = match id_record(doc, members, batch)? {
        Some(item) => item,
        None => {
            let (a, b) = batch.push_text(line)?;
            Item::Raw(a, b)
        }
    };
    batch.items.push(item);
    Ok(())
}

fn parse_object<'a>(tape: &'a mut Tape, line: &'a str) -> R<(Doc<'a>, &'a [Member])> {
    let (doc, root) = match tape.parse(line) {
        Ok(x) => x,
        Err(e) => return bad(e.to_string()),
    };
    match doc.members(root) {
        Some(m) => Ok((doc, m)),
        None => bad("expected a JSON object"),
    }
}

/// Parse a name, level or expression record; `None` for other records.
fn id_record(doc: Doc<'_>, members: &[Member], batch: &mut Batch) -> R<Option<Item>> {
    // Such records are {idkey: n, kind: payload}, in either key order.
    let mut found = None;
    for (i, m) in members.iter().enumerate() {
        let t = match doc.key(m) {
            "in" => Table::Name,
            "il" => Table::Level,
            "ie" => Table::Expr,
            _ => continue,
        };
        found = Some((i, t));
        break;
    }
    let Some((i, table)) = found else {
        return Ok(None);
    };
    if members.len() != 2 {
        return bad(format!(
            "{} record must have exactly two fields, found {}",
            table.noun(),
            members.len()
        ));
    }
    let Some(id) = doc.nat(members[i].val) else {
        let id_key = doc.key(&members[i]);
        return bad(format!("'{id_key}' must be a natural number"));
    };
    let payload = &members[1 - i];
    let (kind, v) = (doc.key(payload), payload.val);
    Ok(Some(match table {
        Table::Name => name_item(doc, id, kind, v, batch)?,
        Table::Level => Item::Level {
            id,
            node: level_item(doc, kind, v)?,
        },
        Table::Expr => Item::Expr {
            id,
            node: expr_item(doc, kind, v, batch)?,
        },
    }))
}

fn val_nat(doc: Doc<'_>, v: Val, what: &str) -> R<u64> {
    match doc.nat(v) {
        Some(n) => Ok(n),
        None => bad(format!("{what} must be a natural number")),
    }
}

fn name_item(doc: Doc<'_>, id: u64, kind: &str, v: Val, batch: &mut Batch) -> R<Item> {
    match kind {
        "str" => {
            let o = Obj::new(doc, v, "name.str")?;
            let pre = o.nat("pre")?;
            let (a, b) = batch.push_text(o.str("str")?)?;
            Ok(Item::Name {
                id,
                pre,
                comp: Comp::Str(a, b),
            })
        }
        "num" => {
            let o = Obj::new(doc, v, "name.num")?;
            Ok(Item::Name {
                id,
                pre: o.nat("pre")?,
                comp: Comp::Num(o.nat("i")?),
            })
        }
        _ => bad(format!("unknown name record kind '{kind}'")),
    }
}

fn level_item(doc: Doc<'_>, kind: &str, v: Val) -> R<RawLevel> {
    let pair = |what: &str| -> R<(u64, u64)> {
        match doc.elems(v) {
            Some(&[a, b]) => Ok((val_nat(doc, a, what)?, val_nat(doc, b, what)?)),
            _ => bad(format!("{what} must be an array of two level ids")),
        }
    };
    Ok(match kind {
        "succ" => RawLevel::Succ(val_nat(doc, v, "level.succ")?),
        "max" => {
            let (a, b) = pair("level.max")?;
            RawLevel::Max(a, b)
        }
        "imax" => {
            let (a, b) = pair("level.imax")?;
            RawLevel::IMax(a, b)
        }
        "param" => RawLevel::Param(val_nat(doc, v, "level.param")?),
        _ => return bad(format!("unknown level record kind '{kind}'")),
    })
}

fn expr_item(doc: Doc<'_>, kind: &str, v: Val, batch: &mut Batch) -> R<RawExpr> {
    Ok(match kind {
        "bvar" => RawExpr::BVar(val_nat(doc, v, "expr.bvar")?),
        "sort" => RawExpr::Sort(val_nat(doc, v, "expr.sort")?),
        "const" => {
            let o = Obj::new(doc, v, "expr.const")?;
            let name = o.nat("name")?;
            let us = o.arr("us")?;
            let start = batch.us.len();
            for &u in us {
                batch
                    .us
                    .push(val_nat(doc, u, "expr.const: entries of 'us'")?);
            }
            if batch.us.len() > u32::MAX as usize {
                return bad("line too long");
            }
            RawExpr::Const(name, start as u32, batch.us.len() as u32)
        }
        "app" => {
            let o = Obj::new(doc, v, "expr.app")?;
            RawExpr::App(o.nat("fn")?, o.nat("arg")?)
        }
        "lam" | "forallE" => {
            let pi = kind == "forallE";
            let o = Obj::new(doc, v, if pi { "expr.forallE" } else { "expr.lam" })?;
            RawExpr::Binder {
                pi,
                name: o.nat("name")?,
                ty: o.nat("type")?,
                body: o.nat("body")?,
                bi: binder_info(o.str("binderInfo")?)?,
            }
        }
        "letE" => {
            let o = Obj::new(doc, v, "expr.letE")?;
            RawExpr::Let {
                name: o.nat("name")?,
                ty: o.nat("type")?,
                value: o.nat("value")?,
                body: o.nat("body")?,
                nondep: o.bool("nondep")?,
            }
        }
        "proj" => {
            let o = Obj::new(doc, v, "expr.proj")?;
            RawExpr::Proj(o.nat("typeName")?, o.u32("idx")?, o.nat("struct")?)
        }
        "natVal" => {
            let Some(s) = doc.str(v) else {
                return bad("expr.natVal must be a string of decimal digits");
            };
            if s.is_empty() || !s.bytes().all(|c| c.is_ascii_digit()) {
                return bad(format!(
                    "expr.natVal must be a string of decimal digits, found {s:?}"
                ));
            }
            let (a, b) = batch.push_text(s)?;
            RawExpr::Nat(a, b)
        }
        "strVal" => {
            let Some(s) = doc.str(v) else {
                return bad("expr.strVal must be a string");
            };
            let (a, b) = batch.push_text(s)?;
            RawExpr::Str(a, b)
        }
        "mdata" => {
            let o = Obj::new(doc, v, "expr.mdata")?;
            let inner = o.nat("expr")?;
            o.obj("data", "expr.mdata.data")?;
            RawExpr::MData(inner)
        }
        _ => return bad(format!("unknown expression record kind '{kind}'")),
    })
}

/// Typed access to the fields of a JSON object, with error messages naming
/// the record and field.
#[derive(Clone, Copy)]
struct Obj<'a> {
    doc: Doc<'a>,
    m: &'a [Member],
    what: &'static str,
}

impl<'a> Obj<'a> {
    fn new(doc: Doc<'a>, v: Val, what: &'static str) -> R<Self> {
        match doc.members(v) {
            Some(m) => Ok(Obj { doc, m, what }),
            None => bad(format!("{what}: expected an object")),
        }
    }

    fn opt(&self, k: &str) -> Option<Val> {
        self.doc.get(self.m, k)
    }

    fn field(&self, k: &str) -> R<Val> {
        match self.opt(k) {
            Some(v) => Ok(v),
            None => bad(format!("{}: missing field '{k}'", self.what)),
        }
    }

    fn nat(&self, k: &str) -> R<u64> {
        let v = self.field(k)?;
        match self.doc.nat(v) {
            Some(n) => Ok(n),
            None => bad(format!(
                "{}: field '{k}' must be a natural number",
                self.what
            )),
        }
    }

    fn u32(&self, k: &str) -> R<u32> {
        match u32::try_from(self.nat(k)?) {
            Ok(n) => Ok(n),
            Err(_) => bad(format!("{}: field '{k}' is out of range", self.what)),
        }
    }

    fn bool(&self, k: &str) -> R<bool> {
        match self.field(k)? {
            Val::Bool(b) => Ok(b),
            _ => bad(format!("{}: field '{k}' must be a boolean", self.what)),
        }
    }

    fn str(&self, k: &str) -> R<&'a str> {
        match self.doc.str(self.field(k)?) {
            Some(s) => Ok(s),
            None => bad(format!("{}: field '{k}' must be a string", self.what)),
        }
    }

    fn arr(&self, k: &str) -> R<&'a [Val]> {
        match self.doc.elems(self.field(k)?) {
            Some(s) => Ok(s),
            None => bad(format!("{}: field '{k}' must be an array", self.what)),
        }
    }

    fn obj(&self, k: &str, what: &'static str) -> R<Obj<'a>> {
        Obj::new(self.doc, self.field(k)?, what)
    }
}

/// The positions at which an export expression contains metadata.
#[derive(Clone, Copy, PartialEq, Eq)]
enum MData {
    Root,
    Spine,
    Nested,
}

struct State {
    env: Env,
    name_ids: IdMap,
    level_ids: IdMap,
    expr_ids: IdMap,
    // Expression ids whose source contains metadata. The interned terms
    // remain transparent for ordinary type checking and reduction.
    mdata: HashMap<u64, MData>,
    shared_exprs: u64,
    // Scratch buffers, reused across records.
    levels_buf: Vec<LevelId>,
    names_buf: Vec<NameId>,
    rules_buf: Vec<RecRule>,
    /// With lazy proofs: a record per expression id (see `lazy`).
    lazy: Option<Box<lazy::Builder>>,
    /// Add expressions without hash-consing them (see `read_open_file`).
    append: bool,
    /// The failure of a line [`scan::line`] gave to this state.
    failed: Option<Fail>,
    /// With `append`: index the names and expressions at the end, on
    /// this many threads.
    index_threads: Option<usize>,
}

/// The state of [`State::lines`] between blocks of input.
#[derive(Default)]
struct Lines {
    tape: Tape,
    /// For lines the scanner leaves to the other parsers.
    batch: Batch,
    us: Vec<u64>,
    seen_first: bool,
    seen_meta: bool,
    lines: u64,
    bytes: u64,
}

/// The length of the line at the start of `s`, its newline included.
fn line_len(s: &[u8]) -> usize {
    match s.iter().position(|&b| b == b'\n') {
        Some(p) => p + 1,
        None => s.len(),
    }
}

/// The single-constant declaration records.
#[derive(Clone, Copy)]
enum Single {
    Axiom,
    Def,
    Thm,
    Opaque,
    Quot,
}

impl Single {
    fn what(self) -> &'static str {
        match self {
            Single::Axiom => "axiom",
            Single::Def => "def",
            Single::Thm => "thm",
            Single::Opaque => "opaque",
            Single::Quot => "quot",
        }
    }
}

/// Which table an id belongs to, for messages.
#[derive(Clone, Copy)]
enum Table {
    Name,
    Level,
    Expr,
}

impl Table {
    fn noun(self) -> &'static str {
        match self {
            Table::Name => "name",
            Table::Level => "level",
            Table::Expr => "expression",
        }
    }
}

#[cold]
fn undefined<T>(t: Table, id: u64) -> R<T> {
    bad(format!(
        "reference to undefined {} id {id} (ids must be defined on an earlier line)",
        t.noun()
    ))
}

fn twice(t: Table, id: u64) -> R<()> {
    bad(format!("{} id {id} is defined twice", t.noun()))
}

fn parse_nat_lit(s: &str) -> Option<BigUint> {
    if s.is_empty() || !s.bytes().all(|c| c.is_ascii_digit()) {
        return None;
    }
    if s.len() <= 19 {
        return s.parse::<u64>().ok().map(BigUint::from);
    }
    BigUint::parse_bytes(s.as_bytes(), 10)
}

fn binder_info(s: &str) -> R<BinderInfo> {
    Ok(match s {
        "default" => BinderInfo::Default,
        "implicit" => BinderInfo::Implicit,
        "strictImplicit" => BinderInfo::StrictImplicit,
        "instImplicit" => BinderInfo::InstImplicit,
        _ => return bad(format!("unknown binder info '{s}'")),
    })
}

impl State {
    fn new() -> Self {
        State {
            env: Env::new(),
            // Name 0 is anonymous and level 0 is zero, implicitly.
            name_ids: IdMap::new(1),
            level_ids: IdMap::new(1),
            expr_ids: IdMap::new(0),
            mdata: HashMap::new(),
            shared_exprs: 0,
            levels_buf: Vec::new(),
            names_buf: Vec::new(),
            rules_buf: Vec::new(),
            lazy: None,
            append: false,
            failed: None,
            index_threads: None,
        }
    }

    fn lookup(&self, t: Table, id: u64) -> R<u32> {
        let m = match t {
            Table::Name => &self.name_ids,
            Table::Level => &self.level_ids,
            Table::Expr => &self.expr_ids,
        };
        match m.get(id) {
            Some(x) => Ok(x),
            None => undefined(t, id),
        }
    }

    #[inline(always)]
    fn bind(&mut self, t: Table, id: u64, target: u32) -> R<()> {
        let m = match t {
            Table::Name => &mut self.name_ids,
            Table::Level => &mut self.level_ids,
            Table::Expr => &mut self.expr_ids,
        };
        match m.bind(id, target) {
            Ok(()) => Ok(()),
            Err(_) => twice(t, id),
        }
    }

    fn name(&self, id: u64) -> R<NameId> {
        Ok(NameId(self.lookup(Table::Name, id)?))
    }

    fn level(&self, id: u64) -> R<LevelId> {
        Ok(LevelId(self.lookup(Table::Level, id)?))
    }

    fn expr(&self, id: u64) -> R<ExprId> {
        Ok(ExprId(self.lookup(Table::Expr, id)?))
    }

    /// A declaration's term, interned.
    fn root(&mut self, id: u64) -> R<ExprId> {
        match &mut self.lazy {
            None => self.expr(id),
            Some(b) if b.has(id) => b.promote(&mut self.env, self.append, id),
            Some(_) => undefined(Table::Expr, id),
        }
    }

    /// A theorem's value: interned, or with lazy proofs, left for later.
    fn thm_value(&mut self, id: u64) -> R<ExprId> {
        match &mut self.lazy {
            None => self.expr(id),
            Some(b) if b.has(id) => b.value(id),
            Some(_) => undefined(Table::Expr, id),
        }
    }

    fn meta(&mut self, doc: Doc<'_>, members: &[Member]) -> R<()> {
        let Some(v) = doc.get(members, "meta") else {
            return bad("expected the meta record {\"meta\": ...} on the first line");
        };
        let meta = Obj::new(doc, v, "meta")?;
        let format = meta.obj("format", "meta.format")?;
        let version = format.str("version")?;
        if version.split('.').next() != Some(FORMAT_MAJOR) {
            return Err(Fail {
                class: ErrorClass::Unsupported,
                msg: format!(
                    "unsupported export format version {version} (expected {FORMAT_MAJOR}.x)"
                ),
            });
        }
        let opt_str = |o: Option<Obj<'_>>, k: &str| -> Option<String> {
            o.and_then(|o| o.opt(k))
                .and_then(|v| doc.str(v))
                .map(str::to_owned)
        };
        let exporter = meta.opt("exporter").and_then(|v| Obj::new(doc, v, "").ok());
        let lean = meta.opt("lean").and_then(|v| Obj::new(doc, v, "").ok());
        self.env.meta = Meta {
            format_version: version.to_owned(),
            exporter_name: opt_str(exporter, "name"),
            exporter_version: opt_str(exporter, "version"),
            lean_version: opt_str(lean, "version"),
            lean_githash: opt_str(lean, "githash"),
        };
        Ok(())
    }

    /// Apply an item of `batch`: intern it, or read the record of a raw
    /// line (the meta record first).
    fn item(&mut self, tape: &mut Tape, batch: &Batch, item: Item, seen_meta: &mut bool) -> R<()> {
        match item {
            Item::Raw(a, b) => {
                let line = batch.text(a, b);
                parse_object(tape, line).and_then(|(doc, members)| {
                    if *seen_meta {
                        self.decl_record(doc, members)
                    } else {
                        *seen_meta = true;
                        self.meta(doc, members)
                    }
                })
            }
            _ => self.apply(batch.src(), item),
        }
    }

    /// Apply `data`, whole lines (the last one may lack its newline only
    /// at the end of the input).
    fn lines(&mut self, l: &mut Lines, data: &[u8]) -> Result<(), ReadError> {
        let fail = |line: u64, f: Fail| ReadError {
            line,
            class: f.class,
            msg: f.msg,
        };
        l.bytes += data.len() as u64;
        let mut pos = 0;
        let mut k = l.lines;
        let mut res = Ok(());
        while pos < data.len() {
            // `{"app"`, `{"forallE"` or `{"ie"`.
            if l.seen_first
                && matches!(data.get(pos + 2..pos + 4), Some(b"ap" | b"fo" | b"ie"))
                && self.mdata.is_empty()
                && let Some(b) = self.lazy.as_deref_mut()
            {
                let (n, m) = b.exprs(&data[pos..], &self.name_ids);
                pos += n;
                k += m;
                if pos == data.len() {
                    break;
                }
            }
            k += 1;
            if l.seen_first {
                match scan::line(&data[pos..], &mut l.us, self) {
                    Some((n, true)) => {
                        pos += n;
                        continue;
                    }
                    Some((_, false)) => {
                        let f = self.failed.take().expect("a failure");
                        res = Err(fail(k, f));
                        break;
                    }
                    None => {}
                }
            }
            let n = line_len(&data[pos..]);
            if let Err(f) = self.other_line(l, &data[pos..pos + n]) {
                res = Err(fail(k, f));
                break;
            }
            pos += n;
        }
        l.lines = k;
        res
    }

    /// A line the scanner left: parsed once, with the general parser.
    fn other_line(&mut self, l: &mut Lines, line: &[u8]) -> R<()> {
        let line = match std::str::from_utf8(line) {
            Ok(s) => s,
            Err(e) => return bad(format!("invalid UTF-8 at column {}", e.valid_up_to() + 1)),
        };
        if line.trim_ascii().is_empty() {
            return Ok(());
        }
        let (doc, members) = parse_object(&mut l.tape, line)?;
        if !l.seen_first {
            l.seen_first = true;
            l.seen_meta = true;
            return self.meta(doc, members);
        }
        l.batch.clear();
        match id_record(doc, members, &mut l.batch)? {
            Some(item) => self.apply(l.batch.src(), item),
            None => self.decl_record(doc, members),
        }
    }

    fn end_lines(&mut self, l: Lines) -> Result<ReadStats, ReadError> {
        if !l.seen_meta {
            return Err(ReadError {
                line: 0,
                class: ErrorClass::Malformed,
                msg: "empty input: expected the meta record".into(),
            });
        }
        Ok(ReadStats {
            lines: l.lines,
            bytes: l.bytes,
            ..ReadStats::default()
        })
    }

    /// The interning stage.
    fn consume(
        &mut self,
        full: Receiver<Batch>,
        empty: SyncSender<Batch>,
    ) -> Result<ReadStats, ReadError> {
        let mut tape = Tape::new();
        let mut seen_meta = false;
        loop {
            let w = std::time::Instant::now();
            let got = full.recv();
            WAIT_NS.fetch_add(
                w.elapsed().as_nanos() as u64,
                std::sync::atomic::Ordering::Relaxed,
            );
            let Ok(mut batch) = got else {
                return Err(ReadError {
                    line: 0,
                    class: ErrorClass::Io,
                    msg: "internal error: the parsing thread stopped".into(),
                });
            };
            for (k, item) in batch.items.iter().enumerate() {
                let res = self.item(&mut tape, &batch, *item, &mut seen_meta);
                if let Err(f) = res {
                    return Err(ReadError {
                        line: batch.lines[k],
                        class: f.class,
                        msg: f.msg,
                    });
                }
            }
            if let Some(end) = batch.end.take() {
                end?;
                if !seen_meta {
                    return Err(ReadError {
                        line: 0,
                        class: ErrorClass::Malformed,
                        msg: "empty input: expected the meta record".into(),
                    });
                }
                return Ok(ReadStats {
                    lines: batch.lines_read,
                    bytes: batch.bytes_read,
                    ..ReadStats::default()
                });
            }
            batch.clear();
            let _ = empty.try_send(batch);
        }
    }

    /// Resolve and intern a name, level or expression item.
    fn apply(&mut self, src: Src<'_>, item: Item) -> R<()> {
        match item {
            Item::Name { id, pre, comp } => {
                let pre = self.name(pre)?;
                let node = match comp {
                    Comp::Str(a, b) => {
                        NameNode::Str(pre, self.env.names.strings.intern(src.text(a, b)?)?)
                    }
                    Comp::Num(n) => NameNode::Num(pre, n),
                };
                let n = if self.append {
                    self.env.names.append(node)?
                } else {
                    self.env.names.intern(node)?.0
                };
                self.bind(Table::Name, id, n.0)
            }
            Item::Level { id, node } => {
                let node = match node {
                    RawLevel::Succ(l) => LevelNode::Succ(self.level(l)?),
                    RawLevel::Max(a, b) => LevelNode::Max(self.level(a)?, self.level(b)?),
                    RawLevel::IMax(a, b) => LevelNode::IMax(self.level(a)?, self.level(b)?),
                    RawLevel::Param(n) => LevelNode::Param(self.name(n)?),
                };
                let (l, _) = self.env.levels.intern(node)?;
                self.bind(Table::Level, id, l.0)
            }
            Item::Expr { id, node } => self.apply_expr(src, id, node),
            Item::Raw(..) => bad("internal error: unexpected raw line"),
        }
    }

    /// With lazy proofs: add compound record `node` to the table (see
    /// `lazy`); whether it was (else, a leaf, or the reader is eager now).
    fn lazy_expr(&mut self, id: u64, node: RawExpr) -> R<bool> {
        let name = |st: &State, n: u64| st.name_ids.get(n).map(NameId);
        let ok = match node {
            RawExpr::App(f, a) => self.lazy.as_deref_mut().expect("lazy").app(id, f, a),
            RawExpr::Binder {
                pi,
                bi,
                name: n,
                ty,
                body,
            } => match name(self, n) {
                Some(n) => self
                    .lazy
                    .as_deref_mut()
                    .expect("lazy")
                    .binder(id, pi, bi, n, ty, body),
                None => false,
            },
            RawExpr::Let {
                name: n,
                ty,
                value,
                body,
                nondep,
            } => match name(self, n) {
                Some(n) => {
                    self.lazy
                        .as_deref_mut()
                        .expect("lazy")
                        .let_in(id, n, [ty, value, body], nondep)
                }
                None => false,
            },
            RawExpr::Proj(s, i, e) => match name(self, s) {
                Some(s) => self.lazy.as_deref_mut().expect("lazy").proj(id, s, i, e),
                None => false,
            },
            RawExpr::MData(inner) => {
                let ok = self.lazy.as_deref_mut().expect("lazy").alias(id, inner);
                if ok {
                    self.shared_exprs += 1;
                }
                ok
            }
            _ => return Ok(false),
        };
        if !ok {
            self.eager()?;
        }
        Ok(ok)
    }

    /// Give up lazy proofs (for an export whose expression ids are not
    /// dense): intern every record, and map each expression id to its
    /// arena id from now on.
    #[cold]
    #[inline(never)]
    fn eager(&mut self) -> R<()> {
        let Some(b) = self.lazy.take() else {
            return Ok(());
        };
        let (ids, roots) = b.into_eager(&mut self.env, self.append)?;
        let mut m = IdMap::new(0);
        m.reserve(ids.len());
        for (i, &a) in ids.iter().enumerate() {
            if m.bind(i as u64, a).is_err() {
                return twice(Table::Expr, i as u64);
            }
        }
        self.expr_ids = m;
        for d in &mut self.env.decls {
            if let DeclKind::Theorem { value, .. } = &mut d.kind
                && is_lazy(*value)
            {
                *value = ExprId(roots[(value.0 - LAZY_BASE) as usize]);
            }
        }
        Ok(())
    }

    #[cold]
    fn track_mdata(&mut self, id: u64, node: RawExpr) {
        let get = |e| self.mdata.get(&e).copied();
        let nested = |e| get(e).map(|_| MData::Nested);
        let spine = |e| {
            get(e).map(|m| match m {
                MData::Root | MData::Spine => MData::Spine,
                MData::Nested => MData::Nested,
            })
        };
        let m = match node {
            RawExpr::MData(_) => Some(MData::Root),
            RawExpr::App(f, a) => spine(f).or_else(|| nested(a)),
            RawExpr::Binder {
                pi: true, ty, body, ..
            } => spine(body).or_else(|| nested(ty)),
            RawExpr::Binder { ty, body, .. } => nested(ty).or_else(|| nested(body)),
            RawExpr::Let {
                ty, value, body, ..
            } => nested(ty)
                .or_else(|| nested(value))
                .or_else(|| nested(body)),
            RawExpr::Proj(_, _, e) => nested(e),
            _ => None,
        };
        if let Some(m) = m {
            self.mdata.insert(id, m);
        }
    }

    fn apply_expr(&mut self, src: Src<'_>, id: u64, node: RawExpr) -> R<()> {
        if !self.mdata.is_empty() || matches!(node, RawExpr::MData(_)) {
            self.track_mdata(id, node);
        }
        if self.lazy.is_some() && self.lazy_expr(id, node)? {
            return Ok(());
        }
        let node = match node {
            RawExpr::BVar(i) => match u32::try_from(i) {
                Ok(i) => ExprNode::BVar(i),
                Err(_) => return Err(ExprError::BVarTooLarge(i).into()),
            },
            RawExpr::Sort(l) => ExprNode::Sort(self.level(l)?),
            RawExpr::Const(name, a, b) => {
                let name = self.name(name)?;
                let mut buf = std::mem::take(&mut self.levels_buf);
                buf.clear();
                let mut res = Ok(());
                for &u in &src.us[a as usize..b as usize] {
                    match self.level(u) {
                        Ok(l) => buf.push(l),
                        Err(e) => {
                            res = Err(e);
                            break;
                        }
                    }
                }
                let ls = res.and_then(|()| Ok(self.env.levels.intern_list(&buf)?));
                self.levels_buf = buf;
                ExprNode::Const(name, ls?)
            }
            RawExpr::App(f, a) => ExprNode::App(self.expr(f)?, self.expr(a)?),
            RawExpr::Binder {
                pi,
                bi,
                name,
                ty,
                body,
            } => {
                let (name, ty, body) = (self.name(name)?, self.expr(ty)?, self.expr(body)?);
                if pi {
                    ExprNode::Pi(bi, name, ty, body)
                } else {
                    ExprNode::Lam(bi, name, ty, body)
                }
            }
            RawExpr::Let {
                name,
                ty,
                value,
                body,
                nondep,
            } => {
                let b = LetBinder {
                    name: self.name(name)?,
                    ty: self.expr(ty)?,
                    value: self.expr(value)?,
                    nondep,
                };
                let body = self.expr(body)?;
                ExprNode::Let(self.env.exprs.intern_let(b)?, body)
            }
            RawExpr::Proj(name, idx, e) => ExprNode::Proj(self.name(name)?, idx, self.expr(e)?),
            RawExpr::Nat(a, b) => {
                let Some(n) = parse_nat_lit(src.text(a, b)?) else {
                    return bad("expr.natVal must be a string of decimal digits");
                };
                self.env.exprs.nat_node(n)?
            }
            RawExpr::Str(a, b) => ExprNode::Str(self.env.names.strings.intern(src.text(a, b)?)?),
            RawExpr::MData(inner) => {
                // Metadata is kernel-irrelevant: bind the id to the inner
                // expression.
                let inner = self.expr(inner)?;
                self.shared_exprs += 1;
                return self.bind(Table::Expr, id, inner.0);
            }
        };
        let (e, fresh) = if self.append {
            (self.env.exprs.append(node, &self.env.levels)?, true)
        } else {
            self.env.exprs.intern(node, &self.env.levels)?
        };
        if !fresh {
            self.shared_exprs += 1;
        }
        if let Some(b) = self.lazy.as_deref_mut() {
            if b.leaf(id, e.0) {
                return Ok(());
            }
            self.eager()?;
        }
        self.bind(Table::Expr, id, e.0)
    }

    /// A declaration record: {kind: payload}.
    fn decl_record(&mut self, doc: Doc<'_>, members: &[Member]) -> R<()> {
        if members.len() != 1 {
            let keys: Vec<&str> = members.iter().map(|m| doc.key(m)).collect();
            return bad(format!("unrecognized record with keys {keys:?}"));
        }
        let m = &members[0];
        let kind = doc.key(m);
        match kind {
            "axiom" => self.single(doc, m.val, Single::Axiom),
            "def" => self.single(doc, m.val, Single::Def),
            "thm" => self.single(doc, m.val, Single::Thm),
            "opaque" => self.single(doc, m.val, Single::Opaque),
            "quot" => self.single(doc, m.val, Single::Quot),
            "inductive" => self.inductive(doc, m.val),
            "meta" => bad("meta record after the first line"),
            _ => bad(format!("unknown record kind '{kind}'")),
        }?;
        if let Some(b) = self.lazy.as_deref_mut() {
            b.decl_done();
        }
        Ok(())
    }

    /// A theorem or definition the scanner read; the same steps, in the
    /// same order, as [`State::single`].
    fn scanned_decl(&mut self, d: &scan::Decl, us: &[u64]) -> R<()> {
        let name = self.name(d.name)?;
        let level_params = self.name_ids(&us[d.level_params.0..d.level_params.1])?;
        let ty = self.root(d.ty)?;
        let all = &us[d.all.0..d.all.1];
        let kind = if d.thm {
            DeclKind::Theorem {
                value: self.thm_value(d.value)?,
                all: self.name_ids(all)?,
            }
        } else {
            DeclKind::Definition {
                value: self.root(d.value)?,
                hints: d.hints,
                safety: d.safety,
                all: self.name_ids(all)?,
            }
        };
        let start = self.env.decls.len() as u32;
        self.push_decl(Decl {
            name,
            level_params,
            ty,
            kind,
        })?;
        self.env.blocks.push(Block {
            start,
            kind: BlockKind::Single,
        });
        if let Some(b) = self.lazy.as_deref_mut() {
            b.decl_done();
        }
        Ok(())
    }

    /// A list of names, by export id.
    fn name_ids(&mut self, ids: &[u64]) -> R<NameList> {
        let mut buf = std::mem::take(&mut self.names_buf);
        buf.clear();
        let mut res = Ok(());
        for &n in ids {
            match self.name(n) {
                Ok(n) => buf.push(n),
                Err(e) => {
                    res = Err(e);
                    break;
                }
            }
        }
        let out = res.and_then(|()| match self.env.push_names(&buf) {
            Some(l) => Ok(l),
            None => Err(Overflow("too many names in declaration lists").into()),
        });
        self.names_buf = buf;
        out
    }

    fn name_list(&mut self, o: &Obj<'_>, k: &str) -> R<NameList> {
        let vals = o.arr(k)?;
        let mut buf = std::mem::take(&mut self.names_buf);
        buf.clear();
        let mut res = Ok(());
        for &v in vals {
            match o.doc.nat(v) {
                Some(n) => match self.name(n) {
                    Ok(n) => buf.push(n),
                    Err(e) => {
                        res = Err(e);
                        break;
                    }
                },
                None => {
                    res = bad(format!("{}: entries of '{k}' must be name ids", o.what));
                    break;
                }
            }
        }
        let out = res.and_then(|()| match self.env.push_names(&buf) {
            Some(l) => Ok(l),
            None => Err(Overflow("too many names in declaration lists").into()),
        });
        self.names_buf = buf;
        out
    }

    fn header(&mut self, o: &Obj<'_>) -> R<(NameId, NameList, ExprId)> {
        let name = self.name(o.nat("name")?)?;
        let lps = self.name_list(o, "levelParams")?;
        let ty = self.root(o.nat("type")?)?;
        Ok((name, lps, ty))
    }

    fn push_decl(&mut self, d: Decl) -> R<()> {
        let idx = match u32::try_from(self.env.decls.len()) {
            Ok(i) if i < u32::MAX => i,
            _ => return Err(Overflow("too many declarations").into()),
        };
        if self.env.by_name.insert(d.name, idx).is_some() {
            return Err(Fail {
                class: ErrorClass::Rejected,
                msg: format!(
                    "constant {} is declared twice",
                    self.env.names.display(d.name)
                ),
            });
        }
        self.env.decls.push(d);
        Ok(())
    }

    fn single(&mut self, doc: Doc<'_>, v: Val, kind: Single) -> R<()> {
        let o = Obj::new(doc, v, kind.what())?;
        let (name, level_params, ty) = self.header(&o)?;
        let kind = match kind {
            Single::Axiom => DeclKind::Axiom {
                is_unsafe: o.bool("isUnsafe")?,
            },
            Single::Def => {
                let value = self.root(o.nat("value")?)?;
                let hints = match o.field("hints")? {
                    h if doc.str(h) == Some("opaque") => Hints::Opaque,
                    h if doc.str(h) == Some("abbrev") => Hints::Abbrev,
                    h => match doc.members(h) {
                        Some(_) => {
                            let ho = Obj::new(doc, h, "def.hints")?;
                            Hints::Regular(ho.u32("regular")?)
                        }
                        None => {
                            return bad(
                                "def: field 'hints' must be \"opaque\", \"abbrev\" or {\"regular\": n}",
                            );
                        }
                    },
                };
                let safety = match o.str("safety")? {
                    "safe" => Safety::Safe,
                    "unsafe" => Safety::Unsafe,
                    "partial" => Safety::Partial,
                    s => return bad(format!("def: unknown safety '{s}'")),
                };
                let all = self.name_list(&o, "all")?;
                DeclKind::Definition {
                    value,
                    hints,
                    safety,
                    all,
                }
            }
            Single::Thm => DeclKind::Theorem {
                value: self.thm_value(o.nat("value")?)?,
                all: self.name_list(&o, "all")?,
            },
            Single::Opaque => DeclKind::Opaque {
                value: self.root(o.nat("value")?)?,
                all: self.name_list(&o, "all")?,
                // Lean's reader defaults this when absent; so do we.
                is_unsafe: match o.opt("isUnsafe") {
                    None => false,
                    Some(_) => o.bool("isUnsafe")?,
                },
            },
            Single::Quot => DeclKind::Quot {
                kind: match o.str("kind")? {
                    "type" => QuotKind::Type,
                    "ctor" => QuotKind::Ctor,
                    "lift" => QuotKind::Lift,
                    "ind" => QuotKind::Ind,
                    s => return bad(format!("quot: unknown kind '{s}'")),
                },
            },
        };
        if matches!(kind, DeclKind::Quot { .. })
            && !self.mdata.is_empty()
            && self.mdata.contains_key(&o.nat("type")?)
        {
            self.env
                .mdata_errors
                .insert(name, "metadata in quotient type");
        }
        let start = self.env.decls.len() as u32;
        self.push_decl(Decl {
            name,
            level_params,
            ty,
            kind,
        })?;
        self.env.blocks.push(Block {
            start,
            kind: BlockKind::Single,
        });
        Ok(())
    }

    fn inductive(&mut self, doc: Doc<'_>, v: Val) -> R<()> {
        let o = Obj::new(doc, v, "inductive")?;
        let (types, ctors, recs) = (o.arr("types")?, o.arr("ctors")?, o.arr("recs")?);
        let start = self.env.decls.len() as u32;
        for &t in types {
            let o = Obj::new(doc, t, "inductive.types")?;
            let (name, level_params, ty) = self.header(&o)?;
            let kind = DeclKind::Inductive {
                num_params: o.u32("numParams")?,
                num_indices: o.u32("numIndices")?,
                all: self.name_list(&o, "all")?,
                ctors: self.name_list(&o, "ctors")?,
                num_nested: o.u32("numNested")?,
                is_rec: o.bool("isRec")?,
                is_reflexive: o.bool("isReflexive")?,
                is_unsafe: o.bool("isUnsafe")?,
            };
            self.push_decl(Decl {
                name,
                level_params,
                ty,
                kind,
            })?;
        }
        for &c in ctors {
            let o = Obj::new(doc, c, "inductive.ctors")?;
            let (name, level_params, ty) = self.header(&o)?;
            let kind = DeclKind::Constructor {
                induct: self.name(o.nat("induct")?)?,
                cidx: o.u32("cidx")?,
                num_params: o.u32("numParams")?,
                num_fields: o.u32("numFields")?,
                is_unsafe: o.bool("isUnsafe")?,
            };
            if !self.mdata.is_empty()
                && matches!(
                    self.mdata.get(&o.nat("type")?),
                    Some(MData::Root | MData::Spine)
                )
            {
                self.env
                    .mdata_errors
                    .insert(name, "metadata on constructor type spine");
            }
            self.push_decl(Decl {
                name,
                level_params,
                ty,
                kind,
            })?;
        }
        for &r in recs {
            let o = Obj::new(doc, r, "inductive.recs")?;
            let (name, level_params, ty) = self.header(&o)?;
            let all = self.name_list(&o, "all")?;
            let mut metadata =
                !self.mdata.is_empty() && self.mdata.get(&o.nat("type")?) == Some(&MData::Root);
            let mut rules = std::mem::take(&mut self.rules_buf);
            rules.clear();
            let res = (|| {
                for &rv in o.arr("rules")? {
                    let ro = Obj::new(doc, rv, "inductive.recs.rules")?;
                    let rhs = ro.nat("rhs")?;
                    metadata |=
                        !self.mdata.is_empty() && self.mdata.get(&rhs) == Some(&MData::Root);
                    rules.push(RecRule {
                        ctor: self.name(ro.nat("ctor")?)?,
                        nfields: ro.u32("nfields")?,
                        rhs: self.root(rhs)?,
                    });
                }
                match self.env.push_rules(&rules) {
                    Some(l) => Ok(l),
                    None => Err(Fail::from(Overflow("too many recursor rules"))),
                }
            })();
            self.rules_buf = rules;
            let is_unsafe = o.bool("isUnsafe")?;
            if metadata && !is_unsafe {
                self.env
                    .mdata_errors
                    .insert(name, "metadata wrapping a recursor type or rule");
            }
            let kind = DeclKind::Recursor {
                all,
                num_params: o.u32("numParams")?,
                num_indices: o.u32("numIndices")?,
                num_motives: o.u32("numMotives")?,
                num_minors: o.u32("numMinors")?,
                rules: res?,
                k: o.bool("k")?,
                is_unsafe,
            };
            self.push_decl(Decl {
                name,
                level_params,
                ty,
                kind,
            })?;
        }
        let n = |a: &[Val]| a.len() as u32;
        self.env.blocks.push(Block {
            start,
            kind: BlockKind::Inductive {
                types: n(types),
                ctors: n(ctors),
                recs: n(recs),
            },
        });
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// An item with its batch ranges resolved, for comparing two batches.
    fn describe(b: &Batch, item: Item) -> String {
        match item {
            Item::Name {
                id,
                pre,
                comp: Comp::Str(x, y),
            } => format!("name {id} {pre} str {:?}", b.text(x, y)),
            Item::Expr {
                id,
                node: RawExpr::Const(n, x, y),
            } => format!("expr {id} const {n} {:?}", &b.us[x as usize..y as usize]),
            Item::Expr {
                id,
                node: RawExpr::Nat(x, y),
            } => format!("expr {id} nat {}", b.text(x, y)),
            Item::Expr {
                id,
                node: RawExpr::Str(x, y),
            } => format!("expr {id} str {:?}", b.text(x, y)),
            Item::Raw(x, y) => format!("raw {:?}", b.text(x, y)),
            other => format!("{other:?}"),
        }
    }

    /// The general path's result for a line.
    fn general(line: &str) -> Result<Option<String>, String> {
        let mut tape = Tape::new();
        let mut b = Batch::default();
        let (doc, members) = parse_object(&mut tape, line).map_err(|f| f.msg)?;
        match id_record(doc, members, &mut b) {
            Ok(Some(item)) => Ok(Some(describe(&b, item))),
            Ok(None) => Ok(None),
            Err(f) => Err(f.msg),
        }
    }

    /// Check the contract of [`scan::line`] on one line; returns whether
    /// it took the line.
    fn scanned_as_general(line: &str) -> bool {
        // Alone (so scanned from a padded window), and followed by more
        // input (scanned in place).
        let alone = scanned_one(line, line.len());
        let mut more = line.to_string();
        if !more.ends_with('\n') {
            more.push('\n');
        }
        let n = more.len();
        more.push_str(&r#"{"bvar":0,"ie":1}"#.repeat(20));
        assert_eq!(scanned_one(&more, n), alone, "line: {line}");
        alone
    }

    /// The scanner on `input`, which starts with a line of `n` bytes.
    fn scanned_one(input: &str, n: usize) -> bool {
        let mut b = Batch::default();
        let mut us = Vec::new();
        let mut sink = ToBatch(&mut b, None);
        let Some((got, took)) = scan::line(input.as_bytes(), &mut us, &mut sink) else {
            return false;
        };
        let res = if took { Ok(()) } else { Err(sink.1) };
        let line = &input[..n];
        assert_eq!(got, n, "line: {line}");
        assert!(res.is_ok());
        let fast = describe(&b, b.items[0]);
        let general_line = line.strip_suffix('\n').unwrap_or(line);
        assert_eq!(general(general_line), Ok(Some(fast)), "line: {line}");
        true
    }

    /// Check the fast-path contract on one line; returns whether the fast
    /// path took it. The scanner is checked on it too.
    fn same_as_general(line: &str) -> bool {
        scanned_as_general(line);
        let mut b = Batch::default();
        let Some(item) = fast::parse(line, &mut b) else {
            return false;
        };
        let fast = describe(&b, item);
        assert_eq!(general(line), Ok(Some(fast)), "line: {line}");
        true
    }

    /// Strings of every length, with an escape, a control character or a
    /// non-ASCII character at every place: the scanner (which reads
    /// eight bytes at a time) takes them or not as the general parser
    /// reads them.
    #[test]
    fn scanned_strings_agree_with_general_path() {
        for n in 0..40 {
            let plain = "a".repeat(n);
            assert!(scanned_as_general(&format!(
                r#"{{"in":1,"str":{{"pre":0,"str":"{plain}"}}}}"#
            )));
            for i in 0..=n {
                for odd in ["\\\"", "\\n", "\u{1}", "\u{1f}", "é", "\u{7f}"] {
                    let text = format!("{}{odd}{}", &plain[..i], &plain[i..]);
                    let line = format!(r#"{{"in":1,"str":{{"pre":0,"str":"{text}"}}}}"#);
                    let took = scanned_as_general(&line);
                    let plain_enough = !odd.starts_with('\\') && odd.as_bytes()[0] >= 0x20;
                    assert_eq!(took, plain_enough, "{line:?}");
                }
            }
        }
    }

    #[test]
    fn fast_path_agrees_with_general_path() {
        let taken = [
            r#"{"in":1,"str":{"pre":0,"str":"Nat"}}"#,
            r#"{"str":{"str":"Nat","pre":0},"in":1}"#,
            r#"{"in":7,"num":{"pre":3,"i":12}}"#,
            r#"{"il":1,"succ":0}"#,
            r#"{"il":3,"max":[1,2]}"#,
            r#"{"imax":[1, 2],"il":3}"#,
            r#"{"il":4,"param":9}"#,
            r#"{"ie":0,"sort":1}"#,
            r#"{"ie":1,"bvar":0}"#,
            r#"{"const":{"name":1,"us":[]},"ie":1}"#,
            r#"{"ie":2,"const":{"name":1,"us":[1,2,3]}}"#,
            r#"{"ie":3,"app":{"fn":1,"arg":2}}"#,
            r#"{"ie":4,"lam":{"binderInfo":"default","body":3,"name":4,"type":0}}"#,
            r#"{"ie":5,"forallE":{"binderInfo":"instImplicit","body":3,"name":4,"type":0}}"#,
            r#"{"ie":6,"letE":{"body":1,"name":2,"nondep":false,"type":3,"value":4}}"#,
            r#"{"ie":7,"proj":{"idx":0,"struct":3,"typeName":1}}"#,
            r#"{"ie":8,"natVal":"123456789012345678901234567890"}"#,
            r#"{"ie":9,"strVal":"héllo"}"#,
            r#"  { "ie" : 10 , "app" : { "fn" : 1 , "arg" : 2 , "extra" : true } }  "#,
            "{\"ie\":11,\"bvar\":3}\r\n",
        ];
        for l in taken {
            assert!(same_as_general(l), "fast path should take: {l}");
        }
        // Lines the fast path must leave to the general parser (errors,
        // escapes, odd shapes). Whatever the general path says is fine.
        let declined = [
            r#"{"in":1,"str":{"pre":0,"str":"a\"b"}}"#,
            r#"{"ie":9,"strVal":"a\nb"}"#,
            r#"{"ie":8,"natVal":"12a"}"#,
            r#"{"ie":8,"natVal":""}"#,
            r#"{"ie":1,"bvar":01}"#,
            r#"{"ie":1,"bvar":1.0}"#,
            r#"{"ie":1,"bvar":-1}"#,
            r#"{"ie":1,"bvar":18446744073709551616}"#,
            r#"{"ie":1,"bvar":0,"x":1}"#,
            r#"{"ie":1,"ie":2}"#,
            r#"{"ie":3,"app":{"fn":1,"fn":2,"arg":2}}"#,
            r#"{"ie":3,"app":{"fn":1}}"#,
            r#"{"ie":3,"app":{"fn":"1","arg":2}}"#,
            r#"{"ie":3,"app":{"fn":1,"arg":{"x":1}}}"#,
            r#"{"ie":4,"lam":{"binderInfo":"weird","body":3,"name":4,"type":0}}"#,
            r#"{"ie":7,"proj":{"idx":4294967296,"struct":3,"typeName":1}}"#,
            r#"{"il":3,"max":[1]}"#,
            r#"{"il":3,"max":[1,2,3]}"#,
            r#"{"il":3,"succ":[1]}"#,
            r#"{"in":1,"str":{"pre":0}}"#,
            r#"{"in":1,"blah":{"pre":0,"str":"a"}}"#,
            r#"{"ie":1,"mdata":{"data":{},"expr":0}}"#,
            r#"{"ie":"1","bvar":0}"#,
            r#"{"ie":1,"bvar":0} x"#,
            r#"{"ie":1,"bvar":0"#,
            r#"{"ie":1,"app":{"fn":1,"arg":2}}}"#,
            r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#,
            r#"{"foo":1,"bar":2}"#,
            r#"{}"#,
            r#"[]"#,
        ];
        for l in declined {
            assert!(!same_as_general(l), "fast path should decline: {l}");
        }
    }

    #[test]
    fn scanner_agrees_with_general_path() {
        let taken = [
            r#"{"in":1,"str":{"pre":0,"str":"Nat"}}"#,
            r#"{"in":7,"num":{"i":12,"pre":3}}"#,
            r#"{"il":1,"succ":0}"#,
            r#"{"il":3,"max":[1,2]}"#,
            r#"{"il":3,"imax":[1,2]}"#,
            r#"{"il":4,"param":9}"#,
            r#"{"ie":0,"sort":1}"#,
            r#"{"bvar":0,"ie":1}"#,
            r#"{"const":{"name":1,"us":[]},"ie":1}"#,
            r#"{"const":{"name":1,"us":[1,2,3]},"ie":2}"#,
            r#"{"app":{"arg":2,"fn":1},"ie":3}"#,
            "{\"app\":{\"arg\":2,\"fn\":1},\"ie\":3}\n",
            r#"{"app":{"arg":123456789,"fn":12345678},"ie":1234567890123}"#,
            r#"{"app":{"arg":0,"fn":10},"ie":9999999999999999999}"#,
            r#"{"ie":4,"lam":{"binderInfo":"default","body":3,"name":4,"type":0}}"#,
            r#"{"ie":4,"lam":{"binderInfo":"strictImplicit","body":3,"name":4,"type":0}}"#,
            r#"{"forallE":{"binderInfo":"instImplicit","body":3,"name":4,"type":0},"ie":5}"#,
            r#"{"forallE":{"binderInfo":"implicit","body":3,"name":4,"type":0},"ie":5}"#,
            r#"{"ie":6,"letE":{"body":1,"name":2,"nondep":false,"type":3,"value":4}}"#,
            r#"{"ie":6,"letE":{"body":1,"name":2,"nondep":true,"type":3,"value":4}}"#,
            r#"{"ie":7,"proj":{"idx":0,"struct":3,"typeName":1}}"#,
            r#"{"ie":8,"natVal":"123456789012345678901234567890"}"#,
            r#"{"ie":9,"strVal":"héllo"}"#,
            r#"{"ie":9,"strVal":""}"#,
        ];
        for l in taken {
            assert!(scanned_as_general(l), "scanner should take: {l}");
        }
        // Long lines: the scanner reads a line from a window of its first
        // bytes, and declines one that does not fit.
        for k in [10, 50, 80, 120] {
            let us = vec!["7"; k].join(",");
            let l = format!(r#"{{"const":{{"name":1,"us":[{us}]}},"ie":2}}"#);
            assert_eq!(scanned_as_general(&l), l.len() < 250, "{l}");
            let l = format!(r#"{{"ie":9,"strVal":"{}"}}"#, "x".repeat(2 * k));
            assert_eq!(scanned_as_general(&l), l.len() < 250, "{l}");
        }
        let declined = [
            r#"{"in":1,"str":{"pre":0,"str":"a\"b"}}"#,
            r#"{"ie":8,"natVal":"12a"}"#,
            r#"{"ie":8,"natVal":""}"#,
            r#"{"bvar":01,"ie":1}"#,
            r#"{"bvar":00000000001,"ie":1}"#,
            r#"{"bvar":1.0,"ie":1}"#,
            r#"{"bvar":1e3,"ie":1}"#,
            r#"{"bvar":-1,"ie":1}"#,
            r#"{"bvar":18446744073709551616,"ie":1}"#,
            r#"{"bvar":1,"ie":1} "#,
            "{\"bvar\":1,\"ie\":1}\r\n",
            r#"{"bvar":1,"ie":1}}"#,
            r#"{"bvar":1,"ie":1"#,
            r#"{"app":{"arg":2,"fn":1}, "ie":3}"#,
            r#"{"ie":3,"app":{"fn":1,"arg":2}}"#,
            r#"{"ie":4,"lam":{"binderInfo":"weird","body":3,"name":4,"type":0}}"#,
            r#"{"ie":7,"proj":{"idx":4294967296,"struct":3,"typeName":1}}"#,
            r#"{"il":3,"max":[1]}"#,
            r#"{"il":3,"max":[1,2,3]}"#,
            r#"{"ie":1,"mdata":{"data":{},"expr":0}}"#,
            r#"{"const":{"name":1,"us":[1,]},"ie":1}"#,
            r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#,
            r#"{}"#,
        ];
        for l in declined {
            assert!(!scanned_as_general(l), "scanner should decline: {l}");
        }
    }

    /// Reading on one thread (the scanner, applied line by line) and on
    /// several (batches) gives the same environment.
    #[test]
    fn one_thread_matches_several() {
        let path = std::env::var_os("NITROLEAN_EXPORT");
        let dir = std::env::temp_dir().join(format!("nitrolean-read-{}", std::process::id()));
        let path = match path {
            Some(p) => std::path::PathBuf::from(p),
            None => {
                let mut text = String::new();
                text.push_str(r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"}}}"#);
                text.push('\n');
                for l in [
                    r#"{"in":1,"str":{"pre":0,"str":"A"}}"#,
                    r#"{"in":2,"str":{"pre":0,"str":"x"}}"#,
                    r#"{"il":1,"succ":0}"#,
                    r#"{"ie":0,"sort":1}"#,
                    r#"{"bvar":0,"ie":1}"#,
                    r#"{"forallE":{"binderInfo":"default","body":0,"name":2,"type":0},"ie":2}"#,
                    r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":2}}"#,
                    r#"{"in":3,"str":{"pre":0,"str":"t"}}"#,
                    r#"{"ie":3,"lam":{"binderInfo":"default","body":1,"name":2,"type":0}}"#,
                    r#"{"ie":4,"mdata":{"data":{},"expr":3}}"#,
                    r#"{"thm":{"all":[3],"levelParams":[],"name":3,"type":2,"value":4}}"#,
                    r#"{"in":4,"str":{"pre":0,"str":"d"}}"#,
                    r#"{"in":5,"num":{"i":2,"pre":4}}"#,
                    r#"{"in":6,"num":{"i":3,"pre":4}}"#,
                    r#"{"in":7,"str":{"pre":0,"str":"u"}}"#,
                    r#"{"def":{"all":[4],"hints":"abbrev","levelParams":[],"name":4,"safety":"safe","type":2,"value":3}}"#,
                    r#"{"def":{"all":[5,6],"hints":{"regular":7},"levelParams":[7],"name":5,"safety":"unsafe","type":2,"value":3}}"#,
                    r#"{"def":{"all":[5,6],"hints":"opaque","levelParams":[],"name":6,"safety":"partial","type":2,"value":4}}"#,
                    r#"{"in":8,"str":{"pre":0,"str":"t2"}}"#,
                    r#"{"thm":{"all":[8],"levelParams":[7],"name":8,"type":2,"value":3}}"#,
                    // Aliases (`mdata`) in a promoted term: of an interned
                    // term, of a stored one, of a recent one.
                    r#"{"in":9,"str":{"pre":0,"str":"m"}}"#,
                    r#"{"ie":5,"mdata":{"data":{},"expr":2}}"#,
                    r#"{"app":{"arg":1,"fn":4},"ie":6}"#,
                    r#"{"ie":7,"mdata":{"data":{},"expr":6}}"#,
                    r#"{"ie":8,"mdata":{"data":{},"expr":7}}"#,
                    r#"{"ie":9,"lam":{"binderInfo":"default","body":8,"name":2,"type":5}}"#,
                    r#"{"def":{"all":[9],"hints":"abbrev","levelParams":[],"name":9,"safety":"safe","type":2,"value":9}}"#,
                ] {
                    text.push_str(l);
                    text.push('\n');
                }
                std::fs::create_dir_all(&dir).expect("temp dir");
                let p = dir.join("small.ndjson");
                std::fs::write(&p, text).expect("write");
                p
            }
        };
        let read = |lazy_proofs, threads| {
            read_file_with(
                &path,
                &Options {
                    lazy_proofs,
                    threads,
                },
            )
            .expect("read")
        };
        // The comparison builds the lazy values of its second argument.
        let (base, stats) = read(false, 1);
        for (lazy_proofs, threads) in [(false, 3), (true, 1), (true, 3)] {
            let (other, s) = read(lazy_proofs, threads);
            assert_eq!((s.lines, s.bytes), (stats.lines, stats.bytes));
            let d = crate::compare::compare(&base, &other);
            assert!(
                d.only_a.is_empty() && d.only_b.is_empty() && d.differ.is_empty(),
                "lazy={lazy_proofs}, threads={threads}: the reads differ"
            );
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// An export whose expression ids stop being dense after a theorem's
    /// value was left lazy reads the same with lazy proofs as without
    /// (the reader turns eager there); and a bad reference fails the same.
    #[test]
    fn lazy_falls_back_to_eager() {
        let meta = r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"}}}"#;
        let start = [
            r#"{"in":1,"str":{"pre":0,"str":"A"}}"#,
            r#"{"in":2,"str":{"pre":0,"str":"x"}}"#,
            r#"{"il":1,"succ":0}"#,
            r#"{"ie":0,"sort":1}"#,
            r#"{"bvar":0,"ie":1}"#,
            r#"{"forallE":{"binderInfo":"default","body":0,"name":2,"type":0},"ie":2}"#,
            r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":2}}"#,
            r#"{"in":3,"str":{"pre":0,"str":"t"}}"#,
            r#"{"ie":3,"lam":{"binderInfo":"default","body":1,"name":2,"type":0}}"#,
            r#"{"ie":4,"mdata":{"data":{},"expr":3}}"#,
            r#"{"app":{"arg":4,"fn":3},"ie":5}"#,
            r#"{"thm":{"all":[3],"levelParams":[],"name":3,"type":2,"value":4}}"#,
            r#"{"in":4,"str":{"pre":0,"str":"u"}}"#,
        ];
        let dir = std::env::temp_dir().join(format!("nitrolean-eager-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        let write = |name: &str, tail: &[&str]| {
            let mut text = format!("{meta}\n");
            for l in start.iter().chain(tail) {
                text.push_str(l);
                text.push('\n');
            }
            let p = dir.join(name);
            std::fs::write(&p, text).expect("write");
            p
        };
        let read = |p: &std::path::Path, lazy_proofs, threads| {
            read_file_with(
                p,
                &Options {
                    lazy_proofs,
                    threads,
                },
            )
        };
        // Ids 7 and 9 (and 5's application interned by neither theorem).
        for tail in [
            &[r#"{"app":{"arg":3,"fn":5},"ie":7}"#][..],
            &[r#"{"ie":9,"lam":{"binderInfo":"default","body":5,"name":2,"type":0}}"#],
            &[r#"{"ie":9,"mdata":{"data":{},"expr":5}}"#],
            &[r#"{"bvar":1,"ie":7}"#],
        ] {
            let mut tail = tail.to_vec();
            let n = if tail[0].contains("\"ie\":7") { 7 } else { 9 };
            let thm = format!(
                r#"{{"thm":{{"all":[4],"levelParams":[],"name":4,"type":2,"value":{n}}}}}"#
            );
            tail.push(&thm);
            let p = write("sparse.ndjson", &tail);
            let (base, _) = read(&p, false, 1).expect("read");
            for threads in [1, 3] {
                let (other, _) = read(&p, true, threads).expect("read");
                let d = crate::compare::compare(&base, &other);
                assert!(
                    d.only_a.is_empty() && d.only_b.is_empty() && d.differ.is_empty(),
                    "{tail:?}, threads={threads}: the reads differ"
                );
                assert_eq!(d.common, 3);
            }
        }
        for tail in [
            &[r#"{"app":{"arg":3,"fn":9},"ie":6}"#][..],
            &[r#"{"thm":{"all":[4],"levelParams":[],"name":4,"type":2,"value":6}}"#],
            &[r#"{"app":{"arg":3,"fn":3},"ie":5}"#],
        ] {
            let p = write("bad.ndjson", tail);
            let eager = read(&p, false, 1).map(|_| ()).expect_err("fails");
            for threads in [1, 3] {
                let lazy = read(&p, true, threads).map(|_| ()).expect_err("fails");
                assert_eq!((lazy.line, &lazy.msg), (eager.line, &eager.msg), "{tail:?}");
            }
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Differential check of every line of a real export. Run with
    /// `NITROLEAN_EXPORT=file cargo test --release -- --ignored`.
    #[test]
    #[ignore = "needs NITROLEAN_EXPORT"]
    fn fast_path_agrees_on_real_export() {
        let Some(path) = std::env::var_os("NITROLEAN_EXPORT") else {
            eprintln!("NITROLEAN_EXPORT not set; skipping");
            return;
        };
        let f = BufReader::new(File::open(path).expect("open NITROLEAN_EXPORT"));
        let (mut taken, mut declined, mut total) = (0u64, 0u64, 0u64);
        for line in f.lines().skip(1) {
            let line = line.expect("read line");
            total += 1;
            if same_as_general(&line) {
                taken += 1;
            } else if let Ok(Some(_)) = general(&line) {
                declined += 1;
            }
        }
        // Declines (escaped strings, mdata, long universe lists) are rare.
        assert!(
            declined * 100 < total,
            "fast path declined {declined} lines"
        );
        eprintln!("fast path took {taken} of {total} lines, declined {declined} records");
    }
}
