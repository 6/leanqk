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

use num_bigint::BigUint;

use crate::env::{
    Block, BlockKind, Decl, DeclKind, Env, Hints, Meta, NameList, QuotKind, RecRule, Safety,
};
use crate::expr::{BinderInfo, ExprError, ExprId, ExprNode, LetBinder};
use crate::idmap::IdMap;
use crate::json::{Doc, Member, Tape, Val};
use crate::level::{LevelId, LevelNode};
use crate::name::{NameId, NameNode};
use crate::strings::Overflow;

mod fast;

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
    let f = File::open(path).map_err(|e| io_error(path, e))?;
    read_open_file(f)
}

/// Read an export from standard input. When it is redirected from a
/// regular file, its size is used to pre-size the tables.
pub fn read_stdin() -> Result<(Env, ReadStats), ReadError> {
    use std::os::fd::AsFd;
    match io::stdin().as_fd().try_clone_to_owned() {
        Ok(fd) => read_open_file(File::from(fd)),
        Err(_) => read(io::stdin()),
    }
}

fn read_open_file(f: File) -> Result<(Env, ReadStats), ReadError> {
    // Only a regular file's length says anything about its contents.
    let size = match f.metadata() {
        Ok(m) if m.is_file() => m.len(),
        _ => 0,
    };
    let mut st = State::new();
    // About 94% of the lines of a real export are expressions, and a line
    // averages 55 bytes; reserving up front avoids rehashing the big table.
    st.env.exprs.reserve((size / 64).min(1 << 31) as usize);
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
    run(State::new(), r)
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
}

fn run<B: BufRead + Send>(mut st: State, r: B) -> Result<(Env, ReadStats), ReadError> {
    let (full_tx, full_rx) = mpsc::sync_channel::<Batch>(4);
    let (empty_tx, empty_rx) = mpsc::sync_channel::<Batch>(8);
    let res = std::thread::scope(|s| {
        s.spawn(move || produce(r, full_tx, empty_rx));
        st.consume(full_rx, empty_tx)
    });
    let mut stats = res?;
    stats.shared_exprs = st.shared_exprs;
    stats.id_map_bytes =
        st.name_ids.heap_bytes() + st.level_ids.heap_bytes() + st.expr_ids.heap_bytes();
    Ok((st.env, stats))
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

struct State {
    env: Env,
    name_ids: IdMap,
    level_ids: IdMap,
    expr_ids: IdMap,
    shared_exprs: u64,
    // Scratch buffers, reused across records.
    levels_buf: Vec<LevelId>,
    names_buf: Vec<NameId>,
    rules_buf: Vec<RecRule>,
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
            shared_exprs: 0,
            levels_buf: Vec::new(),
            names_buf: Vec::new(),
            rules_buf: Vec::new(),
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
            None => bad(format!(
                "reference to undefined {} id {id} (ids must be defined on an earlier line)",
                t.noun()
            )),
        }
    }

    fn bind(&mut self, t: Table, id: u64, target: u32) -> R<()> {
        let m = match t {
            Table::Name => &mut self.name_ids,
            Table::Level => &mut self.level_ids,
            Table::Expr => &mut self.expr_ids,
        };
        match m.bind(id, target) {
            Ok(()) => Ok(()),
            Err(_) => bad(format!("{} id {id} is defined twice", t.noun())),
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

    /// The interning stage.
    fn consume(
        &mut self,
        full: Receiver<Batch>,
        empty: SyncSender<Batch>,
    ) -> Result<ReadStats, ReadError> {
        let mut tape = Tape::new();
        let mut seen_meta = false;
        loop {
            let Ok(mut batch) = full.recv() else {
                return Err(ReadError {
                    line: 0,
                    class: ErrorClass::Io,
                    msg: "internal error: the parsing thread stopped".into(),
                });
            };
            for (k, item) in batch.items.iter().enumerate() {
                let res = match *item {
                    Item::Raw(a, b) => {
                        let line = batch.text(a, b);
                        parse_object(&mut tape, line).and_then(|(doc, members)| {
                            if seen_meta {
                                self.decl_record(doc, members)
                            } else {
                                seen_meta = true;
                                self.meta(doc, members)
                            }
                        })
                    }
                    _ => self.apply(&batch, *item),
                };
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
    fn apply(&mut self, batch: &Batch, item: Item) -> R<()> {
        match item {
            Item::Name { id, pre, comp } => {
                let pre = self.name(pre)?;
                let node = match comp {
                    Comp::Str(a, b) => {
                        NameNode::Str(pre, self.env.names.strings.intern(batch.text(a, b))?)
                    }
                    Comp::Num(n) => NameNode::Num(pre, n),
                };
                let (n, _) = self.env.names.intern(node)?;
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
            Item::Expr { id, node } => self.apply_expr(batch, id, node),
            Item::Raw(..) => bad("internal error: unexpected raw line"),
        }
    }

    fn apply_expr(&mut self, batch: &Batch, id: u64, node: RawExpr) -> R<()> {
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
                for &u in &batch.us[a as usize..b as usize] {
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
                let Some(n) = parse_nat_lit(batch.text(a, b)) else {
                    return bad("expr.natVal must be a string of decimal digits");
                };
                self.env.exprs.nat_node(n)?
            }
            RawExpr::Str(a, b) => ExprNode::Str(self.env.names.strings.intern(batch.text(a, b))?),
            RawExpr::MData(inner) => {
                // Metadata is kernel-irrelevant: bind the id to the inner
                // expression.
                let inner = self.expr(inner)?;
                self.shared_exprs += 1;
                return self.bind(Table::Expr, id, inner.0);
            }
        };
        let (e, fresh) = self.env.exprs.intern(node, &self.env.levels)?;
        if !fresh {
            self.shared_exprs += 1;
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
        }
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
        let ty = self.expr(o.nat("type")?)?;
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
                let value = self.expr(o.nat("value")?)?;
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
                value: self.expr(o.nat("value")?)?,
                all: self.name_list(&o, "all")?,
            },
            Single::Opaque => DeclKind::Opaque {
                value: self.expr(o.nat("value")?)?,
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
            let mut rules = std::mem::take(&mut self.rules_buf);
            rules.clear();
            let res = (|| {
                for &rv in o.arr("rules")? {
                    let ro = Obj::new(doc, rv, "inductive.recs.rules")?;
                    rules.push(RecRule {
                        ctor: self.name(ro.nat("ctor")?)?,
                        nfields: ro.u32("nfields")?,
                        rhs: self.expr(ro.nat("rhs")?)?,
                    });
                }
                match self.env.push_rules(&rules) {
                    Some(l) => Ok(l),
                    None => Err(Fail::from(Overflow("too many recursor rules"))),
                }
            })();
            self.rules_buf = rules;
            let kind = DeclKind::Recursor {
                all,
                num_params: o.u32("numParams")?,
                num_indices: o.u32("numIndices")?,
                num_motives: o.u32("numMotives")?,
                num_minors: o.u32("numMinors")?,
                rules: res?,
                k: o.bool("k")?,
                is_unsafe: o.bool("isUnsafe")?,
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

    /// Check the fast-path contract on one line; returns whether the fast
    /// path took it.
    fn same_as_general(line: &str) -> bool {
        let mut b = Batch::default();
        let Some(item) = fast::parse(line, &mut b) else {
            return false;
        };
        let fast = describe(&b, item);
        assert_eq!(general(line), Ok(Some(fast)), "line: {line}");
        true
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
