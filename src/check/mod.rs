//! The type checker and the declaration checks, following Lean's C++
//! kernel (`src/kernel` at v4.36.0): `type_checker.cpp` (`tc.rs`),
//! `inductive.cpp` (`inductive.rs`), `quot.cpp` (`quot.rs`),
//! `instantiate.cpp` and `abstract.cpp` (`subst.rs`), `level.cpp`
//! (`univ.rs`, which decides level constraints exactly) and
//! `environment.cpp` (this file).
//!
//! Declarations are checked in export order; each sees only the
//! declarations before it (and, for an unsafe or partial mutual group, the
//! rest of its group). Checking one declaration reads the environment and
//! writes only into its own [`store::Store`] and caches, so declarations
//! are checked on several threads (`check_env_jobs`).

mod eval;
mod shape;
pub use eval::stats as eval_stats;
pub mod ext;
mod fingerprint;
mod fingerprint_table;
pub mod inductive;
pub mod nbe;
pub mod pp;
mod quot;
pub mod store;
mod subst;
pub mod tc;
pub mod univ;

use std::ops::Range;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering::SeqCst};

use crate::env::{Block, BlockKind, Decl, DeclKind, Env, Safety};
use crate::expr::ExprId;
use crate::name::NameId;

use ext::Ext;
use inductive::{IndDecl, IndType, RecNaming, alpha_eq};
use nbe::Nbe;
use store::{LOCAL, NatUnfoldLimit, Store};
use tc::{KErr, Mode, R, Tc, err};

pub use fingerprint::{Checker as Fingerprints, hex as hex_digest, key as fingerprint_key};

/// Why checking stopped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FailKind {
    /// The declaration is not valid.
    Rejected,
    /// A resource limit was hit; this says nothing about validity.
    Resource,
}

#[derive(Clone, Debug)]
pub struct Failure {
    pub kind: FailKind,
    /// The declaration that failed (for an inductive block, its first type).
    pub decl: String,
    pub msg: String,
}

#[derive(Clone, Debug, Default)]
pub struct Report {
    pub declarations: usize,
    /// Built-in extensions that are off, and why.
    pub notes: Vec<String>,
}

/// Blocks a worker takes at a time.
const CHUNK: usize = 32;

/// Called before declarations are checked on several threads: the
/// program's allocator settings for that (see `small_heap_pages` in
/// `src/alloc.rs`).
pub static BEFORE_PARALLEL: std::sync::OnceLock<fn()> = std::sync::OnceLock::new();

/// Bytes the checkers' caches may keep between declarations when several
/// check at once, shared equally (see `Nbe::set_cache_share`):
/// `NITROLEAN_CACHE_MIB`, else 256 MiB. One checker alone keeps less than
/// that on Mathlib.
fn cache_bytes() -> usize {
    std::env::var("NITROLEAN_CACHE_MIB")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .map_or(256 << 20, |mib| mib.saturating_mul(1 << 20))
}

/// Stack for each checker thread: the checker recurses on terms. Under a
/// limit on address space, see [`thread_plan`].
const STACK_BYTES: usize = 1 << 30;
/// The least stack a checker thread gets under a limit on address space
/// (the corpus's deepest cases need about 8 MiB).
const MIN_STACK_BYTES: usize = 256 << 20;
/// The stack of a lone checker thread when even [`MIN_STACK_BYTES`] does
/// not fit.
const LAST_STACK_BYTES: usize = 32 << 20;

/// Checker threads and the stack of each, for `jobs` wanted. With no limit
/// on address space (`ulimit -v`), or room for them, `jobs` threads of
/// [`STACK_BYTES`]. Else the stacks share half the room left under the
/// limit (the other half is for checking), each at least
/// [`MIN_STACK_BYTES`], with fewer threads if they do not fit. The verdict
/// does not depend on the number of threads.
fn thread_plan(jobs: usize) -> (usize, usize) {
    let room = match (address_space_limit(), address_space_used()) {
        (Some(lim), Some(used)) => lim.saturating_sub(used) / 2,
        (Some(lim), None) => lim / 2,
        (None, _) => return (jobs, STACK_BYTES),
    };
    plan_for_room(jobs, usize::try_from(room).unwrap_or(usize::MAX))
}

/// [`thread_plan`] with `room` bytes for the stacks.
fn plan_for_room(jobs: usize, room: usize) -> (usize, usize) {
    if room / STACK_BYTES >= jobs {
        return (jobs, STACK_BYTES);
    }
    if room < MIN_STACK_BYTES {
        return (1, (room >> 20 << 20).max(LAST_STACK_BYTES));
    }
    let stack = ((room / jobs) >> 20 << 20).max(MIN_STACK_BYTES);
    (jobs.min(room / stack), stack)
}

/// The soft limit on this process's address space, if any.
pub(crate) fn address_space_limit() -> Option<u64> {
    let limits = std::fs::read_to_string("/proc/self/limits").ok()?;
    let soft = limits
        .lines()
        .find_map(|l| l.strip_prefix("Max address space"))?
        .split_whitespace()
        .next()?;
    soft.parse().ok()
}

/// The address space this process takes now.
fn address_space_used() -> Option<u64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    let kib = status
        .lines()
        .find_map(|l| l.strip_prefix("VmSize:"))?
        .trim()
        .strip_suffix("kB")?
        .trim();
    Some(kib.parse::<u64>().ok()? << 10)
}

/// Check every declaration of `env`, on as many threads as
/// [`default_jobs`] says, stopping at the first failure.
pub fn check_env(env: &Env) -> Result<Report, Failure> {
    check_env_jobs(env, default_jobs())
}

/// How many blocks a thread starts between looks at the process's size.
const POLL_EVERY: u32 = 16;

/// While the process holds more than this, a thread starts a new block only
/// if no other is checking one. Some blocks take gigabytes (huge literals,
/// long computations); this keeps several of them from running at once.
/// `NITROLEAN_MEM_BUDGET_MIB` is the room beyond what the process held when
/// checking started (`start`, the environment). By default it is three
/// quarters of the memory the process may use (see
/// [`crate::stats::memory_limit_bytes`]), and at least 1 GiB more than
/// `start`.
fn mem_budget(start: u64) -> u64 {
    const MIN_ROOM: u64 = 1 << 30;
    if let Some(mib) = std::env::var("NITROLEAN_MEM_BUDGET_MIB")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
    {
        return start.saturating_add(mib << 20);
    }
    let usable = crate::stats::memory_limit_bytes().map_or(0, |m| m / 4 * 3);
    usable.max(start.saturating_add(MIN_ROOM))
}

/// `NITROLEAN_JOBS` if set, else the number of cores.
pub fn default_jobs() -> usize {
    std::env::var("NITROLEAN_JOBS")
        .ok()
        .and_then(|v| v.parse().ok())
        .filter(|&n| n > 0)
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(1, |n| n.get()))
}

/// Check every declaration of `env` on `jobs` threads. Each block is
/// checked against its export prefix. Workers start with contiguous
/// ranges and take unclaimed work from other ranges as they finish.
/// On failure, the checker reports the first failing block in export
/// order after checking every block before it.
pub fn check_env_jobs(env: &Env, jobs: usize) -> Result<Report, Failure> {
    check_env_size(env)?;
    // Usually every exported record already has its derived metadata. If it
    // differs, use the checked metadata before trusting any dependent block.
    let mut canonical = None;
    loop {
        let decls = canonical.as_deref().unwrap_or(env.decls.as_slice());
        match check_decls(env, decls, jobs) {
            Ok(report) => return Ok(report),
            Err(BlockProblem::Failure(f)) => return Err(f),
            Err(BlockProblem::Metadata(corrections)) => {
                let decls = canonical.get_or_insert_with(|| env.decls.clone());
                for (i, kind) in corrections {
                    decls[i].kind = kind;
                }
            }
        }
    }
}

fn check_env_size(env: &Env) -> Result<(), Failure> {
    let fail = |msg: &str| Failure {
        kind: FailKind::Resource,
        decl: String::new(),
        msg: msg.into(),
    };
    for (n, what) in [
        (env.names.len(), "names"),
        (env.levels.len(), "levels"),
        (env.exprs.len(), "expressions"),
        (env.decls.len(), "declarations"),
    ] {
        if n >= LOCAL as usize {
            return Err(fail(&format!(
                "too many {what} (at most 2^31 are supported)"
            )));
        }
    }
    Ok(())
}

enum BlockProblem {
    Failure(Failure),
    Metadata(Vec<(usize, DeclKind)>),
}

fn check_decls(env: &Env, decls: &[Decl], jobs: usize) -> Result<Report, BlockProblem> {
    let ext = Ext::with_decls(env, decls);
    // `NITROLEAN_DECL_TIMES=FILE`: write each block's first name and check
    // time (seconds) to FILE, for benchmarks.
    let times = std::env::var_os("NITROLEAN_DECL_TIMES")
        .and_then(|p| std::fs::File::create(p).ok())
        .map(|f| Mutex::new(std::io::LineWriter::new(f)));
    check_decls_matching(
        env,
        decls,
        &ext,
        jobs,
        times,
        BEFORE_PARALLEL.get().copied(),
        |_, _, _| true,
    )
}

/// Safe singletons use the export cutoff for all declaration lookups.
/// Inductives can choose auxiliary names using the whole environment.
fn prefix_block(b: &Block, decls: &[Decl]) -> bool {
    b.kind == BlockKind::Single && use_nbe(&decls[0])
}

pub(crate) struct CheckedPrefix {
    blocks: Vec<Block>,
    decls: Vec<Decl>,
    ext: Ext,
}

impl CheckedPrefix {
    pub(crate) fn blocks(&self) -> usize {
        self.blocks.len()
    }
}

pub(crate) fn check_prefix(mut env: Env, jobs: usize) -> Option<CheckedPrefix> {
    const MAX_PREFIX_BLOCKS: usize = 90_000;
    check_env_size(&env).ok()?;
    let end = env.blocks.len().min(MAX_PREFIX_BLOCKS);
    let last = env.blocks.get(end.checked_sub(1)?)?;
    let decl_end = last.start as usize + last.len();
    let ext = Ext::with_decls(&env, &env.decls);
    // The full reader is still running. Keep its allocator settings until
    // it has finished, as in the ordinary check.
    check_decls_matching(&env, &env.decls, &ext, jobs, None, None, |i, b, ds| {
        i < end && prefix_block(b, ds)
    })
    .ok()?;
    env.blocks.truncate(end);
    env.decls.truncate(decl_end);
    Some(CheckedPrefix {
        blocks: env.blocks,
        decls: env.decls,
        ext,
    })
}

/// `prefix` must come from a successful read of the start of this same
/// export. Resolve any failure with the ordinary check, which also
/// applies corrected inductive metadata and reports the first failure.
pub(crate) fn finish_after_prefix(env: &Env, jobs: usize, prefix: CheckedPrefix) -> Option<Report> {
    check_env_size(env).ok()?;
    if !env.blocks.starts_with(&prefix.blocks) || !env.decls.starts_with(&prefix.decls) {
        return None;
    }
    let ext = Ext::with_decls(env, &env.decls);
    if ext != prefix.ext {
        return None;
    }
    let end = prefix.blocks.len();
    drop(prefix);
    check_decls_matching(
        env,
        &env.decls,
        &ext,
        jobs,
        None,
        BEFORE_PARALLEL.get().copied(),
        |i, b, ds| i >= end || !prefix_block(b, ds),
    )
    .ok()
}

fn check_decls_matching(
    env: &Env,
    decls: &[Decl],
    ext: &Ext,
    jobs: usize,
    times: Option<Mutex<std::io::LineWriter<std::fs::File>>>,
    before_parallel: Option<fn()>,
    select: impl Fn(usize, &Block, &[Decl]) -> bool + Sync,
) -> Result<Report, BlockProblem> {
    let (jobs, stack) = thread_plan(jobs.clamp(1, env.blocks.len().max(1)));
    let per_worker = env.blocks.len() / jobs;
    let extra = env.blocks.len() % jobs;
    let cut = |worker: usize| per_worker * worker + worker.min(extra);
    let ranges = (0..jobs)
        .map(|worker| cut(worker)..cut(worker + 1))
        .collect();
    let shared = Shared {
        env,
        decls,
        ext,
        ranges: Mutex::new(ranges),
        first_fail: AtomicUsize::new(usize::MAX),
        failures: Mutex::new(Vec::new()),
        times,
        busy: AtomicUsize::new(0),
        budget: mem_budget(crate::stats::rss_bytes().unwrap_or(0)),
        // One checker has the memory to itself: no cap.
        cache_share: if jobs == 1 {
            usize::MAX
        } else {
            cache_bytes() / jobs
        },
    };
    if jobs > 1
        && let Some(f) = before_parallel
    {
        f();
    }
    std::thread::scope(|s| {
        let workers: Vec<_> = (0..jobs)
            .map(|i| {
                let shared = &shared;
                let select = &select;
                std::thread::Builder::new()
                    .name(format!("nitrolean-check-{i}"))
                    .stack_size(stack)
                    .spawn_scoped(s, move || worker(shared, jobs, i, select))
                    .expect("spawn checker thread")
            })
            .collect();
        for w in workers {
            if w.join().is_err() {
                shared.failures.lock().unwrap().push((
                    usize::MAX,
                    BlockProblem::Failure(Failure {
                        kind: FailKind::Resource,
                        decl: String::new(),
                        msg: "checker thread failed".into(),
                    }),
                ));
            }
        }
    });
    let failures = shared.failures.into_inner().unwrap();
    if let Some((_, f)) = failures.into_iter().min_by_key(|x| x.0) {
        return Err(f);
    }
    Ok(Report {
        declarations: env.decls.len(),
        notes: ext.notes.clone(),
    })
}

/// What the checker threads share.
struct Shared<'e> {
    env: &'e Env,
    decls: &'e [Decl],
    ext: &'e Ext,
    /// One contiguous range of unclaimed blocks per worker.
    ranges: Mutex<Vec<Range<usize>>>,
    /// The first block that failed, so far.
    first_fail: AtomicUsize,
    failures: Mutex<Vec<(usize, BlockProblem)>>,
    times: Option<Mutex<std::io::LineWriter<std::fs::File>>>,
    /// Threads checking a block.
    busy: AtomicUsize,
    budget: u64,
    /// What each thread's caches may keep between declarations.
    cache_share: usize,
}

impl Shared<'_> {
    fn claim(&self, worker: usize) -> Range<usize> {
        let mut ranges = self.ranges.lock().unwrap();
        if ranges[worker].is_empty() {
            let (victim, pending) = ranges
                .iter()
                .enumerate()
                .max_by_key(|(_, pending)| pending.len())
                .unwrap();
            if pending.is_empty() {
                return 0..0;
            }
            // Leave the victim's next blocks adjacent to its current work.
            let len = pending.len();
            let stolen = (len / 2).max(CHUNK).min(len);
            let split = pending.end - stolen;
            ranges[worker] = split..pending.end;
            ranges[victim].end = split;
        }
        let range = &mut ranges[worker];
        let start = range.start;
        range.start = (start + CHUNK).min(range.end);
        start..range.start
    }

    /// Wait until this thread may start a block: the process is under the
    /// memory budget, or no other thread is busy. Then count it busy.
    fn enter(&self, jobs: usize, polls: &mut u32) {
        let over = || crate::stats::rss_bytes().is_some_and(|b| b > self.budget);
        // Reading the process's size costs a system call: look every few
        // blocks, and at every block while over.
        *polls = polls.wrapping_add(1);
        if jobs > 1 && polls.is_multiple_of(POLL_EVERY) && over() {
            *polls = POLL_EVERY - 1;
            let mut waited = 0u64;
            loop {
                // Alone: go on whatever the memory.
                if self.busy.compare_exchange(0, 1, SeqCst, SeqCst).is_ok() {
                    return;
                }
                waited = (waited + 1).min(64);
                std::thread::sleep(std::time::Duration::from_micros(50 * waited));
                if !over() {
                    break;
                }
            }
        }
        self.busy.fetch_add(1, SeqCst);
    }
}

fn worker(
    sh: &Shared<'_>,
    jobs: usize,
    worker: usize,
    select: &impl Fn(usize, &Block, &[Decl]) -> bool,
) {
    let env = sh.env;
    let store = || Store::with_decls(env, sh.decls, !sh.ext.nat_ops_complete);
    let mut tc = Tc::new(store(), sh.ext, 0);
    let make_nbe = || Nbe::for_worker(store(), sh.ext, jobs, sh.cache_share);
    let mut nb = make_nbe();
    let mut i = 0;
    let mut end = 0;
    let mut polls = 0;
    loop {
        if i == end {
            let range = sh.claim(worker);
            if range.is_empty() {
                return;
            }
            // The evaluator caches assume the visible export prefix grows.
            if range.start < end {
                nb = make_nbe();
            }
            i = range.start;
            end = range.end;
        }
        // Blocks after a failure need not be checked.
        if i > sh.first_fail.load(SeqCst) {
            return;
        }
        let b = &env.blocks[i];
        let decls = &sh.decls[b.start as usize..b.start as usize + b.len()];
        if !select(i, b, decls) {
            i += 1;
            continue;
        }
        sh.enter(jobs, &mut polls);
        let first = decls.first().map(|d| d.name);
        let t0 = std::time::Instant::now();
        let mut corrections = Vec::new();
        let res = catch_unwind(AssertUnwindSafe(|| {
            check_block(&mut tc, &mut nb, b, decls, &mut corrections)
        }));
        sh.busy.fetch_sub(1, SeqCst);
        if let (Some(w), Some(n)) = (sh.times.as_ref(), first) {
            use std::io::Write;
            let _ = writeln!(
                w.lock().unwrap(),
                "{}\t{:.6}",
                env.names.display(n),
                t0.elapsed().as_secs_f64()
            );
        }
        let res = match res {
            Ok(r) => r.map_err(|e| (FailKind::Rejected, *e.0)),
            Err(p) => {
                let msg = if p.is::<NatUnfoldLimit>() {
                    NatUnfoldLimit::MESSAGE.into()
                } else {
                    p.downcast_ref::<String>()
                        .cloned()
                        .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
                        .unwrap_or_else(|| "internal error".into())
                };
                // Rebuild: the checker's state may be inconsistent.
                tc = Tc::new(store(), sh.ext, 0);
                nb = make_nbe();
                Err((FailKind::Resource, msg))
            }
        };
        let problem = match res {
            Err((kind, msg)) => {
                let decl = first
                    .map(|n| env.names.display(n).to_string())
                    .unwrap_or_default();
                Some(BlockProblem::Failure(Failure { kind, decl, msg }))
            }
            Ok(()) if !corrections.is_empty() => Some(BlockProblem::Metadata(corrections)),
            Ok(()) => None,
        };
        if let Some(problem) = problem {
            sh.first_fail.fetch_min(i, SeqCst);
            sh.failures.lock().unwrap().push((i, problem));
        }
        i += 1;
    }
}

/// Whether Lean's checker skips `d`: like `Environment.replay`, which
/// `leanchecker --from-export` runs, nitrolean does not check unsafe and
/// partial declarations. They carry no logical content: no safe
/// declaration can refer to them.
fn skipped(d: &Decl) -> bool {
    match d.kind {
        DeclKind::Definition { safety, .. } => safety != Safety::Safe,
        _ => Tc::decl_is_unsafe(d),
    }
}

fn check_block(
    tc: &mut Tc<'_>,
    nb: &mut Nbe<'_>,
    b: &Block,
    decls: &[Decl],
    corrections: &mut Vec<(usize, DeclKind)>,
) -> R<()> {
    if decls.first().is_some_and(skipped) {
        if let Some(d) = decls.iter().find(|d| !skipped(d)) {
            return err(format!(
                "'{}' is declared safe in an unsafe inductive block",
                tc.show(d.name)
            ));
        }
        return Ok(());
    }
    let mdata_errors = &tc.st.env.mdata_errors;
    if !mdata_errors.is_empty()
        && let Some((d, msg)) = decls
            .iter()
            .find_map(|d| mdata_errors.get(&d.name).map(|msg| (d, msg)))
    {
        return err(format!("'{}': {msg}", tc.show(d.name)));
    }
    match b.kind {
        BlockKind::Single if use_nbe(&decls[0]) => check_nbe(tc, nb, b, &decls[0]),
        BlockKind::Single => {
            with_substituting_checker(tc, b.start, |tc| check_single(tc, &decls[0]))
        }
        BlockKind::Inductive { types, ctors, .. } => {
            let start = b.start;
            let mut pre = |e, ps: &[NameId], k: u32| nbe_check_type(nb, start, k, ps, e);
            let pre: Option<&mut inductive::PreCheck<'_>> = INDUCTIVE_NBE.then_some(&mut pre);
            with_substituting_checker(tc, start, |tc| {
                check_inductive_block(tc, decls, types as usize, ctors as usize, corrections, pre)
            })
        }
    }
}

/// The substituting checker starts clean and drops its local state after use.
/// The worker rebuilds it if checking unwinds.
fn with_substituting_checker(
    tc: &mut Tc<'_>,
    limit: u32,
    check: impl FnOnce(&mut Tc<'_>) -> R<()>,
) -> R<()> {
    tc.limit = limit;
    let result = check(tc);
    tc.reset(0);
    result
}

/// Check `d` with the evaluating checker, keeping what it knows from earlier
/// declarations. A failure, or running out of room, is decided again from
/// nothing, so neither the verdict nor the message depends on which
/// declarations this worker checked before. Out of room from nothing, the
/// substituting checker decides.
fn check_nbe(tc: &mut Tc<'_>, nb: &mut Nbe<'_>, b: &Block, d: &Decl) -> R<()> {
    nb.begin(b.start);
    loop {
        let r = catch_unwind(AssertUnwindSafe(|| check_single_nbe(tc, nb, d)));
        match r {
            Ok(Ok(())) => return Ok(()),
            Ok(Err(_)) | Err(_) if !nb.is_fresh() => nb.reset(b.start),
            Ok(Err(e)) => return Err(e),
            Err(p) if p.is::<nbe::OutOfRoom>() || p.is::<NatUnfoldLimit>() => {
                nb.reset(b.start);
                return with_substituting_checker(tc, b.start, |tc| check_single(tc, d));
            }
            Err(p) => std::panic::resume_unwind(p),
        }
    }
}

fn check_dup_lparams(tc: &Tc<'_>, d: &Decl) -> R<()> {
    let ps = tc.st.lparams(d);
    for (i, p) in ps.iter().enumerate() {
        if ps[i + 1..].contains(p) {
            return err(format!(
                "failed to add declaration to environment, duplicate universe level parameter: '{}'",
                tc.show(*p)
            ));
        }
    }
    Ok(())
}

/// Lean's `check_constant_val`: the type is a well-formed type.
fn check_header(tc: &mut Tc<'_>, d: &Decl) -> R<()> {
    check_dup_lparams(tc, d)?;
    let lps: Vec<NameId> = tc.st.lparams(d).to_vec();
    let s = tc.check(d.ty, &lps)?;
    tc.ensure_sort(s)?;
    Ok(())
}

fn check_value(tc: &mut Tc<'_>, d: &Decl, value: crate::expr::ExprId) -> R<()> {
    let value = if crate::env::is_lazy(value) {
        match tc.value(d) {
            Ok(v) => v.unwrap_or(value),
            Err(e) => return err(format!("malformed value: {e}")),
        }
    } else {
        value
    };
    let lps: Vec<NameId> = tc.st.lparams(d).to_vec();
    let vt = tc.check(value, &lps)?;
    if !tc.is_def_eq(vt, d.ty)? {
        return err(format!(
            "declaration type mismatch, value has type {} but is expected to have type {}",
            tc.pp(vt),
            tc.pp(d.ty)
        ));
    }
    Ok(())
}

/// Whether the evaluating checker takes `d`: safe axioms, definitions,
/// theorems and opaque constants.
fn use_nbe(d: &Decl) -> bool {
    match d.kind {
        DeclKind::Axiom { is_unsafe } | DeclKind::Opaque { is_unsafe, .. } => !is_unsafe,
        DeclKind::Definition { safety, .. } => safety == Safety::Safe,
        DeclKind::Theorem { .. } => true,
        _ => false,
    }
}

fn check_single_nbe(tc: &mut Tc<'_>, nb: &mut Nbe<'_>, d: &Decl) -> R<()> {
    check_dup_lparams(tc, d)?;
    nb.lparams.extend_from_slice(tc.st.lparams(d));
    let sort = nb.check_type_sort(d.ty)?;
    if let DeclKind::Theorem { .. } = d.kind
        && !univ::normalizes_to_zero(&nb.st, sort)
    {
        return err(format!("theorem type is not Prop: {}", tc.pp(d.ty)));
    }
    // A value left in its file is built in the store for this check only:
    // nothing else unfolds the declaration being checked.
    match nb.read_value(d) {
        Ok(Some(value)) => nb.check_decl_value(value, d.ty),
        Ok(None) => Ok(()),
        Err(e) => err(format!("malformed value: {e}")),
    }
}

fn check_single(tc: &mut Tc<'_>, d: &Decl) -> R<()> {
    match d.kind {
        DeclKind::Axiom { is_unsafe } => {
            tc.mode = if is_unsafe { Mode::Unsafe } else { Mode::Safe };
            check_header(tc, d)
        }
        DeclKind::Definition {
            value, safety, all, ..
        } => {
            tc.mode = match safety {
                Safety::Safe => Mode::Safe,
                Safety::Unsafe => Mode::Unsafe,
                Safety::Partial => Mode::Partial,
            };
            if safety != Safety::Safe {
                // An unsafe or partial (mutual) group: its members may refer
                // to one another (Lean's `add_mutual`, and `add_definition`
                // for an unsafe one). They must agree on safety and
                // universe parameters.
                let env = tc.st.env;
                let mut extra = Vec::new();
                for &n in env.name_list(all) {
                    let Some(m) = env.find(n) else {
                        return err(format!("mutual declaration '{}' is missing", tc.show(n)));
                    };
                    match m.kind {
                        DeclKind::Definition { safety: s2, .. } if s2 == safety => {}
                        _ => {
                            return err(
                                "invalid mutual definition, declarations must have the same safety annotation",
                            );
                        }
                    }
                    if env.name_list(m.level_params) != env.name_list(d.level_params) {
                        return err(
                            "invalid mutual definition, declarations must have the same universe level parameters",
                        );
                    }
                    extra.push(n);
                }
                check_header(tc, d)?;
                tc.extra = extra;
                tc.extra.push(d.name);
                check_value(tc, d, value)
            } else {
                check_header(tc, d)?;
                check_value(tc, d, value)
            }
        }
        DeclKind::Theorem { value, .. } => {
            tc.mode = Mode::Safe;
            check_header(tc, d)?;
            if !tc.is_prop(d.ty)? {
                return err(format!("theorem type is not Prop: {}", tc.pp(d.ty)));
            }
            check_value(tc, d, value)
        }
        DeclKind::Opaque {
            value, is_unsafe, ..
        } => {
            tc.mode = if is_unsafe { Mode::Unsafe } else { Mode::Safe };
            check_header(tc, d)?;
            check_value(tc, d, value)
        }
        DeclKind::Quot { kind } => {
            check_dup_lparams(tc, d)?;
            tc.check_quot(d, kind)
        }
        DeclKind::Inductive { .. } | DeclKind::Constructor { .. } | DeclKind::Recursor { .. } => {
            err("inductive types, constructors and recursors must come in an inductive block")
        }
    }
}

/// Whether the types of an inductive block and of its constructors are
/// checked by the evaluating checker first (`nbe_check_type`).
const INDUCTIVE_NBE: bool = true;

/// Check with the evaluating checker that `e` is a type under the
/// universe parameters `ps`, with the first `k` declarations of the block
/// at `start` visible. A failure says nothing (the substituting checker
/// decides then), and what was learned goes.
fn nbe_check_type(nb: &mut Nbe<'_>, start: u32, k: u32, ps: &[NameId], e: ExprId) -> bool {
    nb.begin(start + k);
    nb.lparams.extend_from_slice(ps);
    match catch_unwind(AssertUnwindSafe(|| nb.check_type(e))) {
        Ok(Ok(())) => true,
        _ => {
            nb.reset(start + k);
            false
        }
    }
}

fn check_inductive_block(
    tc: &mut Tc<'_>,
    decls: &[Decl],
    ntypes: usize,
    nctors: usize,
    corrections: &mut Vec<(usize, DeclKind)>,
    pre: Option<&mut inductive::PreCheck<'_>>,
) -> R<()> {
    let env = tc.st.env;
    let (types, rest) = decls.split_at(ntypes);
    let (ctors, recs) = rest.split_at(nctors);
    let Some(first) = types.first() else {
        return err("invalid empty (mutual) inductive datatype declaration");
    };
    let DeclKind::Inductive {
        num_params,
        is_unsafe,
        ..
    } = first.kind
    else {
        return err("ill-formed inductive block");
    };
    let lparams: Vec<NameId> = env.name_list(first.level_params).to_vec();
    let mut claimed = vec![false; ctors.len()];
    let mut ind_types = Vec::new();
    for t in types {
        let DeclKind::Inductive {
            num_params: np,
            is_unsafe: u,
            ctors: cs,
            ..
        } = t.kind
        else {
            return err("ill-formed inductive block");
        };
        if np != num_params || u != is_unsafe || env.name_list(t.level_params) != lparams {
            return err(format!(
                "the types of mutual inductive block '{}' disagree on their parameters, universe parameters or safety",
                tc.show(first.name)
            ));
        }
        let mut cv = Vec::new();
        for &c in env.name_list(cs) {
            let Some(i) = ctors.iter().position(|d| d.name == c) else {
                return err(format!(
                    "constructor '{}' of '{}' is not in its inductive block",
                    tc.show(c),
                    tc.show(t.name)
                ));
            };
            if claimed[i] {
                return err(format!("constructor '{}' is claimed twice", tc.show(c)));
            }
            claimed[i] = true;
            cv.push((c, ctors[i].ty));
        }
        ind_types.push(IndType {
            name: t.name,
            ty: t.ty,
            ctors: cv,
        });
    }
    if let Some(i) = claimed.iter().position(|c| !c) {
        return err(format!(
            "constructor '{}' does not belong to any type of its inductive block",
            tc.show(ctors[i].name)
        ));
    }
    let decl = IndDecl {
        lparams: lparams.clone(),
        nparams: num_params,
        types: ind_types,
        is_unsafe,
    };
    let main_rec = tc.rec_name_of(first.name)?;
    let elim_param = recs.iter().find(|r| r.name == main_rec).and_then(|r| {
        let lps = env.name_list(r.level_params);
        (lps.len() == lparams.len() + 1).then(|| lps[0])
    });
    let generated = tc.add_inductive(&decl, &RecNaming { elim_param }, pre)?;
    // The export must contain exactly the derived declarations.
    for g in &generated {
        let Some(x) = decls.iter().find(|x| x.name == g.name) else {
            return err(format!(
                "the inductive block lacks the derived declaration '{}'",
                tc.show(g.name)
            ));
        };
        let kind = compare_decl(tc, g, x)?;
        if kind != x.kind {
            corrections.push((env.by_name[&x.name] as usize, kind));
        }
    }
    if generated.len() != decls.len() {
        let extra = decls
            .iter()
            .find(|x| !generated.iter().any(|g| g.name == x.name))
            .map(|x| tc.show(x.name))
            .unwrap_or_default();
        return err(format!(
            "the inductive block declares '{extra}', which is not derived from its types"
        ));
    }
    Ok(())
}

fn compare_decl(tc: &Tc<'_>, g: &Decl, x: &Decl) -> R<DeclKind> {
    let bad = |what: &str| -> R<DeclKind> {
        Err(KErr::new(format!(
            "'{}' does not match the declaration derived from its inductive type ({what})",
            tc.show(x.name)
        )))
    };
    let names = |l| tc.st.name_list(l).to_vec();
    if names(g.level_params) != names(x.level_params) {
        return bad("universe parameters");
    }
    if !alpha_eq(tc, g.ty, x.ty) {
        return bad("type");
    }
    match (g.kind, x.kind) {
        (
            DeclKind::Inductive {
                num_params: a1,
                all: c1,
                ctors: d1,
                num_indices,
                num_nested,
                is_rec,
                is_reflexive,
                is_unsafe,
            },
            DeclKind::Inductive {
                num_params: a2,
                all: c2,
                ctors: d2,
                ..
            },
        ) => {
            if a1 != a2 {
                return bad("numParams");
            }
            if names(c1) != names(c2) || names(d1) != names(d2) {
                return bad("all or ctors");
            }
            Ok(DeclKind::Inductive {
                num_params: a2,
                num_indices,
                all: c2,
                ctors: d2,
                num_nested,
                is_rec,
                is_reflexive,
                is_unsafe,
            })
        }
        (
            DeclKind::Constructor {
                induct: a1,
                cidx: b1,
                num_params: c1,
                num_fields: d1,
                is_unsafe: e1,
            },
            DeclKind::Constructor {
                induct: a2,
                cidx: b2,
                num_params: c2,
                num_fields: d2,
                ..
            },
        ) => {
            if (a1, b1, c1, d1) != (a2, b2, c2, d2) {
                return bad("induct, cidx, numParams or numFields");
            }
            Ok(DeclKind::Constructor {
                induct: a2,
                cidx: b2,
                num_params: c2,
                num_fields: d2,
                is_unsafe: e1,
            })
        }
        (
            DeclKind::Recursor {
                all: a1,
                num_params: b1,
                num_indices: c1,
                num_motives: d1,
                num_minors: e1,
                rules: f1,
                k: g1,
                is_unsafe: h1,
            },
            DeclKind::Recursor {
                all: a2,
                num_params: b2,
                num_indices: c2,
                num_motives: d2,
                num_minors: e2,
                rules: f2,
                k: g2,
                ..
            },
        ) => {
            if (b1, c1, d1, e1, g1) != (b2, c2, d2, e2, g2) {
                return bad(&format!(
                    "numParams, numIndices, numMotives, numMinors, k: derived {:?}, exported {:?}",
                    (b1, c1, d1, e1, g1),
                    (b2, c2, d2, e2, g2)
                ));
            }
            if names(a1) != names(a2) {
                return bad("all");
            }
            let (r1, r2) = (tc.st.rec_rules(f1), tc.st.rec_rules(f2));
            if r1.len() != r2.len() {
                return bad("number of rules");
            }
            for (p, q) in r1.iter().zip(r2) {
                if p.ctor != q.ctor || p.nfields != q.nfields {
                    return bad("rule constructor or field count");
                }
                if !alpha_eq(tc, p.rhs, q.rhs) {
                    return bad("rule right-hand side");
                }
            }
            Ok(DeclKind::Recursor {
                all: a2,
                num_params: b2,
                num_indices: c2,
                num_motives: d2,
                num_minors: e2,
                rules: f2,
                k: g2,
                is_unsafe: h1,
            })
        }
        _ => bad("kind of declaration"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn thread_stacks_fit_the_room() {
        const G: usize = 1 << 30;
        // Room for all: full stacks.
        assert_eq!(plan_for_room(4, 64 * G), (4, STACK_BYTES));
        assert_eq!(plan_for_room(4, 4 * G), (4, STACK_BYTES));
        // Shared room, then fewer threads at the floor.
        assert_eq!(plan_for_room(4, 2 * G), (4, G / 2));
        assert_eq!(plan_for_room(64, 2 * G), (8, MIN_STACK_BYTES));
        assert_eq!(plan_for_room(2, 300 << 20), (1, MIN_STACK_BYTES));
        // Next to nothing: one thread, a small stack.
        assert_eq!(plan_for_room(8, 100 << 20), (1, 100 << 20));
        assert_eq!(plan_for_room(8, 0), (1, LAST_STACK_BYTES));
        for jobs in 1..100 {
            for room in [0, 1 << 20, 300 << 20, 3 * G, 7 * G + 12345, 200 * G] {
                let (n, stack) = plan_for_room(jobs, room);
                assert!((1..=jobs).contains(&n) && stack <= STACK_BYTES);
                assert!(n == 1 || n * stack <= room);
            }
        }
    }
}
