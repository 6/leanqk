//! Checking while the export is read: the reader hands over views of the
//! environment so far (see [`crate::reader::Views`]), at marks through the
//! file and once more when the whole file is read (while its names and
//! expressions are indexed), and checker threads check the views' blocks
//! as they come. Only blocks whose verdict depends on nothing after them
//! are checked early: the blocks [`super::prefix_block`] selects (safe
//! singletons the evaluating checker takes, which look declarations up
//! only before themselves). A view has no index of its expressions, so a
//! check against it may make terms of its own that the environment has
//! (which costs nothing in a verdict: checking never takes two ids for
//! different terms).
//!
//! What an early check finds is a judgment on the condition that the
//! rest of the read agrees with it, which [`finish`] verifies when the
//! read is over: the file is read once (no duplicates made it read again),
//! the names the checker looks up by their text are the same, and so are
//! the built-in extensions the view found, but for the evaluator's
//! (`Ext::EVAL_ONLY`) if the check never asked the evaluator anything.
//! Then the blocks checked early and accepted are not checked again;
//! every other block, and every block an early check failed on or did not
//! finish (whatever the reason), is checked as usual against the whole
//! environment, which decides the verdict and the message exactly as
//! without views. If nothing agrees, every block is checked as usual.

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, OnceLock};

use super::*;
use crate::reader::Views;

/// Names the checker looks up by their text where a view may answer
/// differently from the whole environment (see [`crate::name::Names::find_dotted`]):
/// those of the evaluator. ([`Ext`] has the others, and is compared whole.)
const LOOKED_UP: &[&str] = &[
    "Array.mk",
    "Bool",
    "Bool.false",
    "Bool.true",
    "Decidable",
    "Decidable.decide",
    "Decidable.intro",
    "Decidable.isFalse",
    "Decidable.isTrue",
    "Eq",
    "Eq.refl",
    "List.cons",
    "List.nil",
    "Not",
    "of_decide_eq_false",
    "of_decide_eq_true",
];

/// One view and the work on it.
struct View {
    /// As published, until the first thread to take it prepares it.
    raw: Mutex<Option<Env>>,
    ready: OnceLock<Ready>,
    /// Its blocks not checked in an earlier view.
    from: usize,
    /// The next of them to take.
    next: AtomicUsize,
    /// Its place among the views, from 1.
    id: usize,
    /// Blocks accepted in earlier views, if it may take some of theirs:
    /// then it is the view of the whole file.
    skip: Option<Vec<bool>>,
    /// Whether it is of the whole file.
    whole: bool,
    /// Per block from `from` on: [`PLAIN`] or [`EVAL`] if accepted.
    accepted: Vec<AtomicU8>,
    /// Where it leaves what it found when it goes.
    found: Arc<Mutex<Vec<Found>>>,
}

/// A block accepted without asking the evaluator anything: its verdict
/// does not depend on [`Ext::EVAL_ONLY`].
const PLAIN: u8 = 1;
/// A block accepted with the evaluator's help.
const EVAL: u8 = 2;

/// What a view found: its first block, which of its blocks it accepted
/// (and how), and what must agree with the whole environment.
type Found = (usize, Vec<u8>, (Ext, Vec<Option<NameId>>));

/// A view prepared for checking: its names indexed, its extensions found.
struct Ready {
    env: Env,
    ext: Ext,
    names: Vec<Option<NameId>>,
    /// Whether its built-in extensions look final: else a later view
    /// would likely find more, and this one's checks would be in vain.
    complete: bool,
}

impl View {
    /// Prepared (by the first thread to ask).
    fn ready(&self) -> &Ready {
        self.ready.get_or_init(|| {
            let t = std::time::Instant::now();
            let mut env = self
                .raw
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .take()
                .expect("a view");
            // (Without, if two names are equal: then the read indexes them
            // and reads the file again, and this view is not used.)
            if let Some(t) = env.names.new_index() {
                env.names.set_index(t);
            }
            let ext = Ext::with_decls(&env, &env.decls);
            let names: Vec<_> = LOOKED_UP.iter().map(|s| env.names.find_dotted(s)).collect();
            // A view that lacks something `Ext` looks up (but for the
            // evaluator) is likely to find less than the whole environment
            // (and then its checks are in vain); the last view is of all.
            let complete = self.whole
                || (names.iter().all(Option::is_some)
                    && Ext::kernel_names().all(|s| env.names.find_dotted(s).is_some()));
            if std::env::var_os("NITROLEAN_STREAM_DEBUG").is_some() {
                eprintln!(
                    "view of {} blocks prepared in {:?}: complete {complete} (nat ops {}, lacks {:?})",
                    env.blocks.len(),
                    t.elapsed(),
                    ext.nat_ops_complete,
                    LOOKED_UP
                        .iter()
                        .copied()
                        .chain(Ext::kernel_names())
                        .filter(|s| env.names.find_dotted(s).is_none())
                        .collect::<Vec<_>>()
                );
            }
            Ready {
                env,
                ext,
                names,
                complete,
            }
        })
    }
}

#[derive(Default)]
struct State {
    /// Views in order; the first is the one being worked on.
    views: Vec<Arc<View>>,
    /// Views made at marks so far.
    made: usize,
    /// The last view's [`View::id`].
    id: usize,
    /// Blocks the views since the last drain cover.
    covered: usize,
    /// Threads holding a view.
    busy: usize,
    /// Views were drained: the next one skips what they accepted.
    drained: bool,
    /// The read is over: the threads end.
    over: bool,
}

/// What [`Stream::finish`] gives [`finish`]: per block, whether a view
/// accepted it, and what every view found that must agree with the whole
/// environment.
pub(crate) struct Early {
    found: Vec<Found>,
}

impl Early {
    /// Blocks accepted early.
    pub(crate) fn accepted(&self) -> usize {
        self.found
            .iter()
            .map(|f| f.1.iter().filter(|&&a| a != 0).count())
            .sum()
    }

    /// Views checked.
    pub(crate) fn views(&self) -> usize {
        self.found.len()
    }
}

/// The checker threads' side of reading with views.
pub(crate) struct Stream {
    jobs: usize,
    /// Bytes read at which to make the next view, as a fraction of the
    /// file in thousandths.
    marks: Vec<u64>,
    state: Mutex<State>,
    cv: Condvar,
    /// Set while views are drained: the threads drop theirs.
    stop: AtomicBool,
    found: Arc<Mutex<Vec<Found>>>,
}

impl Stream {
    /// For `jobs` checker threads, with views at the given thousandths of
    /// the file (in increasing order).
    pub(crate) fn new(jobs: usize, marks: Vec<u64>) -> Self {
        Stream {
            jobs,
            marks,
            state: Mutex::new(State::default()),
            cv: Condvar::new(),
            stop: AtomicBool::new(false),
            found: Arc::default(),
        }
    }

    /// The threads' work (each runs this): check the views' blocks as
    /// they come, until the read is over.
    pub(crate) fn work(&self) {
        QUIET.set(true);
        // The view this thread is done with.
        let mut done = 0;
        loop {
            let view = {
                let mut st = self.state.lock().unwrap();
                loop {
                    if st.over {
                        return;
                    }
                    // Past the view this thread finished: the next one.
                    if let Some(v) = st.views.first()
                        && v.id > done
                    {
                        let v = v.clone();
                        st.busy += 1;
                        break v;
                    }
                    st = self.cv.wait(st).unwrap();
                }
            };
            done = view.id;
            self.check_view(&view);
            let mut st = self.state.lock().unwrap();
            // The first thread done with it takes it off the list.
            if st.views.first().is_some_and(|v| v.id == done) {
                st.views.remove(0);
            }
            drop(view);
            st.busy -= 1;
            self.cv.notify_all();
        }
    }

    fn check_view(&self, v: &View) {
        let Ready {
            env, ext, complete, ..
        } = v.ready();
        if !complete {
            return;
        }
        let blocks = env.blocks.len();
        if check_env_size(env).is_err() {
            return;
        }
        let jobs = self.jobs;
        let share = if jobs == 1 {
            usize::MAX
        } else {
            cache_bytes() / jobs
        };
        let store = || Store::with_decls(env, &env.decls, !ext.nat_ops_complete);
        let mut tc = Tc::new(store(), ext, 0);
        let mut nb = Nbe::for_worker(store(), ext, jobs, share);
        let budget = mem_budget(0);
        let mut polls = 0u32;
        loop {
            if self.stop.load(Ordering::Relaxed) {
                return;
            }
            let start = v.next.fetch_add(CHUNK, Ordering::Relaxed);
            if start >= blocks {
                return;
            }
            for i in start..(start + CHUNK).min(blocks) {
                if self.stop.load(Ordering::Relaxed) {
                    return;
                }
                let b = &env.blocks[i];
                let decls = &env.decls[b.start as usize..b.start as usize + b.len()];
                if !prefix_block(b, decls) || v.skip.as_ref().is_some_and(|s| s[i]) {
                    continue;
                }
                // Big blocks wait for the ordinary check, where the
                // memory budget is kept.
                polls = polls.wrapping_add(1);
                if polls.is_multiple_of(POLL_EVERY)
                    && crate::stats::rss_bytes().is_some_and(|r| r > budget)
                {
                    continue;
                }
                let traced = crate::trace::now();
                let asked = eval::entries();
                let mut corrections = Vec::new();
                let res = catch_unwind(AssertUnwindSafe(|| {
                    check_block(&mut tc, &mut nb, b, decls, &mut corrections)
                }));
                crate::trace::check(i, usize::MAX, traced, true);
                match res {
                    Ok(Ok(())) if corrections.is_empty() => {
                        let how = if eval::entries() == asked {
                            PLAIN
                        } else {
                            EVAL
                        };
                        v.accepted[i - v.from].store(how, Ordering::Relaxed);
                    }
                    Ok(_) => {}
                    Err(_) => {
                        tc = Tc::new(store(), ext, 0);
                        nb = Nbe::for_worker(store(), ext, jobs, share);
                    }
                }
            }
        }
    }

    /// What the views found, once the read is over (and the views
    /// drained).
    pub(crate) fn finish(&self) -> Early {
        self.drain();
        self.state.lock().unwrap().over = true;
        self.cv.notify_all();
        let mut found = std::mem::take(&mut *self.found.lock().unwrap());
        found.sort_by_key(|f| f.0);
        Early { found }
    }
}

impl Drop for View {
    fn drop(&mut self) {
        // A view no thread took has nothing to say.
        if let Some(r) = self.ready.take() {
            let acc = self
                .accepted
                .iter()
                .map(|a| a.load(Ordering::Relaxed))
                .collect();
            self.found.lock().unwrap_or_else(|e| e.into_inner()).push((
                self.from,
                acc,
                (r.ext, r.names),
            ));
        }
    }
}

impl Views for Stream {
    fn wanted(&self, done: u64, size: u64) -> bool {
        let st = self.state.lock().unwrap();
        !st.over
            && self
                .marks
                .get(st.made)
                .is_some_and(|&m| m < 1000 && done.saturating_mul(1000) >= size.saturating_mul(m))
    }

    fn wanted_last(&self) -> bool {
        self.marks.last().is_some_and(|&m| m >= 1000)
    }

    fn publish(&self, env: Env) {
        let mut st = self.state.lock().unwrap();
        st.made += 1;
        if st.over || env.blocks.len() <= st.covered {
            return;
        }
        let from = st.covered;
        st.covered = env.blocks.len();
        let n = env.blocks.len() - from;
        let skip = std::mem::take(&mut st.drained).then(|| {
            let mut skip = vec![false; env.blocks.len()];
            for (from, acc, _) in self.found.lock().unwrap().iter() {
                for (i, &a) in acc.iter().enumerate() {
                    if a != 0
                        && let Some(s) = skip.get_mut(from + i)
                    {
                        *s = true;
                    }
                }
            }
            skip
        });
        st.id += 1;
        let v = Arc::new(View {
            id: st.id,
            whole: skip.is_some(),
            skip,
            raw: Mutex::new(Some(env)),
            ready: OnceLock::new(),
            from,
            next: AtomicUsize::new(from),
            accepted: (0..n).map(|_| AtomicU8::new(0)).collect(),
            found: self.found.clone(),
        });
        st.views.push(v);
        self.cv.notify_all();
    }

    fn drain(&self) {
        // For tests: every view checked in full first.
        if std::env::var_os("NITROLEAN_STREAM_FULL").is_some() {
            let mut st = self.state.lock().unwrap();
            while !st.views.is_empty() {
                st = self.cv.wait(st).unwrap();
            }
        }
        self.stop.store(true, Ordering::Relaxed);
        let mut st = self.state.lock().unwrap();
        let views = std::mem::take(&mut st.views);
        while st.busy > 0 {
            st = self.cv.wait(st).unwrap();
        }
        // (The views go, and what they found is kept.)
        drop(views);
        // A view after this one takes every block not accepted yet.
        st.covered = 0;
        st.drained = true;
        self.stop.store(false, Ordering::Relaxed);
    }
}

thread_local! {
    /// Set on the threads that check views: a check that panics there
    /// (out of room, or a value a view cannot build) is checked again
    /// later, so the panic is not reported.
    static QUIET: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Report panics as before, but on the threads that check views.
fn quiet_panics() {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| {
        let report = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if !QUIET.get() {
                report(info);
            }
        }));
    });
}

/// About how many cores a read keeps busy.
const READER_CORES: usize = 3;

/// Run `read` (which reads the export, handing its views to the stream)
/// while threads check the views' blocks (as `jobs` would, but on the
/// cores the read leaves: `NITROLEAN_STREAM_THREADS` says how many); then
/// what they found.
pub(crate) fn read_checking<R: Send>(
    jobs: usize,
    marks: Vec<u64>,
    read: impl FnOnce(&Stream) -> R + Send,
) -> (R, Early) {
    quiet_panics();
    let (jobs, stack) = thread_plan(jobs);
    let stream = Stream::new(jobs, marks);
    // The read keeps about `READER_CORES` busy: the threads take what is
    // left (a reader slowed down slows down everything after it).
    let cores = std::thread::available_parallelism().map_or(1, |n| n.get());
    let threads = std::env::var("NITROLEAN_STREAM_THREADS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| jobs.min(cores.saturating_sub(READER_CORES)).max(1));
    std::thread::scope(|s| {
        for i in 0..threads {
            let stream = &stream;
            // Without the threads, the read goes on alone.
            let _ = std::thread::Builder::new()
                .name(format!("nitrolean-early-{i}"))
                .stack_size(stack)
                .spawn_scoped(s, move || stream.work());
        }
        let r = read(&stream);
        let early = stream.finish();
        (r, early)
    })
}

/// Check `env` on `jobs` threads, as [`check_env_jobs`] does, but for the
/// blocks the views accepted (`early`), if what the views found agrees
/// with it; `same` if it is the environment the views showed the start
/// of. `None` if they do not agree (or there is nothing to skip): then
/// every block is to be checked as usual.
pub(crate) fn finish(
    env: &Env,
    jobs: usize,
    early: &Early,
    same: bool,
) -> Option<Result<Report, Failure>> {
    if !same || early.accepted() == 0 {
        return None;
    }
    check_env_size(env).ok()?;
    let ext = Ext::with_decls(env, &env.decls);
    let names: Vec<_> = LOOKED_UP.iter().map(|s| env.names.find_dotted(s)).collect();
    // The blocks accepted in views that agree with the whole environment.
    let mut accepted = vec![false; env.blocks.len()];
    let mut any = false;
    for (from, acc, (e, n)) in &early.found {
        // Blocks accepted without the evaluator need all but its part.
        let agrees = e.agrees(&ext) && *n == names;
        let plain = e.agrees_but_eval(&ext) && *n == names;
        if std::env::var_os("NITROLEAN_STREAM_DEBUG").is_some() {
            eprintln!(
                "view from block {from}: agrees {agrees}, but for the evaluator {plain} (Ext differs in {:?}, names {})",
                e.differs(&ext),
                *n == names
            );
        }
        if !plain || from + acc.len() > accepted.len() {
            continue;
        }
        for (i, &a) in acc.iter().enumerate() {
            if a == PLAIN || (a == EVAL && agrees) {
                accepted[from + i] = true;
                any = true;
            }
        }
    }
    if !any {
        return None;
    }
    match check_decls_matching(
        env,
        &env.decls,
        &ext,
        jobs,
        None,
        BEFORE_PARALLEL.get().copied(),
        |i, _, _| !accepted[i],
    ) {
        Ok(r) => Some(Ok(r)),
        Err(BlockProblem::Failure(f)) => Some(Err(f)),
        // Corrected metadata: the early checks used the exported one.
        Err(BlockProblem::Metadata(_)) => None,
    }
}
