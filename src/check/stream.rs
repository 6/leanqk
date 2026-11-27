//! Checking while the export is read: the reader hands over views of the
//! environment so far (see [`crate::reader::Views`]), and checker threads
//! check their blocks as they come, each against its view. Only blocks
//! whose verdict depends on nothing after them are checked early: safe
//! singletons, the blocks [`super::prefix_block`] selects (the ones the
//! evaluating checker takes, which look declarations up only before
//! themselves). A view has no index of its expressions, and an index of
//! the names of the first view only, so a check against it may make terms
//! of its own that the environment has (which costs nothing in a verdict:
//! checking never takes two ids for different terms).
//!
//! What an early check finds is a judgment on the condition that the
//! rest of the read agrees with it, which [`finish`] verifies when the
//! read is over: the file is read once (no duplicates made it read again),
//! the built-in extensions found in every view are those of the whole
//! environment, and the names the checker looks up by their text are the
//! same. Then the blocks checked early and accepted are not checked again;
//! every other block, and every block an early check failed on or did not
//! finish (whatever the reason), is checked as usual against the whole
//! environment, which decides the verdict and the message exactly as
//! without views. If anything does not agree, every block is checked as
//! usual.

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
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
    /// Per block from `from` on: accepted.
    accepted: Vec<AtomicBool>,
    /// Where it leaves what it found when it goes.
    found: Arc<Mutex<Vec<Found>>>,
}

/// What a view found: its first block, which of its blocks it accepted,
/// and what must agree with the whole environment.
type Found = (usize, Vec<bool>, (Ext, Vec<Option<NameId>>));

/// A view prepared for checking: its names indexed, its extensions found.
struct Ready {
    env: Env,
    ext: Ext,
    names: Vec<Option<NameId>>,
    /// Whether the built-in extensions are all there: else a later view
    /// would likely find more, and this one's checks would be in vain.
    complete: bool,
}

impl View {
    fn ready(&self) -> &Ready {
        self.ready.get_or_init(|| {
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
            let complete = ext.nat_ops_complete && names.iter().all(Option::is_some);
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
    /// Views made so far, and the blocks they cover.
    made: usize,
    covered: usize,
    /// The read is over (or the views are drained): no more views, and
    /// the threads stop taking blocks.
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
            .map(|f| f.1.iter().filter(|&&a| a).count())
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
    /// Views (and threads holding them) alive.
    alive: Mutex<usize>,
    gone: Condvar,
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
            alive: Mutex::new(0),
            gone: Condvar::new(),
            stop: AtomicBool::new(false),
            found: Arc::default(),
        }
    }

    /// The threads' work (each runs this): check the views' blocks until
    /// the views are drained.
    pub(crate) fn work(&self) {
        QUIET.set(true);
        *self.alive.lock().unwrap() += 1;
        let _left = Left(self);
        let mut current: Option<Arc<View>> = None;
        loop {
            let view = {
                let mut st = self.state.lock().unwrap();
                loop {
                    if st.over {
                        return;
                    }
                    // Past the view this thread finished: the next one.
                    if let Some(v) = st.views.first()
                        && !current.as_ref().is_some_and(|c| Arc::ptr_eq(c, v))
                    {
                        break v.clone();
                    }
                    st = self.cv.wait(st).unwrap();
                }
            };
            current = Some(view.clone());
            self.check_view(&view);
            // The first thread done with it takes it off the list.
            let mut st = self.state.lock().unwrap();
            if st.views.first().is_some_and(|v| Arc::ptr_eq(v, &view)) {
                st.views.remove(0);
                self.cv.notify_all();
            }
            drop(st);
            if self.stop.load(Ordering::Relaxed) {
                return;
            }
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
                if !prefix_block(b, decls) {
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
                let mut corrections = Vec::new();
                let res = catch_unwind(AssertUnwindSafe(|| {
                    check_block(&mut tc, &mut nb, b, decls, &mut corrections)
                }));
                crate::trace::check(i, usize::MAX, traced, true);
                match res {
                    Ok(Ok(())) if corrections.is_empty() => {
                        v.accepted[i - v.from].store(true, Ordering::Relaxed);
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
        let mut found = std::mem::take(&mut *self.found.lock().unwrap());
        found.sort_by_key(|f| f.0);
        Early { found }
    }
}

/// Counts a working thread out when it ends.
struct Left<'a>(&'a Stream);

impl Drop for Left<'_> {
    fn drop(&mut self) {
        let mut n = self.0.alive.lock().unwrap();
        *n -= 1;
        self.0.gone.notify_all();
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
                .is_some_and(|&m| done.saturating_mul(1000) >= size.saturating_mul(m))
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
        let v = Arc::new(View {
            raw: Mutex::new(Some(env)),
            ready: OnceLock::new(),
            from,
            next: AtomicUsize::new(from),
            accepted: (0..n).map(|_| AtomicBool::new(false)).collect(),
            found: self.found.clone(),
        });
        st.views.push(v);
        self.cv.notify_all();
    }

    fn drain(&self) {
        self.stop.store(true, Ordering::Relaxed);
        let views = {
            let mut st = self.state.lock().unwrap();
            st.over = true;
            self.cv.notify_all();
            std::mem::take(&mut st.views)
        };
        drop(views);
        let mut n = self.alive.lock().unwrap();
        while *n > 0 {
            n = self.gone.wait(n).unwrap();
        }
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

/// Run `read` (which reads the export, handing its views to the stream)
/// while `jobs` threads check the views' blocks; then what they found.
pub(crate) fn read_checking<R: Send>(
    jobs: usize,
    marks: Vec<u64>,
    read: impl FnOnce(&Stream) -> R + Send,
) -> (R, Early) {
    quiet_panics();
    let (jobs, stack) = thread_plan(jobs);
    let stream = Stream::new(jobs, marks);
    std::thread::scope(|s| {
        for i in 0..jobs {
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
        let agrees = e.agrees(&ext) && *n == names;
        if std::env::var_os("NITROLEAN_STREAM_DEBUG").is_some() {
            eprintln!("view from block {from}: agrees {agrees}");
        }
        if !agrees || from + acc.len() > accepted.len() {
            continue;
        }
        for (i, &a) in acc.iter().enumerate() {
            if a {
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
