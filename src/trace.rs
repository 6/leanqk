//! `NITROLEAN_TRACE=FILE`: when each block's declaration record was read,
//! when each block was checked (and on which worker), and when the phases
//! of a run ended, for replaying schedules offline. Off unless set; then
//! every event takes a lock, so only for measurements.
//!
//! The file has one event per line, times in nanoseconds since the run
//! started: `phase NAME T`, `arrive BLOCK T`, `check BLOCK WORKER START END PREFIX` (PREFIX 1 if the block's
//! verdict depends only on the export before it: see `check::prefix_block`).

use std::io::Write;
use std::sync::{Mutex, OnceLock};
use std::time::Instant;

enum Event {
    Phase(&'static str, u64),
    Arrive(u32, u64),
    Check(u32, u32, u64, u64, bool),
}

struct Trace {
    t0: Instant,
    path: std::ffi::OsString,
    events: Mutex<Vec<Event>>,
}

static TRACE: OnceLock<Option<Trace>> = OnceLock::new();

fn trace() -> Option<&'static Trace> {
    TRACE
        .get_or_init(|| {
            std::env::var_os("NITROLEAN_TRACE").map(|path| Trace {
                t0: Instant::now(),
                path,
                events: Mutex::new(Vec::new()),
            })
        })
        .as_ref()
}

/// Whether events are recorded. The first call starts the clock.
#[inline]
pub fn on() -> bool {
    trace().is_some()
}

/// Nanoseconds since the clock started (0 when off).
pub fn now() -> u64 {
    trace().map_or(0, |t| t.t0.elapsed().as_nanos() as u64)
}

fn push(e: Event) {
    if let Some(t) = trace() {
        t.events.lock().unwrap_or_else(|e| e.into_inner()).push(e);
    }
}

pub fn phase(name: &'static str) {
    if on() {
        push(Event::Phase(name, now()));
    }
}

pub fn arrive(block: usize) {
    if on() {
        push(Event::Arrive(block as u32, now()));
    }
}

pub fn check(block: usize, worker: usize, start: u64, prefix: bool) {
    if on() {
        push(Event::Check(
            block as u32,
            worker as u32,
            start,
            now(),
            prefix,
        ));
    }
}

/// Write the events to the file (once, at the end of a run).
pub fn write() {
    let Some(t) = trace() else { return };
    let events = std::mem::take(&mut *t.events.lock().unwrap_or_else(|e| e.into_inner()));
    let Ok(f) = std::fs::File::create(&t.path) else {
        return;
    };
    let mut w = std::io::BufWriter::new(f);
    for e in events {
        let _ = match e {
            Event::Phase(n, at) => writeln!(w, "phase {n} {at}"),
            Event::Arrive(b, at) => writeln!(w, "arrive {b} {at}"),
            Event::Check(b, k, s, e, p) => writeln!(w, "check {b} {k} {s} {e} {}", u8::from(p)),
        };
    }
}
