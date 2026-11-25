//! Running a program in its own process group, with a timeout, its resource
//! usage from wait4(2) and its standard error captured.

use std::io::Read;
use std::os::unix::process::CommandExt;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::time::{Duration, Instant};

use anyhow::{Context, Result};

use crate::util::describe;

/// How a run ended.
pub struct Outcome {
    /// The exit status, or minus the signal that killed it (as Python's
    /// `os.waitstatus_to_exitcode`).
    pub code: i32,
    /// Killed at the timeout.
    pub timed_out: bool,
    /// Wall time in seconds, from start to exit.
    pub wall: f64,
    /// Peak resident memory in KiB (ru_maxrss), of the command and the
    /// children it waited for.
    pub maxrss_kib: u64,
    /// User plus system CPU time in seconds, the same way.
    pub cpu: f64,
    /// Its standard error, if captured.
    pub stderr: Vec<u8>,
}

/// Runs `cmd` in a new process group with stdin from /dev/null; past
/// `timeout` the whole group is killed. Its standard error is captured
/// (up to `stderr_limit` bytes kept) when `capture_stderr`, else left as the
/// caller set it. With `kill_group_after`, the group is killed once the
/// command exits too, so that no child it left behind keeps running.
pub fn run_timed(
    cmd: &mut Command,
    timeout: Option<Duration>,
    capture_stderr: bool,
    stderr_limit: usize,
    kill_group_after: bool,
) -> Result<Outcome> {
    cmd.stdin(Stdio::null()).process_group(0);
    if capture_stderr {
        cmd.stderr(Stdio::piped());
    }
    let start = Instant::now();
    let mut child = cmd
        .spawn()
        .with_context(|| format!("cannot run {}", describe(cmd)))?;
    let pid = child.id() as libc::pid_t;
    let reader = child.stderr.take().map(|mut e| {
        std::thread::spawn(move || {
            let mut buf = Vec::new();
            let _ = e.read_to_end(&mut buf);
            buf.truncate(stderr_limit);
            buf
        })
    });
    let timed_out = AtomicBool::new(false);
    let (tx, rx) = mpsc::channel::<()>();
    let (status, ru) = std::thread::scope(|s| {
        if let Some(t) = timeout {
            let timed_out = &timed_out;
            s.spawn(move || {
                if rx.recv_timeout(t) == Err(mpsc::RecvTimeoutError::Timeout) {
                    timed_out.store(true, Ordering::SeqCst);
                    // SAFETY: plain syscall.
                    unsafe { libc::kill(-pid, libc::SIGKILL) };
                }
            });
        }
        let r = wait4(pid);
        drop(tx);
        r
    });
    let wall = start.elapsed().as_secs_f64();
    if kill_group_after {
        // SAFETY: plain syscall.
        unsafe { libc::kill(-pid, libc::SIGKILL) };
    }
    let stderr = reader
        .map(|r| r.join().unwrap_or_default())
        .unwrap_or_default();
    let code = if libc::WIFEXITED(status) {
        libc::WEXITSTATUS(status)
    } else if libc::WIFSIGNALED(status) {
        -libc::WTERMSIG(status)
    } else {
        status
    };
    let tv = |t: libc::timeval| t.tv_sec as f64 + t.tv_usec as f64 / 1e6;
    Ok(Outcome {
        code,
        timed_out: timed_out.load(Ordering::SeqCst),
        wall,
        maxrss_kib: ru.ru_maxrss.max(0) as u64,
        cpu: tv(ru.ru_utime) + tv(ru.ru_stime),
        stderr,
    })
}

/// Waits for `pid`, retrying on EINTR: its wait status and resource usage.
fn wait4(pid: libc::pid_t) -> (i32, libc::rusage) {
    let mut status = 0;
    // SAFETY: rusage is plain old data.
    let mut ru: libc::rusage = unsafe { std::mem::zeroed() };
    loop {
        // SAFETY: valid pointers to locals.
        let r = unsafe { libc::wait4(pid, &mut status, 0, &mut ru) };
        if r == pid || std::io::Error::last_os_error().kind() != std::io::ErrorKind::Interrupted {
            return (status, ru);
        }
    }
}

/// The first of `candidates` that is a file and says it is GNU time.
pub fn gnu_time(candidates: &[Option<std::path::PathBuf>]) -> Option<std::path::PathBuf> {
    for p in candidates.iter().flatten() {
        if p.is_file() {
            let Ok(out) = Command::new(p).arg("--version").output() else {
                continue;
            };
            let text = [out.stdout, out.stderr].concat();
            if String::from_utf8_lossy(&text).contains("GNU") {
                return Some(p.clone());
            }
        }
    }
    None
}
