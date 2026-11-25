//! Running a command under `/usr/bin/time -v` with a wall-clock limit and a
//! resident-memory limit (`kc measure`, `oracle run` and `oracle reduce`).
//!
//! The memory limit is enforced by sampling the resident set of the whole
//! process group every 50 ms and killing it above the limit; `ulimit -v` is
//! not used, because checkers that reserve address space up front cannot
//! start under it.

use std::fs;
use std::os::unix::process::{CommandExt, ExitStatusExt};
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use anyhow::{Context, Result};
use regex::Regex;

/// How a limited run ended.
pub struct Limited {
    /// `exited`, `timeout` or `oom`.
    pub status: String,
    /// The exit status when `exited`, else empty.
    pub exit: String,
    /// Wall time in seconds, to 0.01 s.
    pub wall_s: f64,
    /// Peak resident memory in MiB.
    pub peak_mib: i64,
}

/// The resident memory of the processes of group `pgid`, in KiB.
fn group_rss_kib(pgid: i32) -> u64 {
    // SAFETY: plain sysconf.
    let page_kib = (unsafe { libc::sysconf(libc::_SC_PAGESIZE) } / 1024).max(1) as u64;
    let mut total = 0;
    let Ok(rd) = fs::read_dir("/proc") else {
        return 0;
    };
    for e in rd.flatten() {
        let name = e.file_name();
        let Some(pid) = name.to_str().and_then(|s| s.parse::<i32>().ok()) else {
            continue;
        };
        // SAFETY: plain syscall.
        if unsafe { libc::getpgid(pid) } != pgid {
            continue;
        }
        if let Ok(s) = fs::read_to_string(format!("/proc/{pid}/statm"))
            && let Some(Ok(rss)) = s.split_whitespace().nth(1).map(str::parse::<u64>)
        {
            total += rss * page_kib;
        }
    }
    total
}

/// Runs `cmd` (program and arguments) with its output in `log`.
/// With `path`, the command's PATH is that; with `stack_unlimited`, its soft
/// stack limit is raised to the hard one (`ulimit -s unlimited`).
pub fn run_limited(
    cmd: &[std::ffi::OsString],
    log: &Path,
    timeout: f64,
    mem_mib: i64,
    path: Option<&std::ffi::OsStr>,
    stack_unlimited: bool,
) -> Result<Limited> {
    let tf = crate::corpus::temp_path("time-", "");
    let lf = fs::File::create(log).with_context(|| format!("{}: cannot create", log.display()))?;
    let mut c = Command::new("/usr/bin/time");
    c.arg("-v")
        .arg("-o")
        .arg(&tf)
        .args(cmd)
        .stdin(Stdio::inherit())
        .stdout(lf.try_clone()?)
        .stderr(lf)
        .process_group(0);
    if let Some(p) = path {
        c.env("PATH", p);
    }
    if stack_unlimited {
        crate::util::unlimited_stack(&mut c);
    }
    let t0 = Instant::now();
    let mut child = c.spawn().context("cannot run /usr/bin/time")?;
    let pid = child.id() as i32;
    let mut status = "exited";
    let mut peak: u64 = 0;
    let mut code = String::new();
    loop {
        if let Some(st) = child.try_wait()? {
            code = st
                .code()
                .unwrap_or_else(|| -st.signal().unwrap_or(0))
                .to_string();
            break;
        }
        peak = peak.max(group_rss_kib(pid));
        if t0.elapsed().as_secs_f64() > timeout {
            status = "timeout";
        } else if peak > (mem_mib as u64) * 1024 {
            status = "oom";
        }
        if status != "exited" {
            // SAFETY: plain syscall.
            unsafe { libc::kill(-pid, libc::SIGKILL) };
            let _ = child.wait();
            break;
        }
        std::thread::sleep(Duration::from_millis(50));
    }
    let mut wall = t0.elapsed().as_secs_f64();
    let report = fs::read_to_string(&tf).unwrap_or_default();
    let _ = fs::remove_file(&tf);
    let rss = Regex::new(r"Maximum resident set size \(kbytes\): (\d+)").unwrap();
    if let Some(m) = rss.captures(&report) {
        peak = peak.max(m[1].parse().unwrap_or(0));
    }
    let el = Regex::new(r"(?m)Elapsed \(wall clock\) time.*: (?:(\d+):)?(\d+):([\d.]+)$").unwrap();
    if let Some(m) = el.captures(&report)
        && status == "exited"
    {
        let h: f64 = m.get(1).map_or(0.0, |h| h.as_str().parse().unwrap_or(0.0));
        wall = h * 3600.0
            + m[2].parse::<f64>().unwrap_or(0.0) * 60.0
            + m[3].parse::<f64>().unwrap_or(0.0);
    }
    if status != "exited" {
        code.clear();
    }
    Ok(Limited {
        status: status.to_string(),
        exit: code,
        wall_s: format!("{wall:.2}").parse()?,
        peak_mib: format!("{:.0}", peak as f64 / 1024.0).parse()?,
    })
}
