//! Running the two checkers on an export, with a time and a memory limit.

use std::fs::File;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

pub struct Checkers {
    pub nitrolean: PathBuf,
    pub leanchecker: PathBuf,
    pub timeout: Duration,
    pub memory_mb: u64,
}

pub struct Verdict {
    /// accept, reject, declined (nitrolean exit 2), timeout, or crash(CODE)
    pub verdict: String,
    pub msg: String,
    pub secs: f64,
}

impl Checkers {
    /// Run a command with the limits; (exit code or None for a signal or a timeout,
    /// combined output, seconds, timed out).
    fn run(&self, cmd: &mut Command, scratch: &Path) -> (Option<i32>, String, f64, bool) {
        let out_path = scratch.with_extension("out");
        let Ok(out) = File::create(&out_path) else {
            return (None, "cannot create output file".into(), 0.0, false);
        };
        let err = out.try_clone().expect("dup output file");
        let mem = self.memory_mb << 20;
        cmd.stdin(Stdio::null()).stdout(out).stderr(err);
        // SAFETY: setrlimit is async-signal-safe; nothing else runs between fork and exec.
        unsafe {
            cmd.pre_exec(move || {
                let lim = libc::rlimit {
                    rlim_cur: mem,
                    rlim_max: mem,
                };
                libc::setrlimit(libc::RLIMIT_AS, &lim);
                Ok(())
            });
        }
        let start = Instant::now();
        let Ok(mut child) = cmd.spawn() else {
            return (None, "cannot start checker".into(), 0.0, false);
        };
        let mut timed_out = false;
        let status = loop {
            match child.try_wait() {
                Ok(Some(s)) => break Some(s),
                Ok(None) => {}
                Err(_) => break None,
            }
            if start.elapsed() > self.timeout {
                let _ = child.kill();
                let _ = child.wait();
                timed_out = true;
                break None;
            }
            let e = start.elapsed();
            std::thread::sleep(if e < Duration::from_millis(50) {
                Duration::from_millis(1)
            } else {
                Duration::from_millis(10)
            });
        };
        let secs = start.elapsed().as_secs_f64();
        let text = std::fs::read(&out_path)
            .map(|b| String::from_utf8_lossy(&b).into_owned())
            .unwrap_or_default();
        let _ = std::fs::remove_file(&out_path);
        (status.and_then(|s| s.code()), text, secs, timed_out)
    }

    pub fn nitrolean(&self, path: &Path) -> Verdict {
        let (code, text, secs, to) =
            self.run(Command::new(&self.nitrolean).arg("check").arg(path), path);
        let msg = text
            .trim()
            .lines()
            .last()
            .unwrap_or("")
            .chars()
            .take(400)
            .collect();
        let verdict = match (to, code) {
            (true, _) => "timeout".into(),
            (_, Some(0)) => "accept".into(),
            (_, Some(1)) => "reject".into(),
            (_, Some(2)) => "declined".into(),
            (_, Some(c)) => format!("crash({c})"),
            (_, None) => "crash(signal)".into(),
        };
        Verdict { verdict, msg, secs }
    }

    pub fn lean(&self, path: &Path) -> Verdict {
        let (code, text, secs, to) = self.run(
            Command::new(&self.leanchecker)
                .arg("--from-export")
                .arg(path),
            path,
        );
        let msg: String = text.trim().replace('\n', " ").chars().take(400).collect();
        let verdict = if to {
            "timeout".into()
        } else if code == Some(0) && msg.contains("accepts") {
            "accept".into()
        } else if msg.contains("rejects")
            || msg.contains("uncaught exception")
            || msg.contains("found a problem")
        {
            "reject".into()
        } else {
            match code {
                Some(c) => format!("crash({c})"),
                None => "crash(signal)".into(),
            }
        };
        Verdict { verdict, msg, secs }
    }
}

pub fn disagree(a: &str, b: &str) -> bool {
    (a == "accept" && b == "reject") || (a == "reject" && b == "accept")
}
