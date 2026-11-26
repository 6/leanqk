//! The checker under a limit on address space (`ulimit -v`): the full
//! reservation of its arrays fails there, and the reduced ones must give
//! the same verdicts (see `src/slab.rs`). So must the checker threads,
//! whose stacks share the room left (see `thread_plan` in `src/check`).

use std::os::unix::process::CommandExt;
use std::path::Path;
use std::process::{Command, Output};

/// The limit: a few GiB, far below the full reservation, and below the
/// default stacks of many checker threads.
const LIMIT: u64 = 3 << 30;

/// Checks `export` with `jobs` checking threads (`None`: the default), under
/// `limit` bytes of address space if given.
fn check(export: &Path, jobs: Option<&str>, limit: Option<u64>) -> Output {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_nitrolean"));
    cmd.arg("check").arg(export).env_remove("NITROLEAN_JOBS");
    if let Some(j) = jobs {
        cmd.args(["-j", j]);
    }
    if let Some(lim) = limit {
        // SAFETY: setrlimit is async-signal-safe; nothing else runs between
        // fork and exec.
        unsafe {
            cmd.pre_exec(move || {
                let r = libc::rlimit {
                    rlim_cur: lim,
                    rlim_max: lim,
                };
                if libc::setrlimit(libc::RLIMIT_AS, &r) != 0 {
                    return Err(std::io::Error::last_os_error());
                }
                Ok(())
            });
        }
    }
    cmd.output().expect("run nitrolean")
}

#[test]
fn kernel_exports_check_the_same_under_an_address_space_limit() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/kernel/exports");
    let mut exports: Vec<_> = std::fs::read_dir(&dir)
        .expect("read the exports")
        .map(|e| e.expect("entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "ndjson"))
        .collect();
    exports.sort();
    assert!(!exports.is_empty());
    for p in &exports {
        let free = check(p, None, None);
        let name = p.file_name().unwrap().to_string_lossy();
        assert!(
            matches!(free.status.code(), Some(0 | 1)),
            "{name}: a verdict"
        );
        for jobs in [None, Some("64")] {
            let limited = check(p, jobs, Some(LIMIT));
            assert_eq!(
                (limited.status.code(), &limited.stdout),
                (free.status.code(), &free.stdout),
                "{name}, {jobs:?} jobs, under the limit: {}",
                String::from_utf8_lossy(&limited.stderr)
            );
        }
    }
}
