//! The checker under a limit on address space (`ulimit -v`): the full
//! reservation of its arrays fails there, and the reduced ones must give
//! the same verdicts (see `src/slab.rs`).

use std::os::unix::process::CommandExt;
use std::path::Path;
use std::process::{Command, Output};

/// The limit: a few GiB, far below the full reservation. One checking job,
/// since each checker thread's stack also takes address space.
const LIMIT: u64 = 4 << 30;

fn check(export: &Path, limit: Option<u64>) -> Output {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_nitrolean"));
    cmd.args(["check", "-j", "1"]).arg(export);
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
        let free = check(p, None);
        let limited = check(p, Some(LIMIT));
        let name = p.file_name().unwrap().to_string_lossy();
        assert_eq!(
            (limited.status.code(), &limited.stdout),
            (free.status.code(), &free.stdout),
            "{name}: under the limit: {}",
            String::from_utf8_lossy(&limited.stderr)
        );
        assert!(
            matches!(free.status.code(), Some(0 | 1)),
            "{name}: a verdict"
        );
    }
}
