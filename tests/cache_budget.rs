//! The checkers' caches give up what they keep between declarations once
//! past their share of `NITROLEAN_CACHE_MIB` (see `Nbe::set_cache_share`).
//! With no room at all, every declaration starts from nothing: the
//! verdicts must not change.

use std::path::Path;
use std::process::{Command, Output};

fn check(export: &Path, cache_mib: Option<&str>) -> Output {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_nitrolean"));
    cmd.arg("check").arg(export).args(["-j", "4"]);
    match cache_mib {
        Some(m) => cmd.env("NITROLEAN_CACHE_MIB", m),
        None => cmd.env_remove("NITROLEAN_CACHE_MIB"),
    };
    cmd.output().expect("run nitrolean")
}

#[test]
fn kernel_exports_check_the_same_with_no_room_for_caches() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/kernel/exports");
    let mut exports: Vec<_> = std::fs::read_dir(&dir)
        .expect("read the exports")
        .map(|e| e.expect("entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "ndjson"))
        .collect();
    exports.sort();
    assert!(!exports.is_empty());
    for p in &exports {
        let name = p.file_name().unwrap().to_string_lossy();
        let free = check(p, None);
        assert!(
            matches!(free.status.code(), Some(0 | 1)),
            "{name}: a verdict"
        );
        let none = check(p, Some("0"));
        assert_eq!(
            (none.status.code(), &none.stdout),
            (free.status.code(), &free.stdout),
            "{name}, no room for caches: {}",
            String::from_utf8_lossy(&none.stderr)
        );
    }
}
