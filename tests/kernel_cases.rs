//! The targeted kernel cases committed under `tests/kernel/exports`, with
//! their verdicts from `tests/kernel/cases.tsv` (`either` accepts both).
//! The larger cases are only generated (see `tests/kernel/README.md`).

use std::path::Path;

use leanqk::check::check_env;
use leanqk::reader::read_file;

#[test]
fn committed_kernel_cases_get_their_verdicts() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/kernel");
    let tsv = std::fs::read_to_string(dir.join("cases.tsv")).unwrap();
    let mut ran = 0;
    let mut wrong = Vec::new();
    for line in tsv.lines().skip(1) {
        let cols: Vec<&str> = line.split('\t').collect();
        let (id, expected) = (cols[0], cols[2]);
        let path = dir.join("exports").join(format!("{id}.ndjson"));
        if !path.exists() {
            continue;
        }
        ran += 1;
        let got = match read_file(&path) {
            Ok((env, _)) => match check_env(&env) {
                Ok(_) => "accept",
                Err(_) => "reject",
            },
            Err(_) => "reject",
        };
        if got != expected && expected != "either" {
            wrong.push(format!("{id}: expected {expected}, got {got}"));
        }
    }
    assert!(ran >= 90, "only {ran} committed cases found");
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
