//! The targeted kernel cases committed under `tests/kernel/exports`, with
//! their verdicts from `tests/kernel/cases.tsv` (`either` accepts both).
//! The larger cases are only generated (see `tests/kernel/README.md`).

use std::path::Path;

use nitrolean::check::check_env;
use nitrolean::reader::read_file;

#[test]
fn committed_kernel_cases_get_their_verdicts() {
    let (ran, wrong) = run_cases("exports");
    assert!(ran >= 90, "only {ran} committed cases found");
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// All the cases, including the large ones `gen.py` writes to `out/cases/`
/// (not committed): `cargo test --release -- --ignored` after generating them.
#[test]
#[ignore]
fn generated_kernel_cases_get_their_verdicts() {
    let (ran, wrong) = run_cases("out/cases");
    assert!(
        ran >= 190,
        "only {ran} generated cases found: run tests/kernel/gen.py"
    );
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// Check the cases of `cases.tsv` found in `tests/kernel/<sub>`; the number
/// run and the wrong verdicts.
fn run_cases(sub: &str) -> (usize, Vec<String>) {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/kernel");
    let tsv = std::fs::read_to_string(dir.join("cases.tsv")).unwrap();
    let mut ran = 0;
    let mut wrong = Vec::new();
    for line in tsv.lines().skip(1) {
        let cols: Vec<&str> = line.split('\t').collect();
        let (id, expected) = (cols[0], cols[2]);
        let path = dir.join(sub).join(format!("{id}.ndjson"));
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
    (ran, wrong)
}
