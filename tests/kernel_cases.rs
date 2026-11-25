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

/// All the cases, including the large ones `cargo xtask kernel-cases` writes to `out/cases/`
/// (not committed): `cargo test --release -- --ignored` after generating them.
#[test]
#[ignore]
fn generated_kernel_cases_get_their_verdicts() {
    let (ran, wrong) = run_cases("out/cases");
    assert!(
        ran >= 190,
        "only {ran} generated cases found: run cargo xtask kernel-cases"
    );
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// Check the cases of `cases.tsv` found in `tests/kernel/<sub>`; the number
/// run and the wrong verdicts.
fn run_cases(sub: &str) -> (usize, Vec<String>) {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/kernel");
    let tsv = std::fs::read_to_string(dir.join("cases.tsv")).unwrap();
    // Known bugs: cases nitrolean gets wrong today. Each must still fail, so
    // that a fix also updates the list.
    let open_tsv = std::fs::read_to_string(dir.join("open.tsv")).unwrap();
    let open: Vec<&str> = open_tsv
        .lines()
        .skip(1)
        .filter_map(|l| l.split('\t').next())
        .collect();
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
        let ok = got == expected || expected == "either";
        match (ok, open.contains(&id)) {
            (false, false) => wrong.push(format!("{id}: expected {expected}, got {got}")),
            (true, true) => wrong.push(format!(
                "{id}: now gets its expected verdict ({expected}): remove it from open.tsv"
            )),
            _ => {}
        }
    }
    (ran, wrong)
}

/// The failure reported does not depend on the number of checker threads:
/// it is the first failing block in export order.
#[test]
fn failures_do_not_depend_on_threads() {
    use nitrolean::check::check_env_jobs;
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/kernel/exports");
    let mut seen = 0;
    for entry in std::fs::read_dir(&dir).unwrap() {
        let path = entry.unwrap().path();
        let Ok((env, _)) = read_file(&path) else {
            continue;
        };
        let one = check_env_jobs(&env, 1).map_err(|f| (f.kind, f.decl, f.msg));
        for jobs in [2, 8] {
            let many = check_env_jobs(&env, jobs).map_err(|f| (f.kind, f.decl, f.msg));
            match (&one, &many) {
                (Ok(_), Ok(_)) => {}
                (Err(a), Err(b)) => assert_eq!(a, b, "{}: {jobs} threads", path.display()),
                _ => panic!("{}: verdict differs with {jobs} threads", path.display()),
            }
        }
        seen += 1;
    }
    assert!(seen >= 50, "only {seen} cases read");
}

/// Without a recognized arithmetic definition, reducing a large literal
/// through Nat.rec must stop before expanding it into a unary computation.
#[test]
fn large_nat_unary_reduction_declines() {
    use nitrolean::check::{FailKind, check_env_jobs};
    use nitrolean::reader::read_str;

    // Reuse the Nat and Eq declarations and their export ids.
    let prelude = include_str!("kernel/exports/nat-succ-big.ndjson")
        .split_once("{\"in\":23,")
        .unwrap()
        .0;
    let check = |n, step| {
        let export = format!(
            r#"{prelude}{{"in":23,"str":{{"pre":0,"str":"natRecClaim"}}}}
{{"ie":73,"natVal":"{n}"}}
{{"ie":74,"const":{{"name":19,"us":[3]}}}}
{{"ie":75,"lam":{{"binderInfo":"default","body":43,"name":0,"type":43}}}}
{{"ie":76,"lam":{{"binderInfo":"default","body":{step},"name":0,"type":43}}}}
{{"ie":77,"lam":{{"binderInfo":"default","body":76,"name":0,"type":43}}}}
{{"ie":78,"app":{{"fn":74,"arg":75}}}}
{{"ie":79,"app":{{"fn":78,"arg":46}}}}
{{"ie":80,"app":{{"fn":79,"arg":77}}}}
{{"ie":81,"app":{{"fn":80,"arg":73}}}}
{{"ie":82,"const":{{"name":1,"us":[3]}}}}
{{"ie":83,"app":{{"fn":82,"arg":43}}}}
{{"ie":84,"app":{{"fn":83,"arg":81}}}}
{{"ie":85,"app":{{"fn":84,"arg":46}}}}
{{"ie":86,"const":{{"name":9,"us":[3]}}}}
{{"ie":87,"app":{{"fn":86,"arg":43}}}}
{{"ie":88,"app":{{"fn":87,"arg":46}}}}
{{"thm":{{"all":[23],"levelParams":[],"name":23,"type":85,"value":88}}}}
"#,
        );
        check_env_jobs(&read_str(&export).unwrap(), 1)
    };
    // A successor case that returns the recursive result needs every step.
    assert!(check(12, 1).is_ok());
    for large in [1u128 << 40, 1u128 << 80] {
        let failure = check(large, 1).unwrap_err();
        assert_eq!(failure.kind, FailKind::Resource);
        assert_eq!(failure.decl, "natRecClaim");
        assert!(
            failure
                .msg
                .contains("unary reduction of large Nat literals")
        );
        // A successor case that ignores the recursive result needs one step.
        assert!(check(large, 46).is_ok());
    }
}
