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

/// A compound expression can share its cached check only when both its
/// universe parameters and the types of the local variables it uses agree.
#[test]
fn inference_checks_respect_declaration_scopes() {
    use nitrolean::check::{FailKind, check_env_jobs};
    use nitrolean::reader::read_str;

    let check = |(first_type, first_value), parameter, (next_type, next_value)| {
        let export = format!(
            r#"{{"meta":{{"format":{{"version":"3.1.0"}}}}}}
{{"in":1,"str":{{"pre":0,"str":"u"}}}}
{{"in":2,"str":{{"pre":0,"str":"v"}}}}
{{"in":3,"str":{{"pre":0,"str":"valid"}}}}
{{"in":4,"str":{{"pre":0,"str":"next"}}}}
{{"il":1,"succ":0}}
{{"il":2,"param":1}}
{{"il":3,"succ":2}}
{{"ie":0,"sort":0}}
{{"ie":1,"sort":1}}
{{"ie":2,"sort":2}}
{{"ie":3,"sort":3}}
{{"ie":4,"bvar":0}}
{{"ie":5,"letE":{{"body":0,"name":0,"nondep":true,"type":3,"value":4}}}}
{{"ie":6,"forallE":{{"binderInfo":"default","body":1,"name":0,"type":3}}}}
{{"ie":7,"lam":{{"binderInfo":"default","body":5,"name":0,"type":3}}}}
{{"ie":8,"letE":{{"body":0,"name":0,"nondep":true,"type":3,"value":2}}}}
{{"ie":9,"forallE":{{"binderInfo":"default","body":1,"name":0,"type":2}}}}
{{"ie":10,"lam":{{"binderInfo":"default","body":5,"name":0,"type":2}}}}
{{"def":{{"all":[3],"hints":{{"regular":1}},"levelParams":[1],"name":3,"safety":"safe","type":{first_type},"value":{first_value}}}}}
{{"def":{{"all":[4],"hints":{{"regular":2}},"levelParams":[{parameter}],"name":4,"safety":"safe","type":{next_type},"value":{next_value}}}}}
"#,
        );
        check_env_jobs(&read_str(&export).unwrap(), 1)
    };
    // The two lambdas share the same let in their body. The second gives
    // #0 a different type while keeping the universe parameter list.
    assert_eq!(check((6, 7), 1, (6, 7)).unwrap().declarations, 2);
    let bad_context = check((6, 7), 1, (9, 10)).unwrap_err();
    assert_eq!(bad_context.kind, FailKind::Rejected);
    assert_eq!(bad_context.decl, "next");
    assert!(bad_context.msg.contains("type mismatch at let"));

    // Both headers are closed, and both values share the same closed let
    // mentioning u. With parameter v it must fail while checking the value.
    assert_eq!(check((1, 8), 1, (1, 8)).unwrap().declarations, 2);
    let bad_universe = check((1, 8), 2, (1, 8)).unwrap_err();
    assert_eq!(bad_universe.kind, FailKind::Rejected);
    assert_eq!(bad_universe.decl, "next");
    assert!(
        bad_universe
            .msg
            .contains("undefined universe level parameter")
    );
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

/// The last domain is A in the context A, B, x : A.
#[test]
fn declaration_lambda_domains_are_checked_in_scope() {
    use nitrolean::check::{FailKind, check_env_jobs};
    use nitrolean::reader::read_str;

    let check = |domain, after_let| {
        let x_body = if after_let { 10 } else { 9 };
        let export = format!(
            r#"{{"meta":{{"format":{{"version":"3.1.0"}}}}}}
{{"in":1,"str":{{"pre":0,"str":"binderClaim"}}}}
{{"il":1,"succ":0}}
{{"ie":0,"sort":1}}
{{"ie":1,"bvar":0}}
{{"ie":2,"bvar":1}}
{{"ie":3,"bvar":2}}
{{"ie":4,"sort":0}}
{{"ie":5,"forallE":{{"binderInfo":"default","body":0,"name":0,"type":3}}}}
{{"ie":6,"forallE":{{"binderInfo":"default","body":5,"name":0,"type":2}}}}
{{"ie":7,"forallE":{{"binderInfo":"default","body":6,"name":0,"type":0}}}}
{{"ie":8,"forallE":{{"binderInfo":"default","body":7,"name":0,"type":0}}}}
{{"ie":9,"lam":{{"binderInfo":"default","body":4,"name":0,"type":{domain}}}}}
{{"ie":10,"letE":{{"name":0,"type":0,"value":3,"body":9,"nondep":false}}}}
{{"ie":11,"lam":{{"binderInfo":"default","body":{x_body},"name":0,"type":2}}}}
{{"ie":12,"lam":{{"binderInfo":"default","body":11,"name":0,"type":0}}}}
{{"ie":13,"lam":{{"binderInfo":"default","body":12,"name":0,"type":0}}}}
{{"def":{{"all":[1],"hints":{{"regular":1}},"levelParams":[],"name":1,"safety":"safe","type":8,"value":13}}}}
"#,
        );
        check_env_jobs(&read_str(&export).unwrap(), 1)
    };

    assert!(check(3, false).is_ok());
    // Inserting the let makes #2 refer to B instead of A. Without the
    // let, #0 refers to x, which is not a type.
    for (domain, after_let, message) in [
        (3, true, "declaration type mismatch"),
        (1, false, "type expected"),
    ] {
        let failure = check(domain, after_let).unwrap_err();
        assert_eq!(failure.kind, FailKind::Rejected);
        assert_eq!(failure.decl, "binderClaim");
        assert!(failure.msg.contains(message), "{}", failure.msg);
    }
}

/// An application's inferred argument type and its domain have distinct
/// universe expressions that become equal after normalization.
#[test]
fn sort_arguments_allow_equal_normalized_levels() {
    use nitrolean::check::check_env_jobs;
    use nitrolean::reader::read_str;

    // P : Sort (max u v), f : Sort (max v u) → Prop, claim := f P.
    let export = r#"{"meta":{"format":{"version":"3.1.0"}}}
{"in":1,"str":{"pre":0,"str":"u"}}
{"in":2,"str":{"pre":0,"str":"v"}}
{"in":3,"str":{"pre":0,"str":"P"}}
{"in":4,"str":{"pre":0,"str":"f"}}
{"in":5,"str":{"pre":0,"str":"claim"}}
{"il":1,"param":1}
{"il":2,"param":2}
{"il":3,"max":[1,2]}
{"il":4,"max":[2,1]}
{"ie":0,"sort":0}
{"ie":1,"sort":3}
{"ie":2,"sort":4}
{"ie":3,"forallE":{"binderInfo":"default","body":0,"name":0,"type":2}}
{"ie":4,"const":{"name":3,"us":[1,2]}}
{"ie":5,"const":{"name":4,"us":[1,2]}}
{"ie":6,"app":{"fn":5,"arg":4}}
{"axiom":{"name":3,"type":1,"levelParams":[1,2],"isUnsafe":false}}
{"axiom":{"name":4,"type":3,"levelParams":[1,2],"isUnsafe":false}}
{"def":{"all":[5],"hints":{"regular":1},"levelParams":[1,2],"name":5,"safety":"safe","type":0,"value":6}}
"#;
    let env = read_str(export).unwrap();
    assert_eq!(check_env_jobs(&env, 1).unwrap().declarations, 3);
}
