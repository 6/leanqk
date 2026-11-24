//! The `leanqk check` command-line contract: output and exit codes. Until
//! type checking exists, a well-formed export is declined (exit 2) unless
//! `--parse-only` is given
//! (0 accepted, 1 rejected, including any malformed input; 2 declined or
//! usage error: bad arguments, unreadable file, unsupported format version).

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

const META: &str = r#"{"meta":{"format":{"version":"3.1.0"}}}"#;
const GOOD: &str = r#"{"in":1,"str":{"pre":0,"str":"a"}}
{"ie":0,"sort":0}
{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}
"#;

fn leanqk(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_leanqk"))
        .args(args)
        .output()
        .expect("run leanqk")
}

/// Write `contents` to a fresh file under the target directory.
fn temp_file(name: &str, contents: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"));
    let p = dir.join(format!("cli-{}-{name}", std::process::id()));
    std::fs::write(&p, contents).unwrap();
    p
}

fn check(name: &str, contents: &str) -> Output {
    check_with(name, contents, &[])
}

fn check_with(name: &str, contents: &str, flags: &[&str]) -> Output {
    let p = temp_file(name, contents);
    let mut args = vec!["check"];
    args.extend_from_slice(flags);
    args.push(p.to_str().unwrap());
    let out = leanqk(&args);
    let _ = std::fs::remove_file(p);
    out
}

fn text(b: &[u8]) -> String {
    String::from_utf8_lossy(b).into_owned()
}

#[test]
fn well_formed_export_is_declined_until_type_checking_exists() {
    let out = check("good", &format!("{META}\n{GOOD}"));
    assert_eq!(out.status.code(), Some(2), "{}", text(&out.stderr));
    let stdout = text(&out.stdout);
    assert!(stdout.contains("declarations  1"), "{stdout}");
    assert!(
        stdout.contains("parsed 1 declarations; type checking not implemented yet"),
        "{stdout}"
    );
}

#[test]
fn parse_only_accepts_a_well_formed_export() {
    let out = check_with("parseonly", &format!("{META}\n{GOOD}"), &["--parse-only"]);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
    let stdout = text(&out.stdout);
    assert!(stdout.contains("axioms        1"), "{stdout}");
    assert!(!stdout.contains("not implemented"), "{stdout}");
    assert!(!stdout.contains("peak RSS"));
}

#[test]
fn parse_only_still_rejects_and_declines() {
    let bad = format!("{META}\n{{\"foo\":{{}}}}\n");
    let out = check_with("parseonly-bad", &bad, &["--parse-only"]);
    assert_eq!(out.status.code(), Some(1));
    let v2 = "{\"meta\":{\"format\":{\"version\":\"2.0.0\"}}}\n";
    let out = check_with("parseonly-v2", v2, &["--parse-only"]);
    assert_eq!(out.status.code(), Some(2));
}

#[test]
fn stats_flag_prints_time_and_memory() {
    let p = temp_file("stats", &format!("{META}\n{GOOD}"));
    let out = leanqk(&["check", "--stats", "--parse-only", p.to_str().unwrap()]);
    let _ = std::fs::remove_file(p);
    assert_eq!(out.status.code(), Some(0));
    let stdout = text(&out.stdout);
    assert!(stdout.contains("parse time"), "{stdout}");
    assert!(stdout.contains("peak RSS"), "{stdout}");
}

#[test]
fn reads_standard_input() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_leanqk"))
        .args(["check", "--parse-only", "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let input = format!("{META}\n{GOOD}");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();
    let out = child.wait_with_output().unwrap();
    assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
}

#[test]
fn malformed_input_exits_1_with_line_number() {
    let out = check(
        "forward",
        &format!("{META}\n{{\"ie\":0,\"app\":{{\"fn\":1,\"arg\":1}}}}\n"),
    );
    assert_eq!(out.status.code(), Some(1));
    let stderr = text(&out.stderr);
    assert!(stderr.contains("rejected"), "{stderr}");
    assert!(stderr.contains("line 2:"), "{stderr}");
    assert!(stderr.contains("undefined expression id 1"), "{stderr}");
    assert!(out.stdout.is_empty());
}

#[test]
fn every_kind_of_malformed_input_exits_1() {
    let cases = [
        ("json", format!("{META}\n{{\"ie\":0,\"sort\":0\n")),
        (
            "dupid",
            format!("{META}\n{{\"ie\":0,\"sort\":0}}\n{{\"ie\":0,\"sort\":0}}\n"),
        ),
        (
            "field",
            format!("{META}\n{{\"ie\":0,\"app\":{{\"fn\":0}}}}\n"),
        ),
        ("kind", format!("{META}\n{{\"foo\":{{}}}}\n")),
        ("nometa", "{\"ie\":0,\"sort\":0}\n".to_string()),
        ("empty", String::new()),
        ("nul", format!("{META}\n\u{0}\n")),
    ];
    for (name, contents) in cases {
        let out = check(name, &contents);
        assert_eq!(out.status.code(), Some(1), "{name}: {}", text(&out.stderr));
        assert!(text(&out.stderr).contains("rejected"), "{name}");
    }
}

#[test]
fn unsupported_format_version_exits_2() {
    let out = check("v2", "{\"meta\":{\"format\":{\"version\":\"2.0.0\"}}}\n");
    assert_eq!(out.status.code(), Some(2));
    assert!(text(&out.stderr).contains("unsupported export format version 2.0.0"));
}

#[test]
fn duplicate_declaration_exits_1() {
    let axiom = r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#;
    let out = check("dup", &format!("{META}\n{GOOD}{axiom}\n"));
    assert_eq!(out.status.code(), Some(1));
    assert!(text(&out.stderr).contains("rejected"));
}

#[test]
fn missing_file_and_bad_usage_exit_2() {
    let out = leanqk(&["check", "/nonexistent/leanqk-test.ndjson"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(text(&out.stderr).contains("leanqk-test.ndjson"));
    assert_eq!(leanqk(&[]).status.code(), Some(2));
    assert_eq!(leanqk(&["check"]).status.code(), Some(2));
    assert_eq!(leanqk(&["frobnicate"]).status.code(), Some(2));
    assert_eq!(leanqk(&["check", "--bogus", "x"]).status.code(), Some(2));
}

#[test]
fn help_documents_exit_codes() {
    for args in [&["--help"][..], &["check", "--help"][..]] {
        let out = leanqk(args);
        assert_eq!(out.status.code(), Some(0));
        let stdout = text(&out.stdout);
        assert!(stdout.contains("Exit status:"), "{stdout}");
        assert!(stdout.contains("0  accepted"), "{stdout}");
        assert!(stdout.contains("--parse-only"), "{stdout}");
        assert!(stdout.contains("not implemented yet"), "{stdout}");
        assert!(stdout.contains("1  rejected"), "{stdout}");
        assert!(stdout.contains("2  declined or usage error"), "{stdout}");
    }
}

#[test]
fn reads_standard_input_redirected_from_a_file() {
    let p = temp_file("stdin", &format!("{META}\n{GOOD}"));
    let out = Command::new(env!("CARGO_BIN_EXE_leanqk"))
        .args(["check", "--parse-only", "-"])
        .stdin(std::fs::File::open(&p).unwrap())
        .output()
        .unwrap();
    let _ = std::fs::remove_file(p);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
    assert!(text(&out.stdout).contains("axioms        1"));
}
