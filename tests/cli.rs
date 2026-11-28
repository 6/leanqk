//! The `nitrolean check` command-line contract: output and exit codes. Until
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

fn nitrolean(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_nitrolean"))
        .args(args)
        .output()
        .expect("run nitrolean")
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
    let out = nitrolean(&args);
    let _ = std::fs::remove_file(p);
    out
}

fn text(b: &[u8]) -> String {
    String::from_utf8_lossy(b).into_owned()
}

#[test]
fn well_typed_export_is_accepted() {
    let out = check("good", &format!("{META}\n{GOOD}"));
    assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
    let stdout = text(&out.stdout);
    assert!(stdout.contains("declarations  1"), "{stdout}");
    assert!(
        stdout.contains("accepted: 1 declarations checked"),
        "{stdout}"
    );
}

/// `axiom a : Prop` and `def b : Prop := Prop`, which is ill-typed.
const BAD_DEF: &str = r#"{"in":1,"str":{"pre":0,"str":"a"}}
{"in":2,"str":{"pre":0,"str":"b"}}
{"ie":0,"sort":0}
{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}
{"def":{"name":2,"levelParams":[],"type":0,"value":0,"hints":"opaque","safety":"safe","all":[2]}}
"#;

#[test]
fn ill_typed_declaration_is_rejected_by_name() {
    let out = check("bad", &format!("{META}\n{BAD_DEF}"));
    assert_eq!(out.status.code(), Some(1), "{}", text(&out.stderr));
    let stderr = text(&out.stderr);
    assert!(stderr.contains("rejected: declaration 'b'"), "{stderr}");
    assert!(stderr.contains("type mismatch"), "{stderr}");
}

#[test]
fn overlapping_check_reports_the_same_late_failure() {
    let input = format!("{META}\n{BAD_DEF}");
    let prefix = input.find("{\"def\":").unwrap();
    let path = temp_file("overlap-late-failure", &input);
    let run = |overlap: bool| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_nitrolean"));
        command
            .args(["check", "--threads", "1", "-j8"])
            .arg(&path)
            .env("NITROLEAN_CHECK_OVERLAP_BYTES", prefix.to_string());
        if overlap {
            command.arg("--overlap");
        }
        command.output().expect("run nitrolean")
    };
    let ordinary = run(false);
    let overlap = run(true);
    std::fs::remove_file(path).unwrap();
    assert_eq!(ordinary.status.code(), Some(1));
    assert_eq!(overlap.status, ordinary.status);
    assert_eq!(overlap.stdout, ordinary.stdout);
    assert_eq!(overlap.stderr, ordinary.stderr);
}

#[test]
fn prefix_check_requires_the_overlap_flag() {
    if std::thread::available_parallelism().is_ok_and(|n| n.get() < 2) {
        return;
    }
    let prefix = format!("{META}\n{GOOD}");
    let input = format!("{prefix}\n");
    let path = temp_file("overlap-opt-in", &input);
    let run = |overlap: bool| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_nitrolean"));
        command
            .args(["check", "--stats", "--threads", "1", "-j8"])
            .arg(&path)
            .env("NITROLEAN_CHECK_OVERLAP_BYTES", prefix.len().to_string())
            .env("NITROLEAN_LAZY_PROOFS", "1")
            .env_remove("NITROLEAN_READ_PROFILE")
            .env_remove("NITROLEAN_DECL_TIMES");
        if overlap {
            command.arg("--overlap");
        }
        let output = command.output().expect("run nitrolean");
        assert_eq!(output.status.code(), Some(0), "{}", text(&output.stderr));
        text(&output.stdout)
    };
    let ordinary = run(false);
    let overlap = run(true);
    std::fs::remove_file(path).unwrap();
    assert!(!ordinary.contains("overlap       "), "{ordinary}");
    assert!(overlap.contains("prefix of 1 blocks reused"), "{overlap}");
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
    let out = nitrolean(&["check", "--stats", "--parse-only", p.to_str().unwrap()]);
    let _ = std::fs::remove_file(p);
    assert_eq!(out.status.code(), Some(0));
    let stdout = text(&out.stdout);
    assert!(stdout.contains("parse time"), "{stdout}");
    assert!(stdout.contains("peak RSS"), "{stdout}");
}

#[test]
fn reads_standard_input() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_nitrolean"))
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
    let out = nitrolean(&["check", "/nonexistent/nitrolean-test.ndjson"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(text(&out.stderr).contains("nitrolean-test.ndjson"));
    assert_eq!(nitrolean(&[]).status.code(), Some(2));
    assert_eq!(nitrolean(&["check"]).status.code(), Some(2));
    assert_eq!(nitrolean(&["frobnicate"]).status.code(), Some(2));
    assert_eq!(nitrolean(&["check", "--bogus", "x"]).status.code(), Some(2));
}

#[test]
fn help_documents_exit_codes() {
    for args in [&["--help"][..], &["check", "--help"][..]] {
        let out = nitrolean(args);
        assert_eq!(out.status.code(), Some(0));
        let stdout = text(&out.stdout);
        assert!(stdout.contains("Exit status:"), "{stdout}");
        assert!(stdout.contains("0  accepted"), "{stdout}");
        assert!(stdout.contains("--parse-only"), "{stdout}");
        assert!(stdout.contains("1  rejected"), "{stdout}");
        assert!(stdout.contains("2  declined or usage error"), "{stdout}");
    }
}

#[test]
fn reads_standard_input_redirected_from_a_file() {
    let p = temp_file("stdin", &format!("{META}\n{GOOD}"));
    let out = Command::new(env!("CARGO_BIN_EXE_nitrolean"))
        .args(["check", "--parse-only", "-"])
        .stdin(std::fs::File::open(&p).unwrap())
        .output()
        .unwrap();
    let _ = std::fs::remove_file(p);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
    assert!(text(&out.stdout).contains("axioms        1"));
}

#[test]
fn nlean_is_the_same_program() {
    let p = temp_file("alias", &format!("{META}\n{GOOD}"));
    let path = p.to_str().unwrap();
    for args in [
        &["check", "--parse-only", path][..],
        &["check", "/nonexistent/nitrolean-test.ndjson"][..],
        &["frobnicate"][..],
        &["--version"][..],
    ] {
        let long = nitrolean(args);
        let short = Command::new(env!("CARGO_BIN_EXE_nlean"))
            .args(args)
            .output()
            .expect("run nlean");
        assert_eq!(long.status.code(), short.status.code(), "{args:?}");
        assert_eq!(long.stdout, short.stdout, "{args:?}");
        // Usage lines name the binary as invoked; everything else matches.
        assert_eq!(
            text(&long.stderr),
            text(&short.stderr).replace("nlean", "nitrolean"),
            "{args:?}"
        );
    }
    let _ = std::fs::remove_file(p);
    let out = Command::new(env!("CARGO_BIN_EXE_nlean"))
        .arg("--help")
        .output()
        .expect("run nlean");
    assert_eq!(out.status.code(), Some(0));
    assert!(text(&out.stdout).contains("Usage: nlean"));
}

/// The Init prefix of an export (several of the reader's chunks, so that
/// `--stream` makes views of it), unpacked to a fresh file with `extra`
/// lines at the end; `None` if `xz` cannot unpack it.
fn init_prefix_with(name: &str, extra: &str) -> Option<PathBuf> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let out = Command::new("xz")
        .arg("-dc")
        .arg(root.join("bench/arena/pgo/init-prefix.ndjson.xz"))
        .output()
        .ok()
        .filter(|o| o.status.success())?;
    let p = temp_file(name, "");
    let mut f = std::fs::File::create(&p).unwrap();
    f.write_all(&out.stdout).unwrap();
    f.write_all(extra.as_bytes()).unwrap();
    Some(p)
}

/// `nitrolean check -j4 [--stream] [--stats] FILE`, read in chunks of 256
/// KiB, with views at 30%, 60% and the end of the file and two threads
/// checking them in full.
fn run_stream(path: &std::path::Path, stream: bool, stats: bool) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_nitrolean"));
    command.args(["check", "-j4"]);
    if stream {
        command.arg("--stream");
    }
    if stats {
        command.arg("--stats");
    }
    command
        .arg(path)
        .env("NITROLEAN_VIEW_MARKS", "300,600,1000")
        .env("NITROLEAN_STREAM_THREADS", "2")
        .env("NITROLEAN_READ_AHEAD_BYTES", "262144")
        .env("NITROLEAN_STREAM_FULL", "1")
        .env_remove("NITROLEAN_LAZY_PROOFS")
        .env_remove("NITROLEAN_DECL_TIMES")
        .env_remove("NITROLEAN_READ_PROFILE")
        .output()
        .expect("run nitrolean")
}

/// Same exit status and output with and without `--stream`.
fn assert_stream_same(path: &std::path::Path) -> Output {
    let ordinary = run_stream(path, false, false);
    let stream = run_stream(path, true, false);
    assert_eq!(stream.status, ordinary.status, "{}", text(&stream.stderr));
    assert_eq!(text(&stream.stdout), text(&ordinary.stdout));
    assert_eq!(text(&stream.stderr), text(&ordinary.stderr));
    stream
}

#[test]
fn stream_accepts_early_and_says_the_same() {
    let Some(path) = init_prefix_with("stream-init", "") else {
        eprintln!("xz cannot unpack the Init prefix: skipped");
        return;
    };
    let out = assert_stream_same(&path);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
    let stats = text(&run_stream(&path, true, true).stdout);
    std::fs::remove_file(path).unwrap();
    let early = stats
        .lines()
        .find(|l| l.starts_with("early "))
        .unwrap_or_else(|| panic!("{stats}"));
    assert!(
        early.ends_with("(used)") && !early.starts_with("early         0 "),
        "{early}"
    );
}

/// `def zzBad : Prop := Prop` after the Init prefix (ids far above its
/// own: they need not be dense).
const LATE_BAD: &str = r#"{"in":90000001,"str":{"pre":0,"str":"zzBad"}}
{"ie":90000001,"sort":0}
{"def":{"name":90000001,"levelParams":[],"type":90000001,"value":90000001,"hints":"opaque","safety":"safe","all":[90000001]}}
"#;

#[test]
fn stream_reports_a_late_failure_as_without() {
    let Some(path) = init_prefix_with("stream-late-bad", LATE_BAD) else {
        return;
    };
    let out = assert_stream_same(&path);
    std::fs::remove_file(path).unwrap();
    assert_eq!(out.status.code(), Some(1));
    assert!(
        text(&out.stderr).contains("'zzBad'"),
        "{}",
        text(&out.stderr)
    );
}

#[test]
fn stream_reports_late_malformed_input_as_without() {
    for (name, extra) in [
        ("stream-late-json", "{\"in\":90000001,\n"),
        ("stream-late-dup-id", "{\"ie\":1,\"sort\":0}\n"),
    ] {
        let Some(path) = init_prefix_with(name, extra) else {
            return;
        };
        let out = assert_stream_same(&path);
        std::fs::remove_file(path).unwrap();
        assert_eq!(out.status.code(), Some(1), "{name}");
    }
}

#[test]
fn stream_after_a_reread_says_the_same() {
    // A second name `Nat`: the read finds two equal names at the end and
    // reads the file again, and the views are not used.
    let extra = r#"{"in":90000001,"str":{"pre":0,"str":"Nat"}}
"#;
    let Some(path) = init_prefix_with("stream-reread", extra) else {
        return;
    };
    assert_stream_same(&path);
    let stats = text(&run_stream(&path, true, true).stdout);
    std::fs::remove_file(path).unwrap();
    assert!(
        stats
            .lines()
            .any(|l| l.starts_with("early ") && !l.ends_with("(used)")),
        "{stats}"
    );
}

#[test]
fn stream_on_small_exports_says_the_same() {
    // Exports with no records, or no declarations, for the views.
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/kernel/exports");
    for name in [
        "fmt-meta-only.ndjson",
        "univ-succ-max.ndjson",
        "fmt-fwd-expr.ndjson",
    ] {
        assert_stream_same(&dir.join(name));
    }
}
