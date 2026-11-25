//! The correctness corpus (corpus/): fetching and exporting it, Lean's
//! verdicts on it, running nitrolean on it, and the .olean equivalence check.

use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use anyhow::{Context, Result, anyhow, bail};
use regex::Regex;

use crate::proc::{gnu_time, run_timed};
use crate::util::{
    self, abs_dir, cell, copy_tree, exit_with, git, log, need, read_tsv, root, run, run_logged,
    sha256_file, squash, truncate, which,
};

const LEAN_TOOLCHAIN: &str = "leanprover/lean4:v4.36.0";
const LEAN_GITHASH: &str = "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9";
const DEFAULT_TIMEOUT: i64 = 120;

// ---------------------------------------------------------------------------
// cargo xtask corpus

/// Run `nitrolean check` on every export of the corpus and compare the verdicts.
///
/// Each test's expected verdict comes from corpus/expected-nitrolean.tsv, its
/// export from DIR/<test id>.ndjson (made by `cargo xtask fetch-corpus`) and
/// its timeout from DIR/manifest.tsv (the Arena's per-test timeout, else
/// --timeout).
///
/// `nitrolean check FILE` exits 0 for accepted, 1 for rejected (malformed
/// input included) and 2 for declined (usage or I/O errors, an unsupported
/// format, or a check it cannot do yet). A test is
///
///   pass     the verdict is the expected one
///   fail     the other verdict
///   pending  nitrolean declined (exit 2), or said "not implemented"; listed
///            and counted, but not a failure unless --strict
///   crash    any other exit status, or killed by a signal
///   timeout  no verdict within the timeout
///   missing  the export is not there (fetch the corpus first)
///
/// and the run exits 1 if any test fails, crashes, times out or is missing
/// (or is pending, with --strict).
///
/// With --parse-only, it runs `nitrolean check --parse-only FILE` instead,
/// which exits 0 once the file has been read: every test expected to be
/// accepted must then exit 0, and a test expected to be rejected may exit 0
/// or 1 (its export may be well formed or not).
#[derive(clap::Args)]
#[command(verbatim_doc_comment)]
pub struct RunArgs {
    /// nitrolean binary (default: target/release/nitrolean)
    #[arg(long, alias = "leanqk")]
    nitrolean: Option<String>,
    #[arg(long)]
    corpus: Option<PathBuf>,
    #[arg(long)]
    expected: Option<PathBuf>,
    /// tests to run at once (default 1, for stable times)
    #[arg(long, short = 'j', default_value_t = 1)]
    jobs: usize,
    /// seconds per test without an Arena timeout
    #[arg(long, default_value_t = 120.0)]
    timeout: f64,
    /// multiply every timeout by this (e.g. for slow machines)
    #[arg(long, default_value_t = 1.0)]
    timeout_scale: f64,
    /// only tests whose id matches this regex
    #[arg(long)]
    filter: Option<String>,
    /// also write the results as TSV here
    #[arg(long)]
    results: Option<PathBuf>,
    /// pending tests fail the run
    #[arg(long)]
    strict: bool,
    /// only check that nitrolean reads every export (nitrolean check --parse-only)
    #[arg(long)]
    parse_only: bool,
    /// table rows only for tests that did not pass
    #[arg(long, short = 'q')]
    quiet: bool,
}

const FAILING: [&str; 4] = ["fail", "crash", "timeout", "missing"];
const STATUSES: [&str; 6] = ["pass", "pending", "fail", "crash", "timeout", "missing"];

struct RunResult {
    code: Option<i32>,
    timed_out: bool,
    time: f64,
    rss: u64,
    stderr: String,
}

static TMP_SEQ: AtomicU64 = AtomicU64::new(0);

/// A fresh path for a temporary file.
pub fn temp_path(prefix: &str, suffix: &str) -> PathBuf {
    let n = TMP_SEQ.fetch_add(1, Ordering::SeqCst);
    std::env::temp_dir().join(format!("{prefix}{}-{n}{suffix}", std::process::id()))
}

/// Runs nitrolean on one export: exit status, wall time, peak RSS, stderr.
fn run_one(
    nitrolean: &str,
    export: &Path,
    timeout: f64,
    time_bin: Option<&Path>,
    parse_only: bool,
) -> Result<RunResult> {
    let tf = temp_path("run-corpus-", ".time");
    let mut argv: Vec<std::ffi::OsString> = Vec::new();
    if let Some(t) = time_bin {
        argv.extend([
            t.into(),
            "-f".into(),
            "%M".into(),
            "-o".into(),
            tf.clone().into(),
        ]);
    }
    argv.push(nitrolean.into());
    argv.push("check".into());
    if parse_only {
        argv.push("--parse-only".into());
    }
    argv.push(export.into());
    let mut cmd = Command::new(&argv[0]);
    cmd.args(&argv[1..]).stdout(Stdio::null());
    let o = run_timed(
        &mut cmd,
        Some(Duration::from_secs_f64(timeout)),
        true,
        usize::MAX,
        false,
    )?;
    let mut code = o.code;
    let mut rss = o.maxrss_kib * 1024;
    if time_bin.is_some() {
        let report = fs::read_to_string(&tf).unwrap_or_default();
        let words: Vec<&str> = report.split_whitespace().collect();
        let text = words.join(" ");
        let re = Regex::new(r"Command terminated by signal (\d+)").unwrap();
        if let Some(m) = re.captures(&text) {
            code = -m[1].parse::<i32>().unwrap_or(0);
        }
        rss = match words.last() {
            Some(w) if !w.is_empty() && w.chars().all(|c| c.is_ascii_digit()) => {
                w.parse::<u64>().unwrap_or(0) * 1024
            }
            _ => 0,
        };
    }
    let _ = fs::remove_file(&tf);
    Ok(RunResult {
        code: Some(code),
        timed_out: o.timed_out,
        time: o.wall,
        rss,
        stderr: String::from_utf8_lossy(&o.stderr).into_owned(),
    })
}

/// Status and observed verdict of one run.
fn classify(expected: &str, r: &RunResult, parse_only: bool) -> (&'static str, String) {
    let code = r.code.unwrap_or(0);
    if r.timed_out {
        return ("timeout", "-".into());
    }
    let not_impl = Regex::new(r"(?i)not (yet )?implemented").unwrap();
    if code == 2 || (code != 0 && not_impl.is_match(&r.stderr)) {
        return ("pending", "declined".into());
    }
    if (code == 0 || code == 1) && parse_only {
        let got = if code == 0 { "parsed" } else { "malformed" };
        let st = if code == 0 || expected == "reject" {
            "pass"
        } else {
            "fail"
        };
        return (st, got.into());
    }
    if code == 0 || code == 1 {
        let got = if code == 0 { "accept" } else { "reject" };
        return (if got == expected { "pass" } else { "fail" }, got.into());
    }
    let got = if code > 0 {
        format!("exit {code}")
    } else {
        format!("signal {}", -code)
    };
    ("crash", got)
}

fn first_line(text: &str) -> String {
    for line in text.lines() {
        if !line.trim().is_empty() {
            return truncate(line.trim(), 160);
        }
    }
    String::new()
}

pub fn run_main(a: RunArgs) -> Result<()> {
    let code = run_corpus(a)?;
    if code != 0 {
        return Err(exit_with(code, ""));
    }
    Ok(())
}

fn run_corpus(a: RunArgs) -> Result<i32> {
    let root = root();
    let nitrolean = a.nitrolean.clone().unwrap_or_else(|| {
        root.join("target/release/nitrolean")
            .to_string_lossy()
            .into_owned()
    });
    if !(Path::new(&nitrolean).is_file() || which(&nitrolean).is_some()) {
        eprintln!("run-corpus: {nitrolean} not found (cargo build --release)");
        return Ok(2);
    }
    let corpus = a
        .corpus
        .clone()
        .unwrap_or_else(|| root.join("corpus/exports"));
    let expected = a
        .expected
        .clone()
        .unwrap_or_else(|| root.join("corpus/expected-nitrolean.tsv"));
    let mut tests = read_tsv(&expected)?;
    if let Some(f) = &a.filter {
        let re = Regex::new(f).with_context(|| format!("bad --filter {f}"))?;
        tests.retain(|t| re.is_match(cell(t, "test_id")));
    }
    let mut timeouts: HashMap<String, f64> = HashMap::new();
    let manifest = corpus.join("manifest.tsv");
    if manifest.exists() {
        for r in read_tsv(&manifest)? {
            let t = cell(&r, "timeout");
            if !t.is_empty() {
                let v: f64 = t
                    .parse()
                    .with_context(|| format!("{}: bad timeout {t}", manifest.display()))?;
                timeouts.insert(cell(&r, "id").to_string(), v);
            }
        }
    } else if !tests.is_empty() {
        eprintln!(
            "run-corpus: no {}; run cargo xtask fetch-corpus first",
            manifest.display()
        );
    }

    let time_bin = gnu_time(&[Some("/usr/bin/time".into()), which("gtime")]);
    if time_bin.is_none() {
        eprintln!("run-corpus: no GNU time; peak memory includes the runner's own");
    }

    let wall = Instant::now();
    let width = tests
        .iter()
        .map(|t| cell(t, "test_id").chars().count())
        .max()
        .unwrap_or(0)
        .max(4);
    println!(
        "{:8} {:width$} {:7} {:9} {:>8} {:>9}  note",
        "status", "test", "expect", "got", "time s", "peak MiB"
    );
    struct Row {
        id: String,
        verdict: String,
        status: &'static str,
        got: String,
        time: f64,
        rss: u64,
        note: String,
    }
    let mut results: Vec<Row> = Vec::new();
    let mut first_err: Option<anyhow::Error> = None;
    let run = |t: HashMap<String, String>| -> Result<Row> {
        let id = cell(&t, "test_id").to_string();
        let verdict = cell(&t, "verdict").to_string();
        let export = corpus.join(format!("{id}.ndjson"));
        let timeout = timeouts.get(&id).copied().unwrap_or(a.timeout) * a.timeout_scale;
        let (status, got, r) = if !export.exists() {
            let r = RunResult {
                code: None,
                timed_out: false,
                time: 0.0,
                rss: 0,
                stderr: String::new(),
            };
            ("missing", "-".to_string(), r)
        } else {
            let r = run_one(
                &nitrolean,
                &export,
                timeout,
                time_bin.as_deref(),
                a.parse_only,
            )?;
            let (s, g) = classify(&verdict, &r, a.parse_only);
            (s, g, r)
        };
        let note = if status == "timeout" {
            format!("killed after {} s", util::fmt_g(timeout))
        } else if status != "pass" {
            first_line(&r.stderr)
        } else {
            String::new()
        };
        Ok(Row {
            id,
            verdict,
            status,
            got,
            time: r.time,
            rss: r.rss,
            note,
        })
    };
    util::par_map_ordered(tests, a.jobs.max(1), run, |row| match row {
        Err(e) => {
            first_err.get_or_insert(e);
        }
        Ok(row) => {
            if !(a.quiet && row.status == "pass") {
                println!(
                    "{:8} {:width$} {:7} {:9} {:8.2} {:9.1}  {}",
                    row.status,
                    row.id,
                    row.verdict,
                    row.got,
                    row.time,
                    row.rss as f64 / 1048576.0,
                    row.note
                );
                let _ = std::io::stdout().flush();
            }
            results.push(row);
        }
    });
    if let Some(e) = first_err {
        return Err(e);
    }
    let wall = wall.elapsed().as_secs_f64();

    let mut counts: BTreeMap<&str, usize> = STATUSES.iter().map(|s| (*s, 0)).collect();
    for r in &results {
        *counts.get_mut(r.status).unwrap() += 1;
    }
    let total_time: f64 = results.iter().map(|r| r.time).sum();
    let peak = results.iter().map(|r| r.rss).max().unwrap_or(0);
    let summary = STATUSES
        .iter()
        .filter(|s| counts[*s] > 0 || ["pass", "fail", "timeout", "pending"].contains(s))
        .map(|s| format!("{} {s}", counts[s]))
        .collect::<Vec<_>>()
        .join(", ");
    println!();
    println!("run-corpus: {} tests: {summary}", results.len());
    println!(
        "run-corpus: {total_time:.1} s in nitrolean ({wall:.1} s wall), peak {:.1} MiB",
        peak as f64 / 1048576.0
    );
    let mut bad: Vec<&str> = FAILING.iter().copied().filter(|s| counts[s] > 0).collect();
    if a.strict && counts["pending"] > 0 {
        bad.push("pending");
    }

    if let Some(path) = &a.results {
        let mut s = String::from("test_id\texpected\tstatus\tgot\ttime_s\tpeak_kib\tnote\n");
        for r in &results {
            s.push_str(&format!(
                "{}\t{}\t{}\t{}\t{:.3}\t{}\t{}\n",
                r.id,
                r.verdict,
                r.status,
                r.got,
                r.time,
                r.rss / 1024,
                r.note.replace('\t', " ")
            ));
        }
        fs::write(path, s).with_context(|| format!("{}: cannot write", path.display()))?;
    }
    if let Some(step) = std::env::var_os("GITHUB_STEP_SUMMARY") {
        let mut s = format!(
            "## Corpus{}\n\n| status | tests |\n|---|---:|\n",
            if a.parse_only { " (parse only)" } else { "" }
        );
        for st in STATUSES {
            s.push_str(&format!("| {st} | {} |\n", counts[st]));
        }
        s.push_str(&format!(
            "\n{total_time:.1} s in nitrolean, peak {:.1} MiB\n\n",
            peak as f64 / 1048576.0
        ));
        let unexpected: Vec<&Row> = results
            .iter()
            .filter(|r| FAILING.contains(&r.status))
            .collect();
        if !unexpected.is_empty() {
            s.push_str("| test | expected | status | got | note |\n|---|---|---|---|---|\n");
            for r in unexpected.iter().take(200) {
                s.push_str(&format!(
                    "| `{}` | {} | {} | {} | {} |\n",
                    r.id,
                    r.verdict,
                    r.status,
                    r.got,
                    r.note.replace('|', "/")
                ));
            }
        }
        fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(step)?
            .write_all(s.as_bytes())?;
    }
    if !bad.is_empty() {
        println!("run-corpus: FAILED ({})", bad.join(", "));
        return Ok(1);
    }
    let pending = counts["pending"];
    if pending > 0 {
        println!("run-corpus: OK ({pending} pending)");
    } else {
        println!("run-corpus: OK");
    }
    Ok(0)
}

// ---------------------------------------------------------------------------
// Checksums and collecting exports

#[derive(clap::Args)]
pub struct ChecksumArgs {
    /// The directory of exports (default: corpus/exports)
    out: Option<PathBuf>,
    /// Check them against this file instead of printing them
    #[arg(long)]
    check: Option<PathBuf>,
    /// With --check, let exports through that the file doesn't list
    #[arg(long)]
    allow_extra: bool,
}

pub fn checksums_main(a: ChecksumArgs) -> Result<()> {
    let out = a.out.unwrap_or_else(|| root().join("corpus/exports"));
    let text = checksums(&out, a.check.as_deref(), a.allow_extra)?;
    print!("{text}");
    Ok(())
}

/// The `.ndjson` files under `dir`, as sorted relative paths.
pub fn ndjson_files(dir: &Path) -> Result<Vec<String>> {
    let mut all = Vec::new();
    if dir.is_dir() {
        util::find_files(dir, ".", &[], &mut all)?;
    }
    let mut files: Vec<String> = all
        .into_iter()
        .map(|f| f.trim_start_matches("./").to_string())
        .filter(|f| f.ends_with(".ndjson"))
        .collect();
    files.sort();
    Ok(files)
}

/// The SHA-256 lines of every export in `out` or, with `check`, nothing
/// after checking them against that file.
fn checksums(out: &Path, check: Option<&Path>, allow_extra: bool) -> Result<String> {
    let files = ndjson_files(out)?;
    let mut got = HashMap::new();
    for f in &files {
        got.insert(f.clone(), sha256_file(&out.join(f))?);
    }
    let Some(check) = check else {
        return Ok(files.iter().map(|f| format!("{}  {f}\n", got[f])).collect());
    };
    let mut want: Vec<(String, String)> = Vec::new();
    let text =
        fs::read_to_string(check).with_context(|| format!("{}: cannot read", check.display()))?;
    for line in text.lines() {
        let line = line.trim_start();
        let (digest, name) = line
            .split_once(char::is_whitespace)
            .ok_or_else(|| anyhow!("{}: bad line {line}", check.display()))?;
        let name = name.trim().to_string();
        if let Some(e) = want.iter_mut().find(|(n, _)| *n == name) {
            e.1 = digest.to_string();
        } else {
            want.push((name, digest.to_string()));
        }
    }
    let bad: Vec<&String> = want
        .iter()
        .filter(|(f, d)| got.get(f).is_some_and(|g| g != d))
        .map(|(f, _)| f)
        .collect();
    let missing: Vec<&String> = want
        .iter()
        .filter(|(f, _)| !got.contains_key(f))
        .map(|(f, _)| f)
        .collect();
    let extra: Vec<&String> = files
        .iter()
        .filter(|f| !want.iter().any(|(n, _)| n == *f))
        .collect();
    for f in &bad {
        eprintln!("checksum mismatch: {f}");
    }
    for f in &missing {
        eprintln!("missing export: {f}");
    }
    for f in &extra {
        let what = if allow_extra {
            "unchecked"
        } else {
            "unexpected"
        };
        eprintln!("{what} export: {f}");
    }
    if !bad.is_empty() || !missing.is_empty() || (!extra.is_empty() && !allow_extra) {
        return Err(exit_with(
            1,
            format!(
                "corpus-checksums: {} mismatched, {} missing, {} extra exports (against {})",
                bad.len(),
                missing.len(),
                extra.len(),
                check.display()
            ),
        ));
    }
    eprintln!(
        "corpus-checksums: {} exports match {}",
        want.len(),
        check.file_name().unwrap_or_default().to_string_lossy()
    );
    Ok(String::new())
}

fn manifest_line(id: &str, source: &str, expected: &str, timeout: &str, origin: &str) -> String {
    [id, source, expected, timeout, &squash(origin)].join("\t")
}

/// Copies the exports `lka.py build-test` left in `build_dir` to OUT/arena/;
/// their manifest lines.
fn collect_arena(build_dir: &Path, out: &Path) -> Result<Vec<String>> {
    let mut all = Vec::new();
    util::find_files(build_dir, ".", &[], &mut all)?;
    let mut stats: Vec<String> = all
        .into_iter()
        .map(|f| f.trim_start_matches("./").to_string())
        .filter(|f| f.ends_with(".stats.json") && f.split('/').next() != Some("work"))
        .collect();
    stats.sort();
    let mut lines = Vec::new();
    for s in stats {
        let path = build_dir.join(&s);
        let v: serde_json::Value = serde_json::from_str(&fs::read_to_string(&path)?)
            .with_context(|| format!("{}: bad JSON", path.display()))?;
        let export = build_dir.join(format!("{}.ndjson", &s[..s.len() - ".stats.json".len()]));
        let name = v["name"]
            .as_str()
            .ok_or_else(|| anyhow!("{}: no name", path.display()))?;
        let dest = out.join("arena").join(format!("{name}.ndjson"));
        fs::create_dir_all(dest.parent().unwrap())?;
        fs::copy(&export, &dest).with_context(|| format!("copying {}", export.display()))?;
        let timeout = json_str_or_empty(&v["timeout"]);
        let origin = v["yaml_file"].as_str().unwrap_or("");
        let outcome = v["outcome"].as_str().unwrap_or("");
        lines.push(manifest_line(
            &format!("arena/{name}"),
            "arena",
            outcome,
            &timeout,
            origin,
        ));
    }
    if lines.is_empty() {
        bail!("fetch-corpus: no exports found in {}", build_dir.display());
    }
    Ok(lines)
}

/// Python's `str(x or "")` of a JSON value.
fn json_str_or_empty(v: &serde_json::Value) -> String {
    match v {
        serde_json::Value::Null => String::new(),
        serde_json::Value::Bool(false) => String::new(),
        serde_json::Value::Bool(true) => "True".into(),
        serde_json::Value::Number(n) if n.as_f64() == Some(0.0) => String::new(),
        serde_json::Value::Number(n) => n.to_string(),
        serde_json::Value::String(s) => s.clone(),
        other => other.to_string(),
    }
}

/// Copies the exports a file using the Arena's tutorial machinery wrote to
/// CASES_DIR/{good,bad}/ to OUT/SOURCE/; their manifest lines, sorted.
fn collect_cases(cases_dir: &Path, out: &Path, source: &str) -> Result<Vec<String>> {
    let mut lines = Vec::new();
    for (verdict, sub) in [("accept", "good"), ("reject", "bad")] {
        let d = cases_dir.join(sub);
        let mut names: Vec<String> = match fs::read_dir(&d) {
            Ok(rd) => rd
                .filter_map(|e| e.ok())
                .map(|e| e.file_name().to_string_lossy().into_owned())
                .filter(|n| n.ends_with(".ndjson") && !n.starts_with('.'))
                .collect(),
            Err(_) => Vec::new(),
        };
        names.sort();
        for n in names {
            let export = d.join(&n);
            if fs::metadata(&export)?.len() == 0 {
                bail!("fetch-corpus: empty export {}", export.display());
            }
            let stem = &n[..n.len() - ".ndjson".len()];
            let dest = out.join(source).join(&n);
            fs::create_dir_all(dest.parent().unwrap())?;
            fs::copy(&export, &dest)?;
            lines.push(manifest_line(
                &format!("{source}/{stem}"),
                source,
                verdict,
                "",
                &format!("corpus/lean ({stem})"),
            ));
        }
    }
    if lines.is_empty() {
        bail!("fetch-corpus: no exports found in {}", cases_dir.display());
    }
    lines.sort();
    Ok(lines)
}

// ---------------------------------------------------------------------------
// cargo xtask fetch-corpus

/// Fetch the kernel-checker test corpus and export it as NDJSON.
///
/// Every source is fetched at a pinned commit and its content is checked
/// against a pinned SHA-256; the exports are made with the `leanexport` of the
/// pinned Lean toolchain and checked against corpus/exports.sha256, so that
/// every run produces the same files byte for byte. See corpus/SOURCES.md for
/// the sources. Needs git, curl, elan and uv (`mise install` gives uv).
#[derive(clap::Args)]
pub struct FetchArgs {
    /// also build the large real-world exports (Init, Std, Mathlib, ...) that
    /// the Arena marks `skip-on-ci`; these take hours and tens of GB, and are
    /// not in corpus/exports.sha256
    #[arg(long)]
    full: bool,
    /// where to put the exports (default: corpus/exports)
    #[arg(long)]
    out: Option<PathBuf>,
    /// where to keep sources and build directories (default: corpus/.cache)
    #[arg(long)]
    cache: Option<PathBuf>,
    /// rewrite corpus/exports.sha256 instead of checking it
    #[arg(long)]
    update_checksums: bool,
}

/// name, url, commit, paths used, content SHA-256
const SOURCES: [(&str, &str, &str, &str, &str); 3] = [
    (
        "arena",
        "https://github.com/leanprover/lean-kernel-arena",
        "8a7d0dceea76dfe6fd7bd7f3a6ea216f6347c6aa",
        "lka.py,schemas,tests,tutorial",
        "bca8d90d563dccae56111676d051f36e5bba3701d5445b9b56611ad96eae1262",
    ),
    (
        "lean4",
        "https://github.com/leanprover/lean4",
        LEAN_GITHASH,
        "tests/pkg/leanchecker",
        "e6e4b5d31e95dcf8cc4aefcf899eb943cd2d325ebba43f087941a7142276a126",
    ),
    (
        "nanoda",
        "https://github.com/ammkrn/nanoda_lib",
        "0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929",
        "test_resources",
        "4221408183f2a6a4c518f5dbe9aa9460e18e1463e532aa7238860c27ef739f6e",
    ),
];

/// The Python packages lka.py needs are resolved as of this date.
pub const UV_ENV: [(&str, &str); 2] = [
    ("UV_EXCLUDE_NEWER", "2026-11-24T00:00:00Z"),
    ("UV_PYTHON", "3.12"),
];

const FC: &str = "fetch-corpus";

pub fn fetch_main(a: FetchArgs) -> Result<()> {
    fetch_corpus(a).map_err(|e| {
        let msg = format!("{e:#}");
        if msg.starts_with("fetch-corpus: ") {
            e
        } else {
            anyhow!("fetch-corpus: error: {msg}")
        }
    })
}

/// Checks out `paths` of the repository at `commit` into `dir` and checks
/// their contents (sparse, blobs fetched on demand).
pub fn fetch_source(
    tool: &str,
    dir: &Path,
    (name, url, commit, paths, want): (&str, &str, &str, &str, &str),
    update: bool,
) -> Result<()> {
    let plist: Vec<&str> = paths.split(',').collect();
    if !dir.join(".git").is_dir() {
        if dir.exists() {
            fs::remove_dir_all(dir)?;
        }
        run(Command::new("git").args(["init", "-q"]).arg(dir))?;
        run(git(dir).args(["remote", "add", "origin", url]))?;
    }
    let have = git(dir)
        .args(["cat-file", "-e", &format!("{commit}^{{commit}}")])
        .stderr(Stdio::null())
        .status()?;
    if !have.success() {
        log(tool, &format!("fetching {name} at {commit}"));
        run(git(dir).args([
            "fetch",
            "-q",
            "--depth",
            "1",
            "--filter=blob:none",
            "origin",
            commit,
        ]))?;
    }
    run(git(dir)
        .args(["sparse-checkout", "set", "--no-cone"])
        .args(&plist)
        .stderr(Stdio::null()))?;
    run(git(dir).args([
        "-c",
        "advice.detachedHead=false",
        "checkout",
        "-q",
        "--force",
        commit,
    ]))?;
    run(git(dir).args(["clean", "-qfdx"]))?;
    let head = util::output(git(dir).args(["rev-parse", "HEAD"]))?;
    if head.trim() != commit {
        bail!("{tool}: error: {name}: not at {commit}");
    }
    let got = util::content_sha256(dir, &plist, &[])?;
    if got != want {
        if update {
            log(
                tool,
                &format!("{name}: content SHA-256 is {got} (pinned: {want})"),
            );
        } else {
            bail!("{tool}: error: {name}: content SHA-256 is {got}, expected {want}");
        }
    }
    Ok(())
}

/// Installs the pinned toolchain and checks it is the pinned commit.
pub fn install_pinned_lean(tool: &str) -> Result<()> {
    log(tool, &format!("installing {LEAN_TOOLCHAIN}"));
    util::elan_install(LEAN_TOOLCHAIN, false)?;
    let v = util::output(Command::new("elan").args(["run", LEAN_TOOLCHAIN, "lean", "--version"]))?;
    let v = v.trim_end_matches('\n');
    if !v.contains(&format!("commit {LEAN_GITHASH}")) {
        bail!("{tool}: error: unexpected Lean: {v}");
    }
    Ok(())
}

fn fetch_corpus(a: FetchArgs) -> Result<()> {
    let root = root();
    let out = abs_dir(&a.out.unwrap_or_else(|| root.join("corpus/exports")))?;
    let cache = abs_dir(&a.cache.unwrap_or_else(|| root.join("corpus/.cache")))?;
    need(
        FC,
        &["git", "curl", "elan", "uv"],
        " (`mise install` gives uv)",
    )?;

    install_pinned_lean(FC)?;
    for s in SOURCES {
        fetch_source(FC, &cache.join("src").join(s.0), s, a.update_checksums)?;
    }

    // The output directory holds nothing but generated files: start afresh.
    let entries: Vec<_> = fs::read_dir(&out)?.collect::<Result<_, _>>()?;
    if !entries.is_empty() && !out.join("manifest.tsv").is_file() {
        bail!(
            "{FC}: error: {} is not empty and has no manifest.tsv; refusing to clear it",
            out.display()
        );
    }
    for e in entries {
        let p = e.path();
        if e.file_type()?.is_dir() {
            fs::remove_dir_all(&p)?;
        } else {
            fs::remove_file(&p)?;
        }
    }
    let mut manifest: Vec<String> = Vec::new();
    let work = abs_dir(&cache.join("work"))?;

    // Lean Kernel Arena: every test, built by the Arena's own tool.
    log(FC, "arena: building the tests");
    copy_tree(&cache.join("src/arena"), &work.join("arena"), true)?;
    let mut lka = util::cmd_in("uv", &work.join("arena"));
    lka.envs(UV_ENV)
        .args(["run", "--quiet", "lka.py", "build-test"]);
    if !a.full {
        lka.arg("--skip-ci");
    }
    let arena_log = work.join("arena.log");
    run_logged(
        &mut lka,
        &arena_log,
        40,
        &format!(
            "{FC}: error: arena: build-test failed (log: {})",
            arena_log.display()
        ),
    )?;
    manifest.extend(collect_arena(&work.join("arena/_build/tests"), &out)?);

    // Our own test files, written with the Arena's tutorial machinery
    // (`good_decl`, `bad_decl`, ...): each test case becomes one export.
    log(FC, "arena tutorial machinery: building");
    let tutorial = work.join("arena/tutorial");
    run_logged(
        util::cmd_in("lake", &tutorial).args(["build", "-q", "Tutorial.Meta"]),
        &work.join("tutorial-meta.log"),
        40,
        &format!("{FC}: error: building Tutorial.Meta failed"),
    )?;
    for (source, file) in [
        ("lean4lean", "Lean4LeanTests"),
        ("historical", "HistoricalBugs"),
    ] {
        let file = root.join("corpus/lean").join(format!("{file}.lean"));
        log(
            FC,
            &format!(
                "{source}: exporting {}",
                file.file_name().unwrap().to_string_lossy()
            ),
        );
        let dir = work.join(source);
        if dir.exists() {
            fs::remove_dir_all(&dir)?;
        }
        run_logged(
            util::cmd_in("lake", &tutorial)
                .env("OUT", &dir)
                .env("LEAN_ABORT_ON_PANIC", "1")
                .args(["env", "lean"])
                .arg(&file),
            &work.join(format!("{source}.log")),
            40,
            &format!("{FC}: error: {source}: exporting {} failed", file.display()),
        )?;
        manifest.extend(collect_cases(&dir, &out, source)?);
    }

    // Lean's leanchecker tests (tests/pkg/leanchecker): the modules that have
    // an `.export` file, exported as its run_test.sh does.
    log(FC, "leanchecker: building the test package");
    let lc = work.join("leanchecker");
    copy_tree(&cache.join("src/lean4/tests/pkg/leanchecker"), &lc, true)?;
    fs::write(lc.join("lean-toolchain"), format!("{LEAN_TOOLCHAIN}\n"))?;
    run_logged(
        util::cmd_in("lake", &lc).args(["build", "-q"]),
        &work.join("leanchecker.log"),
        40,
        &format!("{FC}: error: leanchecker: lake build failed"),
    )?;
    fs::create_dir_all(out.join("leanchecker"))?;
    let mut specs: Vec<String> = fs::read_dir(lc.join("LeanCheckerTests"))?
        .filter_map(|e| e.ok())
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .filter(|n| n.ends_with(".lean.export") && !n.starts_with('.'))
        .collect();
    specs.sort();
    for spec_name in specs {
        let spec = lc.join("LeanCheckerTests").join(&spec_name);
        let base = &spec_name[..spec_name.len() - ".lean.export".len()];
        let module = format!("LeanCheckerTests.{base}");
        let decls: Vec<String> = fs::read_to_string(&spec)?
            .lines()
            .map(str::to_string)
            .collect();
        let err_path = work.join(format!("leanchecker-{base}.err"));
        let st = util::cmd_in("lake", &lc)
            .args(["env", "leanexport", &module, "--"])
            .args(&decls)
            .stdout(fs::File::create(
                out.join(format!("leanchecker/{base}.ndjson")),
            )?)
            .stderr(fs::File::create(&err_path)?)
            .status()?;
        let err = fs::read(&err_path)?;
        if !st.success() || !err.is_empty() {
            std::io::stderr().write_all(&err)?;
            bail!("{FC}: error: leanchecker: leanexport {module} failed");
        }
        let expected_out = fs::read_to_string(
            lc.join("LeanCheckerTests")
                .join(format!("{spec_name}.out.expected")),
        )
        .unwrap_or_default();
        let expected = if expected_out.contains("accepts the solution") {
            "accept"
        } else {
            "reject"
        };
        manifest.push(format!(
            "leanchecker/{base}\tleanchecker\t{expected}\t\ttests/pkg/leanchecker/LeanCheckerTests/{base}.lean"
        ));
    }

    // nanoda_lib's test exports, as they are.
    fs::create_dir_all(out.join("nanoda"))?;
    for (base, verdict) in [("Empty", "accept"), ("ProjFromProp", "reject")] {
        fs::copy(
            cache.join(format!("src/nanoda/test_resources/{base}/export")),
            out.join(format!("nanoda/{base}.ndjson")),
        )?;
        manifest.push(format!(
            "nanoda/{base}\tnanoda\t{verdict}\t\ttest_resources/{base}/export"
        ));
    }

    manifest.sort();
    let mut text = String::from("id\tsource\texpected\ttimeout\torigin\n");
    for l in &manifest {
        text.push_str(l);
        text.push('\n');
    }
    fs::write(out.join("manifest.tsv"), text)?;

    let sums = root.join("corpus/exports.sha256");
    if a.update_checksums {
        fs::write(&sums, checksums(&out, None, false)?)?;
        log(FC, &format!("wrote {}", sums.display()));
    } else {
        checksums(&out, Some(&sums), a.full)?;
    }
    log(
        FC,
        &format!("{} exports in {}", manifest.len(), out.display()),
    );
    Ok(())
}

// ---------------------------------------------------------------------------
// cargo xtask lean-verdicts

/// Record Lean's own verdict on every export of the corpus, and derive
/// nitrolean's.
///
/// Runs `leanchecker --from-export` of the pinned Lean on every export in DIR
/// (default: corpus/exports, made by `cargo xtask fetch-corpus`) and writes
/// corpus/expected-lean-v4.36.0.tsv, then corpus/expected-nitrolean.tsv from
/// it and corpus/divergences.md.
#[derive(clap::Args)]
pub struct VerdictArgs {
    #[arg(long)]
    out: Option<PathBuf>,
    #[arg(long)]
    jobs: Option<usize>,
}

pub fn verdicts_main(a: VerdictArgs) -> Result<()> {
    let root = root();
    let out = a.out.unwrap_or_else(|| root.join("corpus/exports"));
    let lean_tsv = root.join("corpus/expected-lean-v4.36.0.tsv");
    lean_verdicts(
        &out,
        &lean_tsv,
        a.jobs.unwrap_or_else(util::nproc),
        LEAN_TOOLCHAIN,
    )?;
    expected_nitrolean(
        &lean_tsv,
        &root.join("corpus/divergences.md"),
        &root.join("corpus/expected-nitrolean.tsv"),
        false,
    )
}

/// Runs a command with its stdout and stderr captured, killing it after
/// `timeout`: exit code (negative for a signal), stdout, stderr, or `None`
/// on a timeout.
fn run_capture(cmd: &mut Command, timeout: Duration) -> Result<Option<(i32, String, String)>> {
    let mut child = cmd
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .with_context(|| format!("cannot run {}", util::describe(cmd)))?;
    let mut so = child.stdout.take().unwrap();
    let mut se = child.stderr.take().unwrap();
    let to = std::thread::spawn(move || {
        let mut b = Vec::new();
        let _ = so.read_to_end(&mut b);
        b
    });
    let te = std::thread::spawn(move || {
        let mut b = Vec::new();
        let _ = se.read_to_end(&mut b);
        b
    });
    let start = Instant::now();
    let status = loop {
        if let Some(st) = child.try_wait()? {
            break Some(st);
        }
        if start.elapsed() > timeout {
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        std::thread::sleep(Duration::from_millis(20));
    };
    let (o, e) = (to.join().unwrap_or_default(), te.join().unwrap_or_default());
    let Some(st) = status else { return Ok(None) };
    use std::os::unix::process::ExitStatusExt;
    let code = st.code().unwrap_or_else(|| -st.signal().unwrap_or(0));
    Ok(Some((
        code,
        String::from_utf8_lossy(&o).into_owned(),
        String::from_utf8_lossy(&e).into_owned(),
    )))
}

fn lean_verdict(export: &Path, toolchain: &str, timeout: i64) -> Result<(String, String)> {
    let r = run_capture(
        Command::new("elan")
            .args(["run", toolchain, "leanchecker", "--from-export"])
            .arg(export),
        Duration::from_secs(timeout as u64),
    )?;
    let Some((code, so, se)) = r else {
        return Ok(("timeout".into(), format!("no verdict within {timeout} s")));
    };
    let text = format!("{so}{se}");
    let text = text.trim();
    let lines: Vec<&str> = text.lines().collect();
    let first = lines.first().copied().unwrap_or("");
    if code == 0 && text.contains("accepts the solution") {
        return Ok(("accept".into(), String::new()));
    }
    if text.contains("rejects the solution") {
        // The first line names the declaration, the second the kernel's complaint.
        let mut parts = vec![
            first
                .split_once("rejects the solution:")
                .map(|(_, r)| r)
                .unwrap_or(first)
                .trim()
                .to_string(),
        ];
        parts.extend(lines.iter().skip(1).take(2).map(|l| l.trim().to_string()));
        return Ok(("reject".into(), truncate(&squash(&parts.join(" ")), 200)));
    }
    if code == 1 && text.contains("uncaught exception") {
        // leanchecker refuses the export before it gets to the kernel, e.g. on
        // a duplicate declaration: a rejection all the same.
        return Ok(("reject".into(), truncate(&squash(first), 200)));
    }
    Ok((
        "error".into(),
        truncate(&squash(&format!("exit {code}: {first}")), 200),
    ))
}

fn lean_verdicts(out: &Path, tsv: &Path, jobs: usize, toolchain: &str) -> Result<()> {
    let rows = read_tsv(&out.join("manifest.tsv"))?;
    let mut verdicts: Vec<Result<(String, String)>> = Vec::new();
    util::par_map_ordered(
        rows.clone(),
        jobs,
        |row| {
            let t = cell(&row, "timeout");
            let t: i64 = if t.is_empty() {
                DEFAULT_TIMEOUT
            } else {
                t.parse().with_context(|| format!("bad timeout {t}"))?
            };
            let timeout = (t * 3).max(DEFAULT_TIMEOUT);
            lean_verdict(
                &out.join(format!("{}.ndjson", cell(&row, "id"))),
                toolchain,
                timeout,
            )
        },
        |r| verdicts.push(r),
    );
    let verdicts: Vec<(String, String)> = verdicts.into_iter().collect::<Result<_>>()?;
    let mut lines = vec!["test_id\tsource\texpected\tlean\tnote".to_string()];
    for (row, (verdict, note)) in rows.iter().zip(&verdicts) {
        let expected = cell(row, "expected");
        let mut note = note.clone();
        let decided = |v: &str| v == "accept" || v == "reject";
        if decided(verdict) && decided(expected) && verdict != expected {
            note = format!("Lean {verdict}s, upstream expects {expected}")
                + &(if note.is_empty() {
                    String::new()
                } else {
                    format!("; {note}")
                });
        }
        lines.push(
            [
                cell(row, "id"),
                cell(row, "source"),
                expected,
                verdict,
                &squash(&note),
            ]
            .join("\t"),
        );
    }
    fs::write(tsv, lines.join("\n") + "\n")?;
    let mut counts: Vec<(String, usize)> = Vec::new();
    for (v, _) in &verdicts {
        match counts.iter_mut().find(|(k, _)| k == v) {
            Some(c) => c.1 += 1,
            None => counts.push((v.clone(), 1)),
        }
    }
    let counts = counts
        .iter()
        .map(|(k, n)| format!("'{k}': {n}"))
        .collect::<Vec<_>>()
        .join(", ");
    eprintln!(
        "lean-verdicts: wrote {} ({} tests: {{{counts}}})",
        tsv.display(),
        rows.len()
    );
    Ok(())
}

/// Derives nitrolean's intended verdicts from Lean's and the divergence list,
/// writing them to `out_tsv` or, with `check`, checking that it holds them.
pub fn expected_nitrolean(
    lean_tsv: &Path,
    divergences: &Path,
    out_tsv: &Path,
    check: bool,
) -> Result<()> {
    let rows = read_tsv(lean_tsv)?;
    let ids: std::collections::HashSet<&str> = rows.iter().map(|r| cell(r, "test_id")).collect();
    let re = Regex::new(r"^\|\s*`([^`]+)`\s*\|\s*(accept|reject)\s*\|").unwrap();
    let mut overrides: HashMap<String, String> = HashMap::new();
    for line in fs::read_to_string(divergences)
        .with_context(|| format!("{}: cannot read", divergences.display()))?
        .lines()
    {
        if let Some(m) = re.captures(line) {
            overrides.insert(m[1].to_string(), m[2].to_string());
        }
    }
    let mut unknown: Vec<&str> = overrides
        .keys()
        .map(String::as_str)
        .filter(|k| !ids.contains(k))
        .collect();
    unknown.sort();
    if !unknown.is_empty() {
        bail!(
            "expected-nitrolean: divergences for unknown tests: {}",
            unknown.join(", ")
        );
    }
    let mut lines = vec!["test_id\tverdict\tbasis".to_string()];
    for r in &rows {
        let tid = cell(r, "test_id");
        let lean = cell(r, "lean");
        let (verdict, basis) = if let Some(v) = overrides.get(tid) {
            if v == lean {
                bail!("expected-nitrolean: {tid} is listed as a divergence but Lean agrees");
            }
            (v.as_str(), "divergence (corpus/divergences.md)")
        } else if lean == "accept" || lean == "reject" {
            (lean, "Lean v4.36.0")
        } else {
            bail!("expected-nitrolean: {tid}: no Lean verdict ({lean}) and no divergence entry");
        };
        lines.push([tid, verdict, basis].join("\t"));
    }
    let text = lines.join("\n") + "\n";
    if check {
        if fs::read_to_string(out_tsv).ok().as_deref() != Some(&text) {
            bail!(
                "expected-nitrolean: {} is out of date; run cargo xtask lean-verdicts",
                out_tsv.display()
            );
        }
        eprintln!(
            "expected-nitrolean: {} is up to date",
            out_tsv.file_name().unwrap_or_default().to_string_lossy()
        );
    } else {
        fs::write(out_tsv, text)?;
        eprintln!(
            "expected-nitrolean: wrote {} ({} divergences)",
            out_tsv.display(),
            overrides.len()
        );
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// cargo xtask olean-equivalence

/// Check that nitrolean's .olean reader builds the same environment as Lean's
/// NDJSON exporter: every exported declaration must be in the oleans with a
/// structurally identical type, value and other fields.
///
/// WORKDIR (default: a new temporary directory) holds the export and, for
/// Mathlib, a Mathlib checkout with its cached build. Needs elan, git and
/// curl; the Mathlib export takes about 15 GB of memory and 10 GB of disk.
#[derive(clap::Args)]
pub struct OleanArgs {
    /// Init, Std, Lean or Mathlib
    module: String,
    workdir: Option<PathBuf>,
}

pub fn olean_main(a: OleanArgs) -> Result<()> {
    const MATHLIB_TAG: &str = "v4.36.0";
    const MATHLIB_COMMIT: &str = "fc4f59e577feb1a4956671bc04ac18aaaf8cd842";
    let repo = root();
    let work = match a.workdir {
        Some(w) => abs_dir(&w)?,
        None => abs_dir(&temp_path("olean-equivalence-", ""))?,
    };
    run(Command::new("elan")
        .args(["toolchain", "install", LEAN_TOOLCHAIN])
        .stdout(Stdio::null()))?;
    let prefix = util::lean_prefix(LEAN_TOOLCHAIN)?;
    let path = util::path_with(&prefix.join("bin"));

    run(util::cmd_in("cargo", &repo).args(["build", "--release", "--quiet"]))?;
    let nitrolean = repo.join("target/release/nitrolean");
    let timefmt = "%e s, peak RSS %M KB";

    let (export_cmd, target, run_dir): (Vec<String>, String, PathBuf) = match a.module.as_str() {
        "Mathlib" => {
            let m = work.join("mathlib4");
            if !m.is_dir() {
                run(Command::new("git")
                    .args([
                        "-c",
                        "advice.detachedHead=false",
                        "clone",
                        "--quiet",
                        "--depth",
                        "1",
                        "--branch",
                        MATHLIB_TAG,
                        "https://github.com/leanprover-community/mathlib4",
                    ])
                    .arg(&m))?;
            }
            let got = util::output(git(&m).args(["rev-parse", "HEAD"]))?;
            if got.trim() != MATHLIB_COMMIT {
                return Err(exit_with(
                    2,
                    format!(
                        "mathlib4 {MATHLIB_TAG} is at {}, expected {MATHLIB_COMMIT}",
                        got.trim()
                    ),
                ));
            }
            run(util::cmd_in("lake", &m)
                .env("PATH", &path)
                .args(["exe", "cache", "get"])
                .stdout(Stdio::null()))?;
            (
                ["lake", "env", "leanexport", "Mathlib"]
                    .map(String::from)
                    .to_vec(),
                m.to_string_lossy().into_owned(),
                m,
            )
        }
        "Init" | "Std" | "Lean" => (
            vec!["leanexport".into(), a.module.clone()],
            a.module.clone(),
            work.clone(),
        ),
        m => {
            return Err(exit_with(
                2,
                format!("unknown module {m} (Init, Std, Lean or Mathlib)"),
            ));
        }
    };

    let out = work.join(format!("{}.ndjson", a.module));
    if fs::metadata(&out).map(|m| m.len()).unwrap_or(0) == 0 {
        println!("exporting {}", a.module);
        let tmp = work.join(format!("{}.ndjson.tmp", a.module));
        let st = util::cmd_in("/usr/bin/time", &run_dir)
            .env("PATH", &path)
            .args(["-f", &format!("export: {timefmt}")])
            .args(&export_cmd)
            .stdout(fs::File::create(&tmp)?)
            .status()?;
        if !st.success() {
            return Err(exit_with(st.code().unwrap_or(1), ""));
        }
        fs::rename(&tmp, &out)?;
    }
    std::io::stdout().flush()?;
    run(Command::new("ls").arg("-l").arg(&out))?;
    println!("comparing");
    std::io::stdout().flush()?;
    let st = util::cmd_in("/usr/bin/time", &run_dir)
        .env("PATH", &path)
        .args(["-f", &format!("compare: {timefmt}")])
        .arg(&nitrolean)
        .arg("compare")
        .arg(&out)
        .arg(&target)
        .status()?;
    if !st.success() {
        return Err(exit_with(st.code().unwrap_or(1), ""));
    }
    Ok(())
}
