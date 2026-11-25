//! `cargo xtask arena ...`: the Lean Kernel Arena benchmark (bench/arena).
//!
//!   fetch     build the arena's test set at its pinned versions
//!   run       run checkers on it, the way the arena does, appending to a TSV
//!   report    print a Markdown table of results
//!   pin       rewrite tests.tsv and published.tsv from the arena's results.json
//!   collect   move the exports `lka.py build-test` wrote into OUT/<test>.ndjson
//!   verify    check every export against the arena's SHA-256 and write SHA256SUMS
//!
//! See bench/arena/README.md.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Duration;

use anyhow::{Context, Result};
use clap::{Args, Subcommand};
use serde_json::Value;

use crate::proc::{gnu_time, run_timed};
use crate::util::{
    cell, content_sha256, copy_into, elan_install, exit_with, fmt_g, glob_match, log, parse_tsv,
    print_tail, read_tsv, root, sha256_file, which,
};

const COLUMNS: [&str; 13] = [
    "checker",
    "test",
    "group",
    "expected",
    "status",
    "correctness",
    "exit_code",
    "wall_s",
    "cpu_s",
    "max_rss_mib",
    "ginstructions",
    "timeout_s",
    "note",
];
const COMPETITORS: [&str; 3] = ["official", "gruszka", "nano-lean"];
const OFFICIAL_TOOLCHAIN: &str = "leanprover--lean4---v4.35.0";

const TEST_COLUMNS: [&str; 12] = [
    "test",
    "group",
    "expected",
    "timeout",
    "compare_perf",
    "skip_on_ci",
    "lean_version",
    "export_format",
    "lines",
    "bytes",
    "sha256",
    "yaml",
];
const PUBLISHED_CHECKERS: [&str; 3] = ["official", "gruszka", "nano-lean"];
const PUBLISHED_COLUMNS: [&str; 10] = [
    "checker",
    "version",
    "test",
    "status",
    "correctness",
    "wall_s",
    "cpu_s",
    "max_rss_bytes",
    "ginstructions",
    "date",
];

// Pins of `fetch`.
const ARENA_URL: &str = "https://github.com/leanprover/lean-kernel-arena";
const ARENA_COMMIT: &str = "8a7d0dceea76dfe6fd7bd7f3a6ea216f6347c6aa";
/// SHA-256 over these paths at ARENA_COMMIT (see `util::content_sha256`).
const ARENA_PATHS: [&str; 4] = ["lka.py", "schemas", "tests", "tutorial"];
const ARENA_SHA256: &str = "bca8d90d563dccae56111676d051f36e5bba3701d5445b9b56611ad96eae1262";
/// The toolchain of the arena's tests/lean-toolchain; its bundled
/// `leanexport` writes the exports.
const LEAN_TOOLCHAIN: &str = "leanprover/lean4:v4.36.0";
const LEAN_GITHASH: &str = "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9";
/// The Python packages lka.py needs, as resolved on this date.
const UV_EXCLUDE_NEWER: &str = "2026-11-24T00:00:00Z";
const UV_PYTHON: &str = "3.12";

fn here() -> PathBuf {
    root().join("bench/arena")
}

#[derive(Subcommand)]
pub enum Cmd {
    /// Build the arena's test set at the arena's pinned versions.
    Fetch(FetchArgs),
    /// Run checkers on every export, appending rows to a TSV.
    Run(RunArgs),
    /// Print a Markdown table of results.
    Report(ReportArgs),
    /// Rewrite tests.tsv and published.tsv from the arena's results.json.
    Pin { results_json: PathBuf },
    /// Move the exports `lka.py build-test` wrote under BUILD_DIR into OUT/<test>.ndjson.
    Collect { build_dir: PathBuf, out: PathBuf },
    /// Check every export in OUT against the arena's SHA-256 and write OUT/SHA256SUMS.
    Verify { out: PathBuf },
}

pub fn main(c: Cmd) -> Result<()> {
    match c {
        Cmd::Fetch(a) => cmd_fetch(a),
        Cmd::Run(a) => cmd_run(a),
        Cmd::Report(a) => cmd_report(a),
        Cmd::Pin { results_json } => cmd_pin(&results_json),
        Cmd::Collect { build_dir, out } => cmd_collect(&build_dir, &out),
        Cmd::Verify { out } => cmd_verify(&out),
    }
}

// ---------------------------------------------------------------------------
// fetch

/// Fetches the arena at its pinned commit, checks the SHA-256 of its sources,
/// installs the Lean toolchain the arena exports with and builds the exports
/// with the arena's own `lka.py build-test`. Every export is then checked
/// against the SHA-256 the arena published for it (tests.tsv), and the
/// SHA-256s of everything built are written to OUT/SHA256SUMS.
#[derive(Args)]
pub struct FetchArgs {
    /// Where the exports go [default: bench/arena/data/exports]
    #[arg(long)]
    out: Option<PathBuf>,
    /// Sources, build directories and lka.py's export cache [default: bench/arena/data/cache]
    #[arg(long)]
    cache: Option<PathBuf>,
    /// The tests the arena builds on CI (no `skip-on-ci`); the default.
    #[arg(long, conflicts_with_all = ["large", "all"])]
    small: bool,
    /// Only the large real-world tests (`skip-on-ci`). Mathlib alone needs
    /// ~25 GB of disk and ~16 GB of RAM to export.
    #[arg(long, conflicts_with = "all")]
    large: bool,
    /// Every test.
    #[arg(long)]
    all: bool,
    /// Keep the projects lka.py built (by default they are removed after
    /// their exports are collected, to save disk).
    #[arg(long)]
    keep_work: bool,
    /// Let lka.py keep a copy of each export of a pinned project in DIR and
    /// reuse it next time (costs as much disk again).
    #[arg(long, value_name = "DIR")]
    export_cache: Option<PathBuf>,
    /// Only tests whose name matches (lka.py's own patterns, e.g. 'perf/*' or
    /// std); combined with --small/--large as a filter.
    #[arg(value_name = "TEST-GLOB")]
    patterns: Vec<String>,
}

fn die(msg: impl std::fmt::Display) -> anyhow::Error {
    exit_with(1, format!("fetch: error: {msg}"))
}

fn git_in(dir: &Path) -> Command {
    let mut c = Command::new("git");
    c.arg("-C").arg(dir);
    c
}

fn ok(c: &mut Command) -> Result<()> {
    crate::util::run(c)
}

fn cmd_fetch(a: FetchArgs) -> Result<()> {
    let here = here();
    let select = if a.large {
        "large"
    } else if a.all {
        "all"
    } else {
        "small"
    };
    for tool in ["git", "curl", "elan", "uv"] {
        if which(tool).is_none() {
            return Err(die(format!("{tool} not found")));
        }
    }
    let out = crate::util::abs_dir(&a.out.unwrap_or_else(|| here.join("data/exports")))?;
    let cache = crate::util::abs_dir(&a.cache.unwrap_or_else(|| here.join("data/cache")))?;

    // The arena at its pinned commit.
    let src = cache.join("arena-src");
    if !src.join(".git").is_dir() {
        if src.exists() {
            fs::remove_dir_all(&src)?;
        }
        ok(Command::new("git").args(["init", "-q"]).arg(&src))?;
        ok(git_in(&src).args(["remote", "add", "origin", ARENA_URL]))?;
    }
    let have = git_in(&src)
        .args(["cat-file", "-e", &format!("{ARENA_COMMIT}^{{commit}}")])
        .stderr(Stdio::null())
        .status()?;
    if !have.success() {
        log("fetch", &format!("fetching the arena at {ARENA_COMMIT}"));
        ok(git_in(&src).args(["fetch", "-q", "--depth", "1", "origin", ARENA_COMMIT]))?;
    }
    ok(git_in(&src).args([
        "-c",
        "advice.detachedHead=false",
        "checkout",
        "-q",
        "--force",
        ARENA_COMMIT,
    ]))?;
    ok(git_in(&src).args(["clean", "-qfdx"]))?;
    let got = content_sha256(&src, &ARENA_PATHS, &[])?;
    if got != ARENA_SHA256 {
        return Err(die(format!(
            "arena sources: SHA-256 {got}, expected {ARENA_SHA256}"
        )));
    }

    // Lean.
    log("fetch", &format!("installing {LEAN_TOOLCHAIN}"));
    elan_install(LEAN_TOOLCHAIN, false)?;
    let version = crate::util::output(Command::new("elan").args([
        "run",
        LEAN_TOOLCHAIN,
        "lean",
        "--version",
    ]))?;
    let version = version.trim_end_matches('\n');
    if !version.contains(&format!("commit {LEAN_GITHASH}")) {
        return Err(die(format!("unexpected Lean: {version}")));
    }

    // A working copy of the arena: lka.py writes its exports to _build/tests.
    let work = cache.join("arena");
    let tests_dir = work.join("_build/tests");
    if tests_dir.exists() {
        fs::remove_dir_all(&tests_dir)?;
    }
    copy_into(&src, &work, true)?;

    let mut args: Vec<String> = vec!["build-test".into()];
    if let Some(ec) = &a.export_cache {
        args.push("--cache".into());
        args.push(ec.to_string_lossy().into_owned());
    }
    let mut patterns = a.patterns;
    match select {
        "small" => args.push("--skip-ci".into()),
        "large" => {
            let large: Vec<String> = read_tsv(&here.join("tests.tsv"))?
                .iter()
                .filter(|t| cell(t, "skip_on_ci") == "yes")
                .map(|t| cell(t, "test").to_string())
                .collect();
            if patterns.is_empty() {
                patterns = large;
            } else {
                let sel: Vec<String> = large
                    .into_iter()
                    .filter(|t| patterns.iter().any(|p| glob_match(p, t)))
                    .collect();
                if sel.is_empty() {
                    return Err(die("no large test matches"));
                }
                patterns = sel;
            }
        }
        _ => {}
    }
    args.extend(patterns);

    // lka.py runs each test's pre-build with /bin/sh; the arena's is bash (in
    // its nix shell), and cedar's pre-build uses `shopt`. Elsewhere it fails.
    if select != "small" {
        let bash = Command::new("/bin/sh")
            .args(["-c", "shopt -s dotglob"])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status();
        if !matches!(bash, Ok(s) if s.success()) {
            log(
                "fetch",
                "warning: /bin/sh is not bash; cedar's pre-build will fail (see README)",
            );
        }
    }

    log("fetch", &format!("building: lka.py {}", args.join(" ")));
    let log_file = cache.join("build-test.log");
    let f = fs::File::create(&log_file)?;
    let st = Command::new("uv")
        .args(["run", "--quiet", "lka.py"])
        .args(&args)
        .current_dir(&work)
        .env("UV_EXCLUDE_NEWER", UV_EXCLUDE_NEWER)
        .env("UV_PYTHON", UV_PYTHON)
        .stdout(f.try_clone()?)
        .stderr(f)
        .status()
        .context("cannot run uv")?;
    if !st.success() {
        print_tail(&log_file, 40);
        return Err(die(format!(
            "lka.py build-test failed (log: {})",
            log_file.display()
        )));
    }

    cmd_collect(&tests_dir, &out)?;
    if !a.keep_work && tests_dir.join("work").exists() {
        fs::remove_dir_all(tests_dir.join("work"))?;
    }
    cmd_verify(&out)?;
    log(
        "fetch",
        &format!(
            "exports in {}, their SHA-256s in {}/SHA256SUMS",
            out.display(),
            out.display()
        ),
    );
    Ok(())
}

// ---------------------------------------------------------------------------
// pin, collect, verify

/// Every file under `dir` whose name ends in `suffix`, as paths relative to
/// `dir`, sorted by their components (as Python sorts paths). Symbolic links
/// to directories are not followed.
fn rglob(dir: &Path, suffix: &str) -> Result<Vec<PathBuf>> {
    fn walk(dir: &Path, rel: &Path, suffix: &str, out: &mut Vec<PathBuf>) -> Result<()> {
        let Ok(rd) = fs::read_dir(dir.join(rel)) else {
            return Ok(());
        };
        for e in rd {
            let e = e?;
            let r = rel.join(e.file_name());
            let ft = e.file_type()?;
            if ft.is_dir() {
                walk(dir, &r, suffix, out)?;
            } else if e.file_name().to_string_lossy().ends_with(suffix) {
                out.push(r);
            }
        }
        Ok(())
    }
    let mut out = Vec::new();
    walk(dir, Path::new(""), suffix, &mut out)?;
    out.sort_by(|a, b| a.components().cmp(b.components()));
    Ok(out)
}

fn posix(p: &Path) -> String {
    p.components()
        .map(|c| c.as_os_str().to_string_lossy().into_owned())
        .collect::<Vec<_>>()
        .join("/")
}

fn group_of(name: &str) -> &str {
    match name.split_once('/') {
        Some((g, _)) => g,
        None => "real-world",
    }
}

/// Python's `str()` of a JSON value.
fn py_str(v: &Value) -> String {
    match v {
        Value::Null => "None".into(),
        Value::Bool(b) => if *b { "True" } else { "False" }.into(),
        Value::String(s) => s.clone(),
        Value::Number(n) => {
            if n.is_f64() {
                py_float(n.as_f64().unwrap_or(0.0))
            } else {
                n.to_string()
            }
        }
        Value::Array(a) => format!("[{}]", a.iter().map(py_repr).collect::<Vec<_>>().join(", ")),
        Value::Object(o) => format!(
            "{{{}}}",
            o.iter()
                .map(|(k, v)| format!("{}: {}", py_repr(&Value::String(k.clone())), py_repr(v)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

fn py_repr(v: &Value) -> String {
    match v {
        Value::String(s) => format!("'{}'", s.replace('\\', "\\\\").replace('\'', "\\'")),
        _ => py_str(v),
    }
}

/// Python's `repr()` of a float.
fn py_float(x: f64) -> String {
    if x.is_nan() {
        return "nan".into();
    }
    if x.is_infinite() {
        return if x > 0.0 { "inf" } else { "-inf" }.into();
    }
    if x == 0.0 {
        return if x.is_sign_negative() { "-0.0" } else { "0.0" }.into();
    }
    let e = format!("{x:e}");
    let (mant, exp) = e.split_once('e').unwrap_or((&e, "0"));
    let exp: i32 = exp.parse().unwrap_or(0);
    if (-4..16).contains(&exp) {
        let s = format!("{x}");
        if s.contains('.') { s } else { format!("{s}.0") }
    } else {
        let sign = if exp < 0 { '-' } else { '+' };
        format!("{mant}e{sign}{:02}", exp.abs())
    }
}

/// Python's truthiness of a JSON value.
fn truthy(v: Option<&Value>) -> bool {
    match v {
        None | Some(Value::Null) => false,
        Some(Value::Bool(b)) => *b,
        Some(Value::Number(n)) => n.as_f64() != Some(0.0),
        Some(Value::String(s)) => !s.is_empty(),
        Some(Value::Array(a)) => !a.is_empty(),
        Some(Value::Object(o)) => !o.is_empty(),
    }
}

fn num(v: &Value, what: &str) -> Result<f64> {
    v.as_f64()
        .with_context(|| format!("pin: {what} is not a number"))
}

fn write_tsv(path: &Path, columns: &[&str], rows: &[BTreeMap<&str, String>]) -> Result<()> {
    let mut s = columns.join("\t") + "\n";
    for r in rows {
        let cells: Vec<String> = columns
            .iter()
            .map(|c| crate::util::squash(r.get(c).map(String::as_str).unwrap_or("")))
            .collect();
        s.push_str(&cells.join("\t"));
        s.push('\n');
    }
    fs::write(path, s).with_context(|| format!("{}: cannot write", path.display()))
}

fn cmd_pin(results_json: &Path) -> Result<()> {
    let here = here();
    let text = fs::read_to_string(results_json)
        .with_context(|| format!("{}: cannot read", results_json.display()))?;
    let data: Value = serde_json::from_str(&text)?;
    eprintln!(
        "results.json of arena commit {}, sha256 {}",
        py_str(&data["meta"]["git_revision"]),
        sha256_file(results_json)?
    );
    let get = |o: &Value, k: &str| -> String { o.get(k).map(py_str).unwrap_or_default() };
    let mut tests: Vec<&Value> = data["tests"]
        .as_array()
        .context("pin: no tests")?
        .iter()
        .collect();
    tests.sort_by_key(|t| t["name"].as_str().unwrap_or("").to_string());
    let mut rows = Vec::new();
    for t in tests {
        let name = py_str(&t["name"]);
        let mut r = BTreeMap::new();
        r.insert("group", group_of(&name).to_string());
        r.insert("test", name);
        r.insert("expected", py_str(&t["outcome"]));
        r.insert("timeout", get(t, "timeout"));
        r.insert(
            "compare_perf",
            if truthy(t.get("compare-perf")) {
                "yes"
            } else {
                ""
            }
            .into(),
        );
        r.insert(
            "skip_on_ci",
            if truthy(t.get("skip-on-ci")) {
                "yes"
            } else {
                ""
            }
            .into(),
        );
        r.insert("lean_version", get(t, "lean_version"));
        r.insert("export_format", get(t, "lean4export_version"));
        r.insert("lines", py_str(&t["lines"]));
        r.insert("bytes", py_str(&t["size"]));
        r.insert("sha256", py_str(&t["sha256"]));
        r.insert("yaml", get(t, "yaml_file"));
        rows.push(r);
    }
    write_tsv(&here.join("tests.tsv"), &TEST_COLUMNS, &rows)?;
    let mut versions = HashMap::new();
    for c in data["checkers"].as_array().context("pin: no checkers")? {
        let v = if truthy(c.get("version")) {
            py_str(&c["version"])
        } else if truthy(c.get("rev")) {
            py_str(&c["rev"]).chars().take(12).collect()
        } else {
            String::new()
        };
        versions.insert(py_str(&c["name"]), v);
    }
    let mut results: Vec<&Value> = data["results"]
        .as_array()
        .context("pin: no results")?
        .iter()
        .collect();
    results.sort_by_key(|r| (py_str(&r["checker"]), py_str(&r["test"])));
    let mut published = Vec::new();
    for r in results {
        let checker = py_str(&r["checker"]);
        if !PUBLISHED_CHECKERS.contains(&checker.as_str()) {
            continue;
        }
        let instructions = match r.get("instructions") {
            Some(v) if truthy(Some(v)) => num(v, "instructions")?,
            _ => 0.0,
        };
        let max_rss = match &r["max_rss"] {
            Value::Number(n) if n.is_f64() => format!("{}", n.as_f64().unwrap_or(0.0).trunc()),
            v => py_str(v),
        };
        let mut p = BTreeMap::new();
        p.insert(
            "version",
            versions.get(&checker).cloned().unwrap_or_default(),
        );
        p.insert("checker", checker);
        p.insert("test", py_str(&r["test"]));
        p.insert("status", py_str(&r["status"]));
        p.insert("correctness", py_str(&r["correctness"]));
        p.insert(
            "wall_s",
            format!("{:.3}", num(&r["wall_time"], "wall_time")?),
        );
        p.insert("cpu_s", format!("{:.3}", num(&r["cpu_time"], "cpu_time")?));
        p.insert("max_rss_bytes", max_rss);
        p.insert("ginstructions", format!("{:.3}", instructions / 1e9));
        p.insert("date", get(r, "date"));
        published.push(p);
    }
    write_tsv(&here.join("published.tsv"), &PUBLISHED_COLUMNS, &published)?;
    eprintln!(
        "wrote {} tests and {} published results",
        rows.len(),
        published.len()
    );
    Ok(())
}

/// Moves every export with a .stats.json next to it (as lka.py writes them,
/// including the generated tutorial tests) to OUT/<test name>.ndjson.
fn cmd_collect(build_dir: &Path, out: &Path) -> Result<()> {
    let mut n = 0;
    for rel in rglob(build_dir, ".stats.json")? {
        if rel
            .components()
            .next()
            .is_some_and(|c| c.as_os_str() == "work")
        {
            continue;
        }
        let stats_file = build_dir.join(&rel);
        let stats: Value = serde_json::from_str(&fs::read_to_string(&stats_file)?)
            .with_context(|| format!("{}: bad JSON", stats_file.display()))?;
        let fname = stats_file.file_name().unwrap().to_string_lossy();
        let export = stats_file.with_file_name(format!("{}.ndjson", &fname[..fname.len() - 11]));
        if !export.exists() {
            continue;
        }
        let dest = out.join(format!("{}.ndjson", py_str(&stats["name"])));
        if let Some(d) = dest.parent() {
            fs::create_dir_all(d)?;
        }
        if fs::symlink_metadata(&dest).is_ok() {
            fs::remove_file(&dest)?;
        }
        if fs::rename(&export, &dest).is_err() {
            fs::copy(&export, &dest)?;
            fs::remove_file(&export)?;
        }
        n += 1;
    }
    eprintln!("collected {n} exports into {}", out.display());
    Ok(())
}

fn cmd_verify(out: &Path) -> Result<()> {
    let pinned: HashMap<String, HashMap<String, String>> = read_tsv(&here().join("tests.tsv"))?
        .into_iter()
        .map(|t| (cell(&t, "test").to_string(), t))
        .collect();
    let mut bad = 0;
    let mut sums = Vec::new();
    let mut built = HashSet::new();
    for rel in rglob(out, ".ndjson")? {
        let p = posix(&rel);
        let name = p[..p.len() - 7].to_string();
        let digest = sha256_file(&out.join(&rel))?;
        sums.push(format!("{digest}  {name}.ndjson"));
        match pinned.get(&name) {
            None => {
                eprintln!("verify: {name}: not an arena test");
                bad += 1;
            }
            Some(t) if digest != cell(t, "sha256") => {
                eprintln!(
                    "verify: {name}: sha256 {digest}, the arena's is {}",
                    cell(t, "sha256")
                );
                bad += 1;
            }
            _ => {}
        }
        built.insert(name);
    }
    fs::write(out.join("SHA256SUMS"), sums.join("\n") + "\n")?;
    let missing = pinned.keys().filter(|k| !built.contains(*k)).count();
    eprintln!(
        "verify: {} of {} exports identical to the arena's; {missing} arena tests not built here",
        sums.len() - bad,
        sums.len()
    );
    if bad > 0 {
        return Err(exit_with(1, ""));
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// run

/// Runs checkers on the arena's test set, the way the arena does.
///
/// The arena calls a checker as a shell command (`sh -c CMD`) with the
/// export's path in $IN, and reads its verdict from the exit code alone: 0
/// accepted, 1 rejected, 2 declined, anything else an error; past the test's
/// timeout it is killed and the run counts as a timeout (scored like an
/// error). A verdict is correct when it matches the test's expected outcome
/// (`accept` or `reject`); tests whose outcome is `either` accept both
/// verdicts. This runner does the same, and measures each run as the arena
/// does with GNU time: wall time, CPU time (user + system, of the command and
/// every child it waited for) and peak resident memory, all from wait4(2).
///
/// Checkers (`--checker NAME`, repeatable; default: nitrolean):
///
///   nitrolean   nitrolean check "$IN" (--nitrolean PATH; default
///               target/release/nitrolean, else `nitrolean` on PATH)
///   official    leanchecker --from-export "$IN", Lean's own checker; the
///               arena uses Lean v4.35.0's ($LEANCHECKER, else that
///               toolchain's from elan, else `leanchecker` on PATH)
///   gruszka     scripts/arena-run "$IN" 4, in a built checkout ($GRUSZKA_DIR)
///   nano-lean   target/release/nl-fast -q -j 4 "$IN", in a built checkout
///               ($NANO_LEAN_DIR), else `nl-fast` on PATH
///   NAME=CMD    any other command, run with $IN set
///
/// --competitors adds official, gruszka and nano-lean where they are
/// installed and skips the others with a note.
#[derive(Args)]
#[command(verbatim_doc_comment)]
pub struct RunArgs {
    /// The exports [default: bench/arena/data/exports]
    #[arg(long)]
    exports: Option<PathBuf>,
    /// The tests [default: bench/arena/tests.tsv]
    #[arg(long)]
    tests: Option<PathBuf>,
    /// TSV to append to; pairs already in it are skipped [default: bench/arena/results/results.tsv]
    #[arg(long)]
    out: Option<PathBuf>,
    /// nitrolean, official, gruszka, nano-lean or NAME=CMD
    #[arg(long)]
    checker: Vec<String>,
    /// Also run the installed competitors.
    #[arg(long)]
    competitors: bool,
    /// Path of the nitrolean binary.
    #[arg(long)]
    nitrolean: Option<String>,
    /// Only tests matching this glob (repeatable).
    #[arg(long)]
    test: Vec<String>,
    /// Skip exports larger than this.
    #[arg(long)]
    max_bytes: Option<u64>,
    /// Multiply the arena's timeouts (set for its 8-core runner) by this.
    #[arg(long, default_value_t = 1.0)]
    timeout_scale: f64,
    /// Ignore the arena's timeouts.
    #[arg(long)]
    no_timeout: bool,
    /// Print only mismatches and errors.
    #[arg(long)]
    quiet: bool,
}

fn sh_quote(s: &str) -> String {
    format!("'{}'", s.replace('\'', "'\\''"))
}

fn env_nonempty(k: &str) -> Option<String> {
    std::env::var(k).ok().filter(|v| !v.is_empty())
}

/// (name, command, cwd), or why the checker is unavailable.
fn resolve_checker(
    spec: &str,
    nitrolean: Option<&str>,
) -> std::result::Result<(String, String, Option<PathBuf>), String> {
    if let Some((name, cmd)) = spec.split_once('=') {
        return Ok((name.into(), cmd.into(), None));
    }
    let root = root();
    match spec {
        "nitrolean" => {
            let built = root.join("target/release/nitrolean");
            let exe = match nitrolean.filter(|n| !n.is_empty()) {
                Some(n) => Some(n.to_string()),
                None if built.exists() => Some(built.to_string_lossy().into_owned()),
                None => which("nitrolean").map(|p| p.to_string_lossy().into_owned()),
            };
            match exe {
                Some(e) => Ok((
                    "nitrolean".into(),
                    format!("{} check \"$IN\"", sh_quote(&e)),
                    None,
                )),
                None => {
                    Err("nitrolean not found (cargo build --release, or pass --nitrolean)".into())
                }
            }
        }
        "official" => {
            let exe = env_nonempty("LEANCHECKER").or_else(|| {
                let elan_home = std::env::var_os("ELAN_HOME")
                    .map(PathBuf::from)
                    .unwrap_or_else(|| {
                        PathBuf::from(std::env::var_os("HOME").unwrap_or_default()).join(".elan")
                    });
                let cand = elan_home
                    .join("toolchains")
                    .join(OFFICIAL_TOOLCHAIN)
                    .join("bin/leanchecker");
                if cand.exists() {
                    Some(cand.to_string_lossy().into_owned())
                } else {
                    which("leanchecker").map(|p| p.to_string_lossy().into_owned())
                }
            });
            match exe {
                Some(e) => Ok((
                    "official".into(),
                    format!("{} --from-export \"$IN\"", sh_quote(&e)),
                    None,
                )),
                None => Err("leanchecker not found (elan toolchain install leanprover/lean4:v4.35.0, or set LEANCHECKER)".into()),
            }
        }
        "gruszka" => match env_nonempty("GRUSZKA_DIR") {
            Some(d) if Path::new(&d).join("scripts/arena-run").exists() => Ok((
                "gruszka".into(),
                "scripts/arena-run \"$IN\" 4".into(),
                Some(PathBuf::from(d)),
            )),
            _ => Err("gruszka not found (set GRUSZKA_DIR to a built checkout)".into()),
        },
        "nano-lean" => {
            if let Some(d) = env_nonempty("NANO_LEAN_DIR")
                && Path::new(&d).join("target/release/nl-fast").exists()
            {
                return Ok((
                    "nano-lean".into(),
                    "target/release/nl-fast -q -j 4 \"$IN\"".into(),
                    Some(PathBuf::from(d)),
                ));
            }
            match which("nl-fast") {
                Some(e) => Ok((
                    "nano-lean".into(),
                    format!("{} -q -j 4 \"$IN\"", sh_quote(&e.to_string_lossy())),
                    None,
                )),
                None => Err("nano-lean not found (set NANO_LEAN_DIR to a built checkout)".into()),
            }
        }
        _ => Err(format!("unknown checker {spec} (use NAME=CMD for others)")),
    }
}

/// Whether `perf stat` can count instructions here, as the arena does when
/// it ranks checkers (by Mathlib's instruction count).
fn perf_ok() -> bool {
    if which("perf").is_none() {
        return false;
    }
    match Command::new("perf")
        .args(["stat", "-x,", "-e", "instructions", "--", "true"])
        .output()
    {
        Ok(o) => {
            let err = String::from_utf8_lossy(&o.stderr);
            o.status.success() && !err.contains("not supported") && !err.contains("<not")
        }
        Err(_) => false,
    }
}

struct Tools {
    /// GNU time, which the arena measures peak memory with. A process forked
    /// from the runner may start with the runner's resident pages counted in
    /// its peak, so without it the peak of a small run reads too high.
    gnu_time: Option<PathBuf>,
    perf: bool,
    tmp: PathBuf,
}

struct RunResult {
    status: String,
    exit_code: i32,
    wall_s: String,
    cpu_s: String,
    max_rss_mib: String,
    ginstructions: String,
    note: String,
}

fn run_one(
    tools: &Tools,
    cmd: &str,
    export: &Path,
    cwd: Option<&Path>,
    timeout: Option<f64>,
) -> Result<RunResult> {
    let tf = tools.tmp.join("time");
    let pf = tools.tmp.join("perf");
    let _ = fs::remove_file(&tf);
    let _ = fs::remove_file(&pf);
    let mut argv: Vec<String> = vec!["sh".into(), "-c".into(), cmd.into()];
    if let Some(t) = &tools.gnu_time {
        let mut w = vec![
            t.to_string_lossy().into_owned(),
            "-q".into(),
            "-f".into(),
            "%M".into(),
            "-o".into(),
            tf.to_string_lossy().into_owned(),
            "--".into(),
        ];
        w.extend(argv);
        argv = w;
    }
    if tools.perf {
        let mut w: Vec<String> = ["perf", "stat", "-x,", "-e", "instructions", "-o"]
            .iter()
            .map(|s| s.to_string())
            .collect();
        w.push(pf.to_string_lossy().into_owned());
        w.push("--".into());
        w.extend(argv);
        argv = w;
    }
    let mut c = Command::new(&argv[0]);
    c.args(&argv[1..]).env("IN", export).stdout(Stdio::null());
    if let Some(d) = cwd {
        c.current_dir(d);
    }
    let o = run_timed(
        &mut c,
        timeout.map(Duration::from_secs_f64),
        true,
        1 << 16,
        true,
    )?;
    let stderr = String::from_utf8_lossy(&o.stderr).into_owned();
    let mut maxrss_kib = o.maxrss_kib as f64;
    if tools.gnu_time.is_some()
        && let Ok(t) = fs::read_to_string(&tf)
        && let Some(Ok(v)) = t.split_whitespace().last().map(str::parse::<i64>)
    {
        maxrss_kib = v as f64;
    }
    let mut instructions = String::new();
    if tools.perf
        && let Ok(t) = fs::read_to_string(&pf)
    {
        for line in t.lines() {
            let f: Vec<&str> = line.split(',').collect();
            if f.len() > 2
                && f[2].starts_with("instructions")
                && !f[0].is_empty()
                && f[0].chars().all(|c| c.is_ascii_digit())
                && let Ok(n) = f[0].parse::<u128>()
            {
                // In billions, as a long bare count reads like an id.
                instructions = format!("{:.3}", n as f64 / 1e9);
            }
        }
    }
    let status = if o.timed_out {
        "timeout"
    } else {
        match o.code {
            0 => "accepted",
            1 => "rejected",
            2 => "declined",
            _ => "error",
        }
    };
    let note = stderr
        .lines()
        .map(str::trim)
        .find(|l| !l.is_empty())
        .unwrap_or("");
    let note = note.replace(&export.to_string_lossy().into_owned(), "$IN");
    // Long digit runs (hygiene hashes in names) are noise and read like ids.
    let digits = regex::Regex::new(r"\d{9,}").expect("valid regex");
    let note = digits.replace_all(&note, "#");
    let note: String = crate::util::squash(&note).chars().take(160).collect();
    Ok(RunResult {
        status: status.into(),
        exit_code: o.code,
        wall_s: format!("{:.3}", o.wall),
        cpu_s: format!("{:.3}", o.cpu),
        max_rss_mib: format!("{:.1}", maxrss_kib / 1024.0),
        ginstructions: instructions,
        note,
    })
}

/// As the arena scores a result.
fn correctness(expected: &str, status: &str) -> &'static str {
    match status {
        "declined" => "declined",
        "error" | "timeout" => "error",
        _ if expected == "either" => "either",
        _ if matches!(
            (expected, status),
            ("accept", "accepted") | ("reject", "rejected")
        ) =>
        {
            "correct"
        }
        _ => "incorrect",
    }
}

fn cmd_run(a: RunArgs) -> Result<()> {
    let here = here();
    let tests = read_tsv(&a.tests.unwrap_or_else(|| here.join("tests.tsv")))?;
    let exports = a.exports.unwrap_or_else(|| here.join("data/exports"));
    let out = a.out.unwrap_or_else(|| here.join("results/results.tsv"));
    let mut specs = if a.checker.is_empty() {
        vec!["nitrolean".to_string()]
    } else {
        a.checker
    };
    if a.competitors {
        for c in COMPETITORS {
            if !specs.iter().any(|s| s == c) {
                specs.push(c.into());
            }
        }
    }
    let mut checkers = Vec::new();
    for spec in &specs {
        match resolve_checker(spec, a.nitrolean.as_deref()) {
            Ok(c) => checkers.push(c),
            Err(why) => eprintln!("run: skipping {spec}: {why}"),
        }
    }
    if checkers.is_empty() {
        return Err(exit_with(1, "run: no checker to run"));
    }

    let mut done = HashSet::new();
    if fs::metadata(&out).map(|m| m.len() > 0).unwrap_or(false) {
        for r in read_tsv(&out)? {
            done.insert((
                cell(&r, "checker").to_string(),
                cell(&r, "test").to_string(),
            ));
        }
    } else {
        if let Some(d) = out.parent() {
            fs::create_dir_all(d)?;
        }
        fs::write(&out, COLUMNS.join("\t") + "\n")?;
    }

    let mut selected = Vec::new();
    for t in &tests {
        let name = cell(t, "test");
        if !a.test.is_empty() && !a.test.iter().any(|p| glob_match(p, name)) {
            continue;
        }
        let export = exports.join(format!("{name}.ndjson"));
        let Ok(md) = fs::metadata(&export) else {
            continue;
        };
        if a.max_bytes.is_some_and(|m| md.len() > m) {
            continue;
        }
        selected.push((t, export));
    }
    eprintln!(
        "run: {} exports, checkers: {}",
        selected.len(),
        checkers
            .iter()
            .map(|c| c.0.as_str())
            .collect::<Vec<_>>()
            .join(", ")
    );

    let tmp = std::env::temp_dir().join(format!("arena-run-{}", std::process::id()));
    fs::create_dir_all(&tmp)?;
    let gt = which("time").or_else(|| {
        let p = PathBuf::from("/usr/bin/time");
        p.exists().then_some(p)
    });
    let tools = Tools {
        gnu_time: gnu_time(&[gt]),
        perf: perf_ok(),
        tmp: tmp.clone(),
    };
    let res = run_all(
        &a.quiet,
        a.no_timeout,
        a.timeout_scale,
        &tools,
        &checkers,
        &selected,
        &done,
        &out,
    );
    let _ = fs::remove_dir_all(&tmp);
    res
}

#[allow(clippy::too_many_arguments)]
fn run_all(
    quiet: &bool,
    no_timeout: bool,
    timeout_scale: f64,
    tools: &Tools,
    checkers: &[(String, String, Option<PathBuf>)],
    selected: &[(&HashMap<String, String>, PathBuf)],
    done: &HashSet<(String, String)>,
    out: &Path,
) -> Result<()> {
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    for (name, cmd, cwd) in checkers {
        for (t, export) in selected {
            let test = cell(t, "test");
            if done.contains(&(name.clone(), test.to_string())) {
                continue;
            }
            let mut timeout = None;
            let tt = cell(t, "timeout");
            if !tt.is_empty() && !no_timeout {
                let v: f64 = tt
                    .trim()
                    .parse()
                    .with_context(|| format!("run: bad timeout {tt}"))?;
                timeout = Some(v * timeout_scale);
            }
            let timeout = timeout.filter(|&t| t != 0.0);
            let r = run_one(tools, cmd, export, cwd.as_deref(), timeout)?;
            let expected = cell(t, "expected");
            let corr = correctness(expected, &r.status);
            let row = [
                name.as_str(),
                test,
                cell(t, "group"),
                expected,
                &r.status,
                corr,
                &r.exit_code.to_string(),
                &r.wall_s,
                &r.cpu_s,
                &r.max_rss_mib,
                &r.ginstructions,
                &timeout.map(fmt_g).unwrap_or_default(),
                &r.note,
            ]
            .iter()
            .map(|c| c.replace('\t', " "))
            .collect::<Vec<_>>()
            .join("\t");
            let mut f = fs::OpenOptions::new().append(true).open(out)?;
            writeln!(f, "{row}")?;
            *counts.entry(corr).or_default() += 1;
            let flag = if corr == "incorrect" {
                "  <-- MISMATCH"
            } else {
                ""
            };
            if !*quiet || !flag.is_empty() || corr == "error" {
                eprintln!(
                    "{name:10} {test:50} {expected:7} {:9} {:>9}s {:>9} MiB{flag}",
                    r.status, r.wall_s, r.max_rss_mib
                );
            }
        }
    }
    eprintln!(
        "run: {}",
        counts
            .iter()
            .map(|(k, v)| format!("{k} {v}"))
            .collect::<Vec<_>>()
            .join(", ")
    );
    Ok(())
}

// ---------------------------------------------------------------------------
// report

#[derive(Args)]
pub struct ReportArgs {
    /// Result TSVs (later ones override earlier ones).
    #[arg(required = true)]
    results: Vec<PathBuf>,
    /// The tests [default: bench/arena/tests.tsv]
    #[arg(long)]
    tests: Option<PathBuf>,
    /// The arena's published results [default: bench/arena/published.tsv]
    #[arg(long)]
    published: Option<PathBuf>,
    /// The checker the table is about.
    #[arg(long, default_value = "nitrolean")]
    main: String,
    /// Only tests of this group (repeatable).
    #[arg(long)]
    group: Vec<String>,
}

fn fmt_time(s: &str) -> Result<String> {
    if s.is_empty() {
        return Ok(String::new());
    }
    let v = pyfloat(s)?;
    Ok(if v < 10.0 {
        format!("{v:.2}")
    } else if v < 100.0 {
        format!("{v:.1}")
    } else {
        format!("{v:.0}")
    })
}

fn fmt_mib(mib: f64) -> String {
    if mib < 1024.0 {
        format!("{mib:.0} MiB")
    } else {
        format!("{:.1} GiB", mib / 1024.0)
    }
}

fn pyfloat(s: &str) -> Result<f64> {
    s.trim()
        .parse()
        .with_context(|| format!("could not convert string to float: '{s}'"))
}

fn short(status: &str) -> &str {
    match status {
        "accepted" => "accept",
        "rejected" => "reject",
        s => s,
    }
}

fn cmd_report(a: ReportArgs) -> Result<()> {
    let here = here();
    let tests_path = a.tests.unwrap_or_else(|| here.join("tests.tsv"));
    let text = fs::read_to_string(&tests_path)
        .with_context(|| format!("{}: cannot read", tests_path.display()))?;
    let test_rows = parse_tsv(&text);
    let mut tests: HashMap<String, &HashMap<String, String>> = HashMap::new();
    let mut order: HashMap<String, usize> = HashMap::new();
    for r in &test_rows {
        let n = cell(r, "test").to_string();
        if !order.contains_key(&n) {
            order.insert(n.clone(), order.len());
        }
        tests.insert(n, r);
    }
    let mut rows: HashMap<(String, String), HashMap<String, String>> = HashMap::new();
    for path in &a.results {
        for r in read_tsv(path)? {
            rows.insert((cell(&r, "checker").into(), cell(&r, "test").into()), r);
        }
    }
    let published: HashMap<(String, String), HashMap<String, String>> =
        read_tsv(&a.published.unwrap_or_else(|| here.join("published.tsv")))?
            .into_iter()
            .map(|r| ((cell(&r, "checker").into(), cell(&r, "test").into()), r))
            .collect();
    let main = a.main.as_str();
    let mut others: Vec<&str> = rows
        .keys()
        .map(|(c, _)| c.as_str())
        .filter(|c| *c != main)
        .collect::<HashSet<_>>()
        .into_iter()
        .collect();
    others.sort_by_key(|c| {
        (
            COMPETITORS
                .iter()
                .position(|x| x == c)
                .unwrap_or(COMPETITORS.len()),
            c.to_string(),
        )
    });
    let mut names: Vec<&str> = rows
        .keys()
        .filter(|(c, _)| c == main)
        .map(|(_, t)| t.as_str())
        .collect();
    names.sort_by_key(|n| (order.get(*n).copied().unwrap_or(0), n.to_string()));
    let test_of = |n: &str| -> Result<&HashMap<String, String>> {
        tests
            .get(n)
            .copied()
            .with_context(|| format!("KeyError: '{n}'"))
    };
    if !a.group.is_empty() {
        let mut kept = Vec::new();
        for n in names {
            let g = cell(test_of(n)?, "group");
            if a.group.iter().any(|x| x == g) {
                kept.push(n);
            }
        }
        names = kept;
    }

    let mut head: Vec<String> = ["test", "expected", main, "wall s", "CPU s", "peak RSS"]
        .iter()
        .map(|s| s.to_string())
        .collect();
    for o in &others {
        head.push(format!("{o} (here)"));
    }
    for c in COMPETITORS {
        head.push(format!("{c} (arena)"));
    }
    let mut s = String::new();
    s.push_str(&format!("| {} |\n", head.join(" | ")));
    s.push_str(&format!("|{}\n", "---|".repeat(head.len())));
    let mut tally: BTreeMap<String, usize> = BTreeMap::new();
    for n in &names {
        let r = &rows[&(main.to_string(), n.to_string())];
        let corr = cell(r, "correctness");
        *tally.entry(corr.to_string()).or_default() += 1;
        let mut verdict = short(cell(r, "status")).to_string();
        if corr == "incorrect" {
            verdict = format!("**{verdict} MISMATCH**");
        } else if corr == "error" {
            verdict = format!("**{verdict}**");
        }
        // A run killed at its timeout leaves no usable CPU time or peak.
        let killed = cell(r, "status") == "timeout";
        let mut cells = vec![
            n.to_string(),
            cell(test_of(n)?, "expected").to_string(),
            verdict,
            fmt_time(cell(r, "wall_s"))?,
            if killed {
                String::new()
            } else {
                fmt_time(cell(r, "cpu_s"))?
            },
            if killed {
                String::new()
            } else {
                fmt_mib(pyfloat(cell(r, "max_rss_mib"))?)
            },
        ];
        for o in &others {
            cells.push(match rows.get(&(o.to_string(), n.to_string())) {
                Some(x) => format!(
                    "{} {} s, {}",
                    short(cell(x, "status")),
                    fmt_time(cell(x, "wall_s"))?,
                    fmt_mib(pyfloat(cell(x, "max_rss_mib"))?)
                ),
                None => String::new(),
            });
        }
        for c in COMPETITORS {
            cells.push(match published.get(&(c.to_string(), n.to_string())) {
                Some(p) => {
                    let bytes: i64 = cell(p, "max_rss_bytes")
                        .trim()
                        .parse()
                        .context("bad max_rss_bytes")?;
                    format!(
                        "{} {} s, {}",
                        short(cell(p, "status")),
                        fmt_time(cell(p, "wall_s"))?,
                        fmt_mib(bytes as f64 / 1048576.0)
                    )
                }
                None => String::new(),
            });
        }
        s.push_str(&format!("| {} |\n", cells.join(" | ")));
    }
    s.push('\n');
    s.push_str(&format!(
        "{main}: {}\n",
        tally
            .iter()
            .map(|(k, v)| format!("{k} {v}"))
            .collect::<Vec<_>>()
            .join(", ")
    ));
    print!("{s}");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn python_floats() {
        assert_eq!(py_float(120.0), "120.0");
        assert_eq!(py_float(1.5), "1.5");
        assert_eq!(py_float(1e-5), "1e-05");
        assert_eq!(py_float(1e16), "1e+16");
        assert_eq!(py_float(123456789.25), "123456789.25");
    }

    #[test]
    fn scoring() {
        assert_eq!(correctness("accept", "accepted"), "correct");
        assert_eq!(correctness("reject", "accepted"), "incorrect");
        assert_eq!(correctness("either", "rejected"), "either");
        assert_eq!(correctness("accept", "timeout"), "error");
        assert_eq!(correctness("accept", "declined"), "declined");
    }
}
