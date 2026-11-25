//! `cargo xtask oracle build|run|reduce|all`: the corpus oracle of
//! bench/oracle, which compares nitrolean's verdicts with those of Lean's own
//! checker, declaration by declaration, on pinned public Lean projects.

mod export;
mod pyjson;
mod reduce;

use std::collections::{HashMap, HashSet};
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use anyhow::{Context, Result, anyhow, bail};
use regex::Regex;

use crate::limited::run_limited;
use crate::util::{self, exit_with, git, log, root, sha256_file};
use export::{Index, norm_name};
use pyjson::J;

#[derive(clap::Subcommand)]
pub enum Cmd {
    /// Build the pinned projects and export each one.
    #[command(alias = "fetch")]
    Build(BuildArgs),
    /// Per-declaration verdicts of Lean's checker and of nitrolean on the built projects.
    Run(RunArgs),
    /// Reduce a declaration the checkers disagree on to a small export.
    Reduce(reduce::Args),
    /// Write the closure of some declarations (with everything they use) as an export.
    Closure(reduce::ClosureArgs),
    /// `cargo build --release`, then `oracle build`, then `oracle run`.
    All(RunArgs),
}

pub fn main(c: Cmd) -> Result<()> {
    match c {
        Cmd::Build(a) => build(a).map_err(|e| prefix_error("build", e)),
        Cmd::Run(a) => run_main(a),
        Cmd::Reduce(a) => reduce::main(a),
        Cmd::Closure(a) => reduce::closure_main(a),
        Cmd::All(a) => all(a),
    }
}

fn here() -> PathBuf {
    root().join("bench/oracle")
}

fn prefix_error(tool: &str, e: anyhow::Error) -> anyhow::Error {
    if e.downcast_ref::<util::Exit>().is_some() {
        return e;
    }
    let msg = format!("{e:#}");
    if msg.starts_with(&format!("{tool}: ")) {
        e
    } else {
        anyhow!("{tool}: error: {msg}")
    }
}

fn default_dir(env: &str, sub: &str) -> PathBuf {
    std::env::var_os(env)
        .map(PathBuf::from)
        .unwrap_or_else(|| here().join(sub))
}

// ---------------------------------------------------------------------------
// cargo xtask oracle build

/// Build the pinned projects and export each one.
///
/// For each project: a checkout at the pinned commit (its lean-toolchain must
/// be the pinned one), `lake exe cache get` if the project asks for it, `lake
/// build` of its roots, then the list of the non-internal constants declared
/// in its own modules and the export of their closure with the exporter of
/// that toolchain. Writes, in OUT/<id>/:
///   export.ndjson     the export (not committed)
///   own-names.txt     the constants it is the closure of
///   build.env         toolchain, project directory and roots, for `oracle run`
/// and checks the export's SHA-256 against exports.sha256 (an id not listed
/// there is added). Needs git and elan. A project already built is not rebuilt.
#[derive(clap::Args)]
#[command(verbatim_doc_comment)]
pub struct BuildArgs {
    /// the projects of projects.tsv with tier <= N
    #[arg(long, default_value_t = 1)]
    tier: i64,
    /// these projects (comma list of ids) instead, whatever their tier
    #[arg(long, default_value = "")]
    only: String,
    /// where the exports go (default bench/oracle/out, or $ORACLE_OUT)
    #[arg(long)]
    out: Option<PathBuf>,
    /// sources and build trees (default bench/oracle/cache, or $ORACLE_CACHE)
    #[arg(long)]
    cache: Option<PathBuf>,
    /// record export SHA-256s that differ from exports.sha256 instead of stopping
    #[arg(long)]
    update_pins: bool,
}

/// The exporter commit of github.com/leanprover/lean4export for toolchains
/// before v4.35.0, whose `leanexport` does not ship with Lean.
fn lean4export_commit(tc: &str) -> Option<&'static str> {
    Some(match tc {
        "leanprover/lean4:v4.28.0" => "ca36c44858e2d7ba40996203d2f08a69113d1211",
        "leanprover/lean4:v4.29.0" => "caccfbebbc99077962b3321125b2375bb3fa22db",
        "leanprover/lean4:v4.30.0" => "a3e35a584f59b390667db7269cd37fca8575e4bf",
        "leanprover/lean4:v4.31.0" => "8554815c2dc6b7abe99ec1f08849c9759ba77947",
        "leanprover/lean4:v4.32.0" => "4e7915201d3f9f04470d9eae002fa695f7cdc589",
        "leanprover/lean4:v4.33.0" => "15f6055e299ad5b89345e533cc2192f4cc00f659",
        "leanprover/lean4:v4.34.0" => "076e8e57707e813375e8f9da8bf989799ace9680",
        _ => return None,
    })
}

const LEAN4EXPORT_URL: &str = "https://github.com/leanprover/lean4export";

/// The exporter for a toolchain, built into the cache if needed.
fn exporter(tc: &str, bin: &Path, cache: &Path) -> Result<PathBuf> {
    let shipped = bin.join("leanexport");
    if util::is_executable(&shipped) {
        return Ok(shipped);
    }
    let commit = lean4export_commit(tc)
        .ok_or_else(|| anyhow!("build: error: no exporter pinned for {tc}"))?;
    let dir = cache.join(format!("lean4export-{}", &commit[..12]));
    let exe = dir.join(".lake/build/bin/lean4export");
    if !util::is_executable(&exe) {
        if dir.exists() {
            fs::remove_dir_all(&dir)?;
        }
        fs::create_dir_all(&dir)?;
        util::run(git(&dir).args(["init", "-q"]))?;
        util::run(git(&dir).args(["remote", "add", "origin", LEAN4EXPORT_URL]))?;
        util::run(git(&dir).args(["fetch", "-q", "--depth", "1", "origin", commit]))?;
        util::run(git(&dir).args(["-c", "advice.detachedHead=false", "checkout", "-q", commit]))?;
        let got = fs::read_to_string(dir.join("lean-toolchain"))?;
        let got = got.trim_end_matches('\n');
        if got != tc {
            bail!("build: error: lean4export {commit} is for {got}, not {tc}");
        }
        util::run(
            util::cmd_in("lake", &dir)
                .env("PATH", util::path_with(bin))
                .arg("build")
                .stdout(stderr()?),
        )?;
    }
    Ok(exe)
}

fn stderr() -> Result<Stdio> {
    use std::os::fd::AsFd;
    Ok(Stdio::from(std::io::stderr().as_fd().try_clone_to_owned()?))
}

/// The lines of projects.tsv with tier <= `tier` (or whose id is in the comma
/// list `only`, when it is not empty), split into their fields.
fn build_projects(tier: i64, only: &str) -> Result<Vec<Vec<String>>> {
    let text = fs::read_to_string(here().join("projects.tsv"))?;
    let only: Vec<&str> = only.split(',').collect();
    let mut out = Vec::new();
    for line in text.lines() {
        if line.starts_with('#') || line.trim().is_empty() {
            continue;
        }
        // As `IFS=$'\t' read`: runs of tabs separate fields.
        let f: Vec<String> = line
            .split('\t')
            .filter(|s| !s.is_empty())
            .map(String::from)
            .collect();
        let id = f.first().map(String::as_str).unwrap_or("");
        let t: i64 = f.get(1).and_then(|t| t.trim().parse().ok()).unwrap_or(0);
        let selected = if only != [""] {
            only.contains(&id)
        } else {
            t <= tier
        };
        if selected {
            out.push(f);
        }
    }
    Ok(out)
}

fn build(a: BuildArgs) -> Result<()> {
    util::need("build", &["git", "elan"], " (see README.md)")?;
    let out = util::abs_dir(&a.out.unwrap_or_else(|| default_dir("ORACLE_OUT", "out")))?;
    let cache = util::abs_dir(
        &a.cache
            .unwrap_or_else(|| default_dir("ORACLE_CACHE", "cache")),
    )?;
    fs::create_dir_all(cache.join("src"))?;
    let sums = here().join("exports.sha256");
    if !sums.exists() {
        fs::write(&sums, "")?;
    }
    let mut n = 0;
    for f in build_projects(a.tier, &a.only)? {
        let get = |i: usize| f.get(i).cloned().unwrap_or_default();
        let (id, tc, url, commit) = (get(0), get(2), get(3), get(4));
        let (subdir, roots, prefixes, use_cache) =
            (get(5), get(6), get(7), f[8.min(f.len())..].join("\t"));
        let env = out.join(&id).join("build.env");
        if out.join(&id).join("export.ndjson").is_file()
            && env.is_file()
            && fs::read_to_string(&env)?
                .lines()
                .any(|l| l == format!("commit={commit}"))
        {
            log("build", &format!("{id}: already built"));
            n += 1;
            continue;
        }
        build_one(
            &out,
            &cache,
            &sums,
            a.update_pins,
            &id,
            &tc,
            &url,
            &commit,
            &subdir,
            &roots,
            &prefixes,
            &use_cache,
        )?;
        n += 1;
    }
    if n == 0 {
        bail!("build: error: no project selected");
    }
    log(
        "build",
        &format!("built {n} project(s) in {}", out.display()),
    );
    Ok(())
}

/// `du -h FILE`: the disk usage, rounded up, as 4.0K, 57M, 1.2G...
fn du_h(path: &Path) -> String {
    use std::os::unix::fs::MetadataExt;
    let bytes = fs::metadata(path).map(|m| m.blocks() * 512).unwrap_or(0) as f64;
    if bytes < 1024.0 {
        return format!("{bytes}");
    }
    let mut v = bytes;
    for u in ["K", "M", "G", "T", "P", "E"] {
        v /= 1024.0;
        if v < 1024.0 || u == "E" {
            return if v < 10.0 {
                let r = (v * 10.0).ceil() / 10.0;
                if r >= 10.0 {
                    format!("{r:.0}{u}")
                } else {
                    format!("{r:.1}{u}")
                }
            } else {
                format!("{:.0}{u}", v.ceil())
            };
        }
    }
    unreachable!()
}

#[allow(clippy::too_many_arguments)]
fn build_one(
    out_root: &Path,
    cache: &Path,
    sums: &Path,
    update: bool,
    id: &str,
    tc: &str,
    url: &str,
    commit: &str,
    subdir: &str,
    roots: &str,
    prefixes: &str,
    use_cache: &str,
) -> Result<()> {
    let src = cache.join("src").join(id);
    let dir = src.join(subdir);
    let out = out_root.join(id);
    fs::create_dir_all(&out)?;
    if !src.join(".git").is_dir() {
        util::run(Command::new("git").args(["init", "-q"]).arg(&src))?;
        util::run(git(&src).args(["remote", "add", "origin", url]))?;
    }
    let have = git(&src)
        .args(["cat-file", "-e", &format!("{commit}^{{commit}}")])
        .stderr(Stdio::null())
        .status()?;
    if !have.success() {
        log("build", &format!("{id}: fetching {commit}"));
        util::run(git(&src).args(["fetch", "-q", "--depth", "1", "origin", commit]))?;
    }
    util::run(git(&src).args([
        "-c",
        "advice.detachedHead=false",
        "checkout",
        "-q",
        "--force",
        commit,
    ]))?;
    if util::output(git(&src).args(["rev-parse", "HEAD"]))?.trim() != commit {
        bail!("build: error: {id}: not at {commit}");
    }
    let got_tc = fs::read_to_string(dir.join("lean-toolchain")).unwrap_or_default();
    if got_tc.split_whitespace().collect::<String>() != tc {
        bail!(
            "build: error: {id}: lean-toolchain is {}, pinned {tc}",
            got_tc.trim_end_matches('\n')
        );
    }
    let bin = util::tc_bin(tc)?;
    let exp = exporter(tc, &bin, cache)?;
    let path = util::path_with(&bin);
    let r: Vec<&str> = roots.split(',').filter(|s| !s.is_empty()).collect();
    let p: Vec<&str> = prefixes.split(',').filter(|s| !s.is_empty()).collect();
    let lake = |args: &[&str]| {
        let mut c = util::cmd_in("lake", &dir);
        c.env("PATH", &path).args(args);
        c
    };
    let part = out.join("export.ndjson.part");
    let res = (|| -> Result<()> {
        if use_cache == "yes" {
            log("build", &format!("{id}: lake exe cache get"));
            util::run(lake(&["exe", "cache", "get"]).stdout(stderr()?))?;
        }
        log("build", &format!("{id}: lake build {} ({tc})", r.join(" ")));
        let mut b = lake(&["build"]);
        b.args(&r);
        let blog = out.join("build.log");
        util::run_logged(&mut b, &blog, 30, "lake build failed")?;
        log("build", &format!("{id}: own declarations"));
        let own = out.join("own-names.txt");
        let mut l = lake(&["env", "lean", "--run"]);
        l.arg(root().join("bench/kernel-compute/lean/ListOwn.lean"))
            .args(&r)
            .arg("--")
            .args(&p)
            .stdout(fs::File::create(&own)?);
        util::unlimited_stack(&mut l);
        util::run(&mut l)?;
        let names = fs::read_to_string(&own)?;
        let count = names.bytes().filter(|&b| b == b'\n').count();
        log("build", &format!("{id}: export ({count} names)"));
        let mut e = lake(&["env"]);
        e.arg(&exp)
            .args(&r)
            .arg("--")
            .args(names.split_whitespace())
            .stdout(fs::File::create(&part)?);
        util::unlimited_stack(&mut e);
        util::run(&mut e)
    })();
    if res.is_err() {
        bail!("build: error: {id}: build or export failed");
    }
    let export = out.join("export.ndjson");
    fs::rename(&part, &export)?;
    fs::write(
        out.join("build.env"),
        format!(
            "toolchain={tc}\nproject_dir={}\nroots={roots}\ncommit={commit}\n",
            dir.display()
        ),
    )?;
    let got = sha256_file(&export)?;
    let file = format!("{id}.ndjson");
    let text = fs::read_to_string(sums)?;
    let want = text
        .lines()
        .filter_map(|l| {
            let mut w = l.split_whitespace();
            let (h, f) = (w.next()?, w.next()?);
            (f == file).then(|| h.to_string())
        })
        .collect::<Vec<_>>()
        .join("\n");
    if want.is_empty() {
        let mut lines: Vec<String> = text.lines().map(String::from).collect();
        lines.push(format!("{got}  {file}"));
        // As `sort -k2`: by the text after the first field, then the whole line.
        let key = |l: &String| {
            let t = l.trim_start();
            let rest = &t[t.find(char::is_whitespace).unwrap_or(t.len())..];
            (rest.to_string(), l.clone())
        };
        lines.sort_by_key(key);
        fs::write(
            sums,
            lines.iter().map(|l| format!("{l}\n")).collect::<String>(),
        )?;
        log("build", &format!("{id}: recorded SHA-256 {got}"));
    } else if got != want {
        if update {
            let new: String = text
                .lines()
                .map(|l| {
                    let mut w = l.split_whitespace();
                    match (w.next(), w.next()) {
                        (Some(_), Some(f)) if f == file => format!("{got}  {f}\n"),
                        _ => format!("{l}\n"),
                    }
                })
                .collect();
            fs::write(sums, new)?;
            log("build", &format!("{id}: SHA-256 now {got} (was {want})"));
        } else {
            bail!(
                "build: error: {id}: export SHA-256 is {got}, pinned {want} (--update-pins to accept it)"
            );
        }
    }
    let lines = {
        let mut n = 0usize;
        export::for_lines(&export, |_, _| {
            n += 1;
            Ok(())
        })?;
        // `wc -l` counts newlines: a last line without one is not counted.
        let ends = fs::metadata(&export)?.len() == 0 || {
            use std::io::{Read, Seek, SeekFrom};
            let mut f = fs::File::open(&export)?;
            f.seek(SeekFrom::End(-1))?;
            let mut b = [0u8; 1];
            f.read_exact(&mut b)?;
            b[0] == b'\n'
        };
        if ends { n } else { n - 1 }
    };
    log("build", &format!("{id}: {lines} lines, {}", du_h(&export)));
    Ok(())
}

// ---------------------------------------------------------------------------
// cargo xtask oracle run

/// Per-declaration verdicts of Lean's checker and of nitrolean.
///
/// For each project built by `oracle build` (OUT/<id>/export.ndjson and build.env):
///
/// 1. Lean: `leanchecker --from-export` of the project's toolchain (v4.36.0
///    for toolchains before v4.35.0, whose leanchecker has no --from-export).
/// 2. nitrolean on the export, with --threads 1 and with all cores.
/// 3. nitrolean on the project's .olean files (`check --olean DIR --module
///    ROOT`), with --threads 1 and with all cores, when they are .olean files
///    of Lean v4.36.0, the only version nitrolean's .olean reader supports.
///
/// A run that rejects declaration D is repeated on the export without D (a
/// theorem becomes an axiom, anything else is dropped with its dependents),
/// up to --max-rounds runs; the verdicts are compared constant by constant
/// (see bench/oracle/README.md).
///
/// Writes OUT/<id>/result.json and OUT/<id>/verdicts.tsv, and the summary
/// table to --results (default bench/oracle/RESULTS.md). Prints every
/// mismatch; a constant nitrolean accepts and Lean rejects is reported as a
/// SOUNDNESS mismatch. Exit status 0 if every project agrees and the variants
/// are identical, 1 if not.
#[derive(clap::Args, Clone)]
#[command(verbatim_doc_comment)]
pub struct RunArgs {
    #[arg(long, default_value_t = 1)]
    tier: i64,
    #[arg(long, default_value = "")]
    only: String,
    /// default bench/oracle/out, or $ORACLE_OUT
    #[arg(long)]
    out: Option<PathBuf>,
    /// default target/release/nitrolean
    #[arg(long)]
    nitrolean: Option<PathBuf>,
    #[arg(long, default_value_t = 3600.0)]
    timeout: f64,
    #[arg(long, default_value_t = 64 * 1024)]
    mem_mib: i64,
    #[arg(long, default_value_t = 50)]
    max_rounds: usize,
    /// default bench/oracle/RESULTS.md
    #[arg(long)]
    results: Option<PathBuf>,
    #[arg(long)]
    keep_logs: bool,
}

/// Error kinds, from the message of either checker (first match wins).
const KINDS: [(&str, &str); 16] = [
    (
        "declined",
        r"^declined|resource limit|not implemented|too large|unsupported",
    ),
    (
        "malformed",
        r"malformed|parse error|undefined .*id|duplicate id|unknown record|line \d+:",
    ),
    (
        "already-declared",
        r"already declared|declared twice|duplicate (declaration|constant)",
    ),
    // Lean's replay skips partial and unsafe constants, so it reports a use of
    // one as an unknown constant.
    (
        "unknown-constant",
        r"unknown (constant|declaration)|must not contain (partial|unsafe)|uses unsafe declaration|environment does not have",
    ),
    // A constructor or recursor record that differs from what the kernel
    // derives (Lean: "Invalid recursor", found after the replay).
    (
        "inductive",
        r"does not match the declaration derived|^invalid (constructor|recursor)",
    ),
    ("declaration-type-mismatch", r"declaration type mismatch"),
    ("application-type-mismatch", r"application type mismatch"),
    ("function-expected", r"function expected"),
    ("type-expected", r"type expected"),
    ("projection", r"projection"),
    (
        "theorem-not-prop",
        r"theorem type is not prop|not a proposition",
    ),
    ("universe", r"universe|level param"),
    (
        "inductive",
        r"inductive|constructor|recursor|positiv|nested|quotient",
    ),
    ("loose-variables", r"free variable|metavariable|loose bound"),
    (
        "deep-recursion",
        r"deep recursion|recursion depth|stack overflow",
    ),
    ("timeout", r"deterministic timeout|heartbeat"),
];

pub fn kind_of(msg: &str) -> &'static str {
    let m = msg.to_lowercase();
    for (k, rx) in KINDS {
        if Regex::new(rx).unwrap().is_match(&m) {
            return k;
        }
    }
    "other"
}

/// The last `n` characters of `s`.
fn last_chars(s: &str, n: usize) -> String {
    let c: Vec<char> = s.chars().collect();
    c[c.len().saturating_sub(n)..].iter().collect()
}

/// (accepted, declaration, message) from a checker's output.
pub type Parsed = (bool, Option<String>, String);

pub fn parse_lean(log: &str) -> Parsed {
    if log.contains("Lean default kernel accepts the solution") && !log.contains("rejects") {
        return (true, None, String::new());
    }
    let re = Regex::new(r"(?s)while replaying declaration '(.+?)':\n(.*)").unwrap();
    if let Some(m) = re.captures(log) {
        return (false, Some(m[1].to_string()), m[2].trim().to_string());
    }
    let re = Regex::new(r"(Invalid|No such) (constructor|recursor) (\S+)").unwrap();
    if let Some(m) = re.captures(log) {
        return (false, Some(m[3].to_string()), m[0].to_string());
    }
    let re =
        Regex::new(r"(Quotient constant mismatch on|quotient constant in final kernel env): (\S+)")
            .unwrap();
    if let Some(m) = re.captures(log) {
        return (false, Some(m[2].to_string()), format!("quotient {}", &m[0]));
    }
    (false, None, last_chars(log.trim(), 500))
}

pub fn parse_nitrolean(log: &str) -> Parsed {
    if Regex::new(r"(?m)^accepted").unwrap().is_match(log) {
        return (true, None, String::new());
    }
    let re =
        Regex::new(r"(?ms)^nitrolean: (rejected|declined): declaration '(.+?)': (.*)").unwrap();
    if let Some(m) = re.captures(log) {
        let msg = m[3].trim().to_string();
        let msg = if &m[1] == "declined" {
            format!("declined: {msg}")
        } else {
            msg
        };
        return (false, Some(m[2].to_string()), msg);
    }
    let re = Regex::new(r"(?ms)^nitrolean: (.*)").unwrap();
    let s = match re.captures(log) {
        Some(m) => m[1].to_string(),
        None => log.to_string(),
    };
    (false, None, last_chars(s.trim(), 500))
}

pub fn read_log(path: &Path) -> String {
    String::from_utf8_lossy(&fs::read(path).unwrap_or_default()).into_owned()
}

/// One limited run as the JSON object `run.py` recorded.
fn run_json(st: &crate::limited::Limited) -> J {
    let mut j = J::obj();
    j.set("status", st.status.as_str());
    j.set("exit", st.exit.as_str());
    j.set("wall_s", st.wall_s);
    j.set("peak_mib", st.peak_mib);
    j
}

/// First line of a message, at most 300 characters (empty if no message).
fn first_line(msg: &str) -> String {
    util::truncate(msg.lines().next().unwrap_or(""), 300)
}

/// A map that keeps its insertion order (as a Python dict).
#[derive(Default, Clone, PartialEq)]
struct Ordered {
    items: Vec<(String, String)>,
    pos: HashMap<String, usize>,
}

impl Ordered {
    fn insert(&mut self, k: String, v: String) {
        match self.pos.get(&k) {
            Some(&i) => self.items[i].1 = v,
            None => {
                self.pos.insert(k.clone(), self.items.len());
                self.items.push((k, v));
            }
        }
    }
    fn get(&self, k: &str) -> Option<&str> {
        self.pos.get(k).map(|&i| self.items[i].1.as_str())
    }
    fn same(&self, o: &Ordered) -> bool {
        self.items.len() == o.items.len()
            && self.items.iter().all(|(k, v)| o.get(k) == Some(v.as_str()))
    }
}

struct PerDecl {
    j: J,
    status: String,
    verdicts: Ordered,
}

struct Ctx<'a> {
    args: &'a RunArgs,
    path: Option<OsString>,
}

/// The per-declaration loop for one checker on one export.
fn per_decl(
    label: &str,
    cmd_of: &dyn Fn(&Path) -> Vec<OsString>,
    parse: fn(&str) -> Parsed,
    export: &Path,
    index: &Index,
    work: &Path,
    cx: &Ctx,
) -> Result<PerDecl> {
    fs::create_dir_all(work)?;
    let mut cur = export.to_path_buf();
    let mut rejected: Vec<(String, (String, String))> = Vec::new();
    let mut axioms: HashSet<String> = HashSet::new();
    let mut drop: HashSet<String> = HashSet::new();
    let mut dropped: HashSet<String> = HashSet::new();
    let mut runs: Vec<J> = Vec::new();
    let mut status = "complete".to_string();
    let mut finished = false;
    for rnd in 0..cx.args.max_rounds {
        let log = work.join(format!("{label}.{rnd}.log"));
        let st = run_limited(
            &cmd_of(&cur),
            &log,
            cx.args.timeout,
            cx.args.mem_mib,
            cx.path.as_deref(),
            true,
        )?;
        let mut sj = run_json(&st);
        if st.status != "exited" {
            status = st.status.clone();
            runs.push(sj);
            finished = true;
            break;
        }
        let (ok, decl, msg) = parse(&read_log(&log));
        if ok && st.exit == "0" {
            runs.push(sj);
            finished = true;
            break;
        }
        if ok {
            status = format!("error: exit {}", st.exit);
            runs.push(sj);
            finished = true;
            break;
        }
        let d = decl.as_deref().map(norm_name);
        let rec = d
            .as_ref()
            .and_then(|d| index.by_name.get(d))
            .map(|&i| &index.decls[i]);
        let (Some(d), Some(rec)) = (d, rec) else {
            status = format!(
                "rejected without a declaration of the export: {}",
                util::truncate(&msg, 300)
            );
            runs.push(sj);
            finished = true;
            break;
        };
        let block: Vec<String> = rec.names.iter().map(|n| norm_name(n)).collect();
        if drop.contains(&d) {
            status = format!("rejected '{d}' again after dropping it");
            runs.push(sj);
            finished = true;
            break;
        }
        let kind = kind_of(&msg);
        sj.set("decl", d.as_str());
        sj.set("kind", kind);
        runs.push(sj);
        for n in &block {
            if !rejected.iter().any(|(k, _)| k == n) {
                rejected.push((n.clone(), (kind.to_string(), first_line(&msg))));
            }
        }
        if rec.kind == "thm" && !axioms.contains(&d) {
            axioms.insert(d);
        } else {
            axioms.remove(&d);
            drop.extend(block);
        }
        let nxt = work.join(format!("{label}.{}.ndjson", rnd + 1));
        dropped = export::rewrite(export, &nxt, &drop, &axioms)?;
        if cur != export {
            fs::remove_file(&cur)?;
        }
        cur = nxt;
    }
    if !finished {
        status = format!("stopped after {} rounds", cx.args.max_rounds);
    }
    if cur != export && cur.exists() {
        fs::remove_file(&cur)?;
    }
    let mut verdicts = Ordered::default();
    for n in index.constants() {
        let n = norm_name(n);
        let v = if let Some((_, (k, _))) = rejected.iter().find(|(r, _)| *r == n) {
            format!("reject:{k}")
        } else if dropped.contains(&n) {
            "skipped".into()
        } else if status != "complete" {
            "unknown".into()
        } else {
            "accept".into()
        };
        verdicts.insert(n, v);
    }
    let mut j = J::obj();
    j.set("label", label);
    j.set("status", status.as_str());
    j.set("runs", J::List(runs));
    j.set(
        "rejected",
        J::Obj(
            rejected
                .into_iter()
                .map(|(n, (k, m))| (n, J::List(vec![J::Str(k), J::Str(m)])))
                .collect(),
        ),
    );
    Ok(PerDecl {
        j,
        status,
        verdicts,
    })
}

fn single(
    label: &str,
    cmd: &[OsString],
    parse: fn(&str) -> Parsed,
    work: &Path,
    cx: &Ctx,
) -> Result<J> {
    let log = work.join(format!("{label}.log"));
    let st = run_limited(
        cmd,
        &log,
        cx.args.timeout,
        cx.args.mem_mib,
        cx.path.as_deref(),
        true,
    )?;
    let mut out = J::obj();
    out.set("label", label);
    out.set("runs", J::List(vec![run_json(&st)]));
    if st.status != "exited" {
        out.set("status", st.status.as_str());
        return Ok(out);
    }
    let (ok, decl, msg) = parse(&read_log(&log));
    if ok && st.exit == "0" {
        out.set("status", "accept");
    } else if st.exit == "1" || st.exit == "2" {
        out.set("status", "reject");
        out.set("decl", decl.map(|d| norm_name(&d)));
        out.set("kind", kind_of(&msg));
        out.set("message", first_line(&msg));
    } else {
        out.set("status", format!("error: exit {}", st.exit));
        out.set("message", util::truncate(&msg, 300));
    }
    Ok(out)
}

fn compare(lean: &Ordered, nitro: &Ordered) -> J {
    let mut agree = 0i64;
    let mut not_compared = 0i64;
    let (mut kind_differs, mut nor, mut noa) = (Vec::new(), Vec::new(), Vec::new());
    let s = |x: &str| J::Str(x.to_string());
    for (n, lv) in &lean.items {
        let nv = nitro.get(n).unwrap_or("unknown");
        let open = |v: &str| v == "skipped" || v == "unknown";
        if open(lv) || open(nv) {
            if lv == "skipped" && nv == "skipped" {
                agree += 1;
            } else {
                not_compared += 1;
            }
        } else if lv == nv {
            agree += 1;
        } else if lv == "accept" {
            nor.push(J::List(vec![s(n), s(nv)]));
        } else if nv == "accept" {
            noa.push(J::List(vec![s(n), s(lv)]));
        } else {
            agree += 1;
            kind_differs.push(J::List(vec![s(n), s(lv), s(nv)]));
        }
    }
    let mut c = J::obj();
    c.set("agree", agree);
    c.set("kind_differs", J::List(kind_differs));
    c.set("nitro_only_reject", J::List(nor));
    c.set("nitro_only_accept", J::List(noa));
    c.set("not_compared", not_compared);
    c
}

fn env_file(path: &Path) -> Result<HashMap<String, String>> {
    let mut out = HashMap::new();
    for line in fs::read_to_string(path)
        .with_context(|| format!("{}: cannot read", path.display()))?
        .lines()
    {
        if let Some((k, v)) = line.split_once('=') {
            out.insert(k.to_string(), v.to_string());
        }
    }
    Ok(out)
}

/// The bin directory of a toolchain, installing it quietly if needed.
pub fn toolchain_bin(tc: &str) -> Result<PathBuf> {
    let _ = Command::new("elan")
        .args(["toolchain", "install", tc])
        .output();
    Ok(util::lean_prefix(tc)?.join("bin"))
}

fn check_toolchain(tc: &str) -> String {
    let re = Regex::new(r"^leanprover/lean4:v4\.(\d+)\.").unwrap();
    match re.captures(tc).and_then(|m| m[1].parse::<u32>().ok()) {
        Some(minor) if minor < 35 => "leanprover/lean4:v4.36.0".into(),
        _ => tc.into(),
    }
}

fn cpu_count() -> i64 {
    // SAFETY: plain sysconf.
    let n = unsafe { libc::sysconf(libc::_SC_NPROCESSORS_ONLN) };
    if n > 0 { n as i64 } else { 1 }
}

/// Today's local date as YYYY-MM-DD.
fn today() -> String {
    // SAFETY: localtime_r writes into the local struct.
    unsafe {
        let t = libc::time(std::ptr::null_mut());
        let mut tm: libc::tm = std::mem::zeroed();
        libc::localtime_r(&t, &mut tm);
        format!(
            "{:04}-{:02}-{:02}",
            tm.tm_year + 1900,
            tm.tm_mon + 1,
            tm.tm_mday
        )
    }
}

fn os(s: impl Into<OsString>) -> OsString {
    s.into()
}

fn run_project(pid: &str, args: &RunArgs, out_root: &Path, nitro: &Path) -> Result<Option<J>> {
    let out = out_root.join(pid);
    let export = out.join("export.ndjson");
    if !export.exists() {
        eprintln!("{pid}: not built (run cargo xtask oracle build)");
        return Ok(None);
    }
    let b = env_file(&out.join("build.env"))?;
    let bget = |k: &str| -> Result<&String> {
        b.get(k)
            .ok_or_else(|| anyhow!("{}: no {k}", out.join("build.env").display()))
    };
    let work = out.join("work");
    let _ = fs::remove_dir_all(&work);
    fs::create_dir_all(&work)?;
    eprintln!("{pid}: indexing the export");
    let index = Index::new(&export)?;
    let toolchain = bget("toolchain")?.clone();
    let lean_tc = check_toolchain(&toolchain);
    let leanchecker = toolchain_bin(&lean_tc)?.join("leanchecker");
    let ncpu = cpu_count();
    let mut res = J::obj();
    res.set("id", pid);
    res.set("toolchain", toolchain.as_str());
    res.set("check_toolchain", lean_tc.as_str());
    res.set("commit", b.get("commit").cloned());
    res.set("constants", index.constants().count());
    res.set("records", index.decls.len());
    res.set("export_bytes", fs::metadata(&export)?.len());
    res.set("threads_all", ncpu);
    res.set("date", today());
    let cx = Ctx { args, path: None };
    eprintln!("{pid}: leanchecker ({lean_tc})");
    let lean = per_decl(
        "lean",
        &|f| vec![os(&leanchecker), os("--from-export"), os(f)],
        parse_lean,
        &export,
        &index,
        &work,
        &cx,
    )?;
    res.set("lean", lean.j.clone());
    let mut variants: Vec<(String, PerDecl)> = Vec::new();
    for (threads, name) in [(1, "export-1"), (0, "export-all")] {
        eprintln!(
            "{pid}: nitrolean, export, threads {}",
            if threads == 0 { ncpu } else { threads }
        );
        let v = per_decl(
            &format!("nitrolean-{name}"),
            &|f| {
                vec![
                    os(nitro),
                    os("check"),
                    os("--threads"),
                    os(threads.to_string()),
                    os(f),
                ]
            },
            parse_nitrolean,
            &export,
            &index,
            &work,
            &cx,
        )?;
        variants.push((name.to_string(), v));
    }
    let main = &variants[1].1;
    let one = &variants[0].1;
    res.set("nitrolean", main.j.clone());
    res.set("compare", compare(&lean.verdicts, &main.verdicts));
    let mut vj = J::obj();
    let mut e1 = one.j.clone();
    e1.set("identical", one.verdicts.same(&main.verdicts));
    vj.set("export-1", e1);
    let nitro_rejected: HashSet<&str> = main
        .verdicts
        .items
        .iter()
        .filter(|(_, v)| v.starts_with("reject:"))
        .map(|(n, _)| n.as_str())
        .collect();
    if toolchain == "leanprover/lean4:v4.36.0" {
        let cx = Ctx {
            args,
            path: Some(util::path_with(&toolchain_bin(&toolchain)?)),
        };
        let mut mods = Vec::new();
        for r in bget("roots")?.split(',') {
            mods.push(os("--module"));
            mods.push(os(r));
        }
        for (threads, name) in [(1, "olean-1"), (0, "olean-all")] {
            eprintln!(
                "{pid}: nitrolean, .olean, threads {}",
                if threads == 0 { ncpu } else { threads }
            );
            let mut cmd = vec![
                os(nitro),
                os("check"),
                os("--olean"),
                os("--threads"),
                os(threads.to_string()),
            ];
            cmd.extend(mods.iter().cloned());
            cmd.push(os(bget("project_dir")?));
            let mut o = single(
                &format!("nitrolean-{name}"),
                &cmd,
                parse_nitrolean,
                &work,
                &cx,
            )?;
            let identical = match o.str_of("status") {
                "accept" => nitro_rejected.is_empty() && main.status == "complete",
                "reject" => {
                    let d = o.str_of("decl").to_string();
                    matches!(o.get("decl"), Some(J::Str(_)))
                        && nitro_rejected.contains(d.as_str())
                        && main.verdicts.get(&d) == Some(&format!("reject:{}", o.str_of("kind")))
                }
                _ => false,
            };
            o.set("identical", identical);
            vj.set(name, o);
        }
    } else {
        let mut o = J::obj();
        o.set("status", "n/a");
        o.set("identical", J::Null);
        o.set(
            "message",
            format!(".olean files of {toolchain}; the reader supports Lean v4.36.0 only"),
        );
        vj.set("olean", o);
    }
    res.set("variants", vj);
    let mut tsv = String::from("constant\tlean\tnitrolean\n");
    for (n, lv) in &lean.verdicts.items {
        tsv.push_str(&format!(
            "{n}\t{lv}\t{}\n",
            main.verdicts.get(n).unwrap_or("unknown")
        ));
    }
    fs::write(out.join("verdicts.tsv"), tsv)?;
    fs::write(out.join("result.json"), res.dumps_indent1())?;
    if !args.keep_logs {
        let _ = fs::remove_dir_all(&work);
    }
    Ok(Some(res))
}

/// 1234567 as `1 234 567`.
fn num(n: i64) -> String {
    let s = n.unsigned_abs().to_string();
    let mut out = String::new();
    for (i, c) in s.chars().enumerate() {
        if i > 0 && (s.len() - i).is_multiple_of(3) {
            out.push(' ');
        }
        out.push(c);
    }
    if n < 0 { format!("-{out}") } else { out }
}

fn jint(j: Option<&J>) -> i64 {
    match j {
        Some(J::Int(i)) => *i,
        _ => 0,
    }
}

fn jfloat(j: Option<&J>) -> f64 {
    match j {
        Some(J::Float(f)) => *f,
        Some(J::Int(i)) => *i as f64,
        _ => 0.0,
    }
}

fn jlist(j: Option<&J>) -> &[J] {
    match j {
        Some(J::List(v)) => v,
        _ => &[],
    }
}

/// Python's `str()` of a JSON value, for the few that are printed.
fn jshow(j: Option<&J>) -> String {
    match j {
        None | Some(J::Null) => "None".into(),
        Some(J::Str(s)) => s.clone(),
        Some(J::Bool(b)) => if *b { "True" } else { "False" }.into(),
        Some(J::Int(i)) => i.to_string(),
        Some(J::Float(f)) => pyjson::py_float(*f),
        Some(other) => other.dumps_indent1(),
    }
}

/// A cell like `1.2 s, 345` (MiB).
fn fmt_run(r: &J) -> String {
    let st = &jlist(r.get("runs"))[0];
    let wall = jfloat(st.get("wall_s"));
    if st.str_of("status") != "exited" {
        return format!("{} after {wall:.0} s", st.str_of("status"));
    }
    let ts = if wall < 10.0 {
        format!("{wall:.2} s")
    } else if wall < 100.0 {
        format!("{wall:.1} s")
    } else {
        format!("{wall:.0} s")
    };
    format!("{ts}, {}", num(jint(st.get("peak_mib"))))
}

fn variant_cell(v: &J) -> String {
    let status = v.get("status");
    if status == Some(&J::Str("n/a".into())) {
        return "n/a".into();
    }
    let s = if !jlist(v.get("runs")).is_empty() {
        fmt_run(v)
    } else if status.is_some() {
        jshow(status)
    } else {
        String::new()
    };
    let mut verdict = match status {
        Some(J::Str(x)) if x == "complete" => String::new(),
        Some(J::Str(x)) if x == "accept" => "accepts".into(),
        None => String::new(),
        other => jshow(other),
    };
    if v.str_of("status") == "reject" {
        verdict = format!("rejects {}", jshow(v.get("decl")));
    }
    if let Some(J::Obj(r)) = v.get("rejected")
        && !r.is_empty()
    {
        verdict = format!("{} rejected", r.len());
    }
    if verdict.is_empty() {
        s
    } else {
        format!("{s}; {verdict}")
    }
}

fn write_results(results: &[J], path: &Path, nitro_version: &str) -> Result<()> {
    let mut rows = Vec::new();
    for r in results {
        let c = r.get("compare").unwrap();
        let mut notes = Vec::new();
        let kd = jlist(c.get("kind_differs")).len();
        if kd > 0 {
            notes.push(format!("{kd} with another error kind"));
        }
        let nc = jint(c.get("not_compared"));
        if nc != 0 {
            notes.push(format!("{nc} not compared (skipped or unknown)"));
        }
        for side in ["lean", "nitrolean"] {
            let st = r.get(side).unwrap().str_of("status");
            if st != "complete" {
                notes.push(format!("{side}: {}", util::truncate(st, 80)));
            }
        }
        rows.push(format!(
            "| {} | {} | {} | {} | {} | {} | {} | {} | {} |",
            r.str_of("id"),
            r.str_of("toolchain").rsplit(':').next().unwrap_or(""),
            num(jint(r.get("constants"))),
            num(jint(c.get("agree"))),
            jlist(c.get("nitro_only_reject")).len(),
            jlist(c.get("nitro_only_accept")).len(),
            fmt_run(r.get("nitrolean").unwrap()),
            fmt_run(r.get("lean").unwrap()),
            notes.join("; ")
        ));
    }
    let mut vrows = Vec::new();
    for r in results {
        let v = r.get("variants").unwrap();
        let mut cells = vec![
            variant_cell(r.get("nitrolean").unwrap()),
            variant_cell(v.get("export-1").unwrap()),
        ];
        if v.get("olean-all").is_some() {
            for k in ["olean-all", "olean-1"] {
                cells.push(variant_cell(v.get(k).unwrap()));
            }
        } else {
            cells.push("n/a (not Lean v4.36.0)".into());
            cells.push("n/a".into());
        }
        let ident = match v {
            J::Obj(items) => items
                .iter()
                .all(|(_, x)| x.get("identical") != Some(&J::Bool(false))),
            _ => true,
        };
        vrows.push(format!(
            "| {} | {} | {} |",
            r.str_of("id"),
            cells.join(" | "),
            if ident { "yes" } else { "NO" }
        ));
    }
    let mut mism = Vec::new();
    let pair = |x: &J, i: usize| match x {
        J::List(v) => jshow(v.get(i)),
        _ => String::new(),
    };
    for r in results {
        let c = r.get("compare").unwrap();
        let id = r.str_of("id");
        for x in jlist(c.get("nitro_only_accept")) {
            mism.push(format!(
                "- **soundness**: `{}` ({id}): nitrolean accepts, Lean {}",
                pair(x, 0),
                pair(x, 1)
            ));
        }
        for x in jlist(c.get("nitro_only_reject")) {
            mism.push(format!(
                "- `{}` ({id}): Lean accepts, nitrolean {}",
                pair(x, 0),
                pair(x, 1)
            ));
        }
        for x in jlist(c.get("kind_differs")) {
            mism.push(format!(
                "- `{}` ({id}): both reject, Lean {}, nitrolean {}",
                pair(x, 0),
                pair(x, 1),
                pair(x, 2)
            ));
        }
    }
    let (date, cores) = match results.first() {
        Some(r) => (
            r.str_of("date").to_string(),
            jint(r.get("threads_all")).to_string(),
        ),
        None => (String::new(), "?".into()),
    };
    let text = format!(
        "# Corpus oracle results

Written by `cargo xtask oracle run` ({date};
{nitro_version}, {cores} cores). How the verdicts are
obtained is in `README.md`. Times are wall-clock seconds and memory is peak resident MiB,
of the first run on the whole export (`check --threads 0` for nitrolean,
`leanchecker --from-export` for Lean).

| project | Lean | declarations | agree | nitrolean-only reject | nitrolean-only accept | nitrolean | leanchecker | notes |
| --- | --- | ---: | ---: | ---: | ---: | --- | --- | --- |
{}

## Variants

nitrolean's verdicts on each project from the NDJSON export and from the project's .olean
files, with all cores and with one thread. The .olean runs load the roots and everything
they import, the Lean core library included, so they check more than the export.

| project | NDJSON, all cores | NDJSON, 1 thread | .olean, all cores | .olean, 1 thread | identical |
| --- | --- | --- | --- | --- | --- |
{}

## Mismatches

{}
",
        rows.join("\n"),
        vrows.join("\n"),
        if mism.is_empty() {
            "None.".to_string()
        } else {
            mism.join("\n")
        }
    );
    fs::write(path, text).with_context(|| format!("{}: cannot write", path.display()))
}

/// The ids of projects.tsv with tier <= `tier`, or those in `only`.
fn run_projects(tier: i64, only: &[&str]) -> Result<Vec<String>> {
    let mut out = Vec::new();
    for line in fs::read_to_string(here().join("projects.tsv"))?.lines() {
        if line.starts_with('#') || line.trim().is_empty() {
            continue;
        }
        let cols: Vec<&str> = line.split('\t').collect();
        let sel = if !only.is_empty() {
            only.contains(&cols[0])
        } else {
            let t: i64 = cols
                .get(1)
                .and_then(|t| t.trim().parse().ok())
                .ok_or_else(|| anyhow!("projects.tsv: bad tier in {line}"))?;
            t <= tier
        };
        if sel {
            out.push(cols[0].to_string());
        }
    }
    Ok(out)
}

fn run_main(a: RunArgs) -> Result<()> {
    let out_root = a
        .out
        .clone()
        .unwrap_or_else(|| default_dir("ORACLE_OUT", "out"));
    let nitro_arg = a
        .nitrolean
        .clone()
        .unwrap_or_else(|| root().join("target/release/nitrolean"));
    let nitro = util::absolute(&nitro_arg);
    let only: Vec<&str> = a.only.split(',').filter(|s| !s.is_empty()).collect();
    let mut results = Vec::new();
    let mut bad = false;
    for pid in run_projects(a.tier, &only)? {
        let Some(r) = run_project(&pid, &a, &out_root, &nitro)? else {
            bad = true;
            continue;
        };
        let c = r.get("compare").unwrap();
        let item = |x: &J, i: usize| match x {
            J::List(v) => jshow(v.get(i)),
            _ => String::new(),
        };
        let noa = jlist(c.get("nitro_only_accept"));
        let nor = jlist(c.get("nitro_only_reject"));
        let kd = jlist(c.get("kind_differs"));
        for x in noa {
            println!(
                "SOUNDNESS {pid}: nitrolean accepts {}, Lean {}",
                item(x, 0),
                item(x, 1)
            );
        }
        for x in nor {
            println!(
                "MISMATCH {pid}: Lean accepts {}, nitrolean {}",
                item(x, 0),
                item(x, 1)
            );
        }
        for x in kd {
            println!(
                "KIND {pid}: {}: Lean {}, nitrolean {}",
                item(x, 0),
                item(x, 1),
                item(x, 2)
            );
        }
        if let Some(J::Obj(vs)) = r.get("variants") {
            for (k, v) in vs {
                if v.get("identical") == Some(&J::Bool(false)) {
                    let decl = match v.get("decl") {
                        None => String::new(),
                        d => jshow(d),
                    };
                    println!(
                        "VARIANT {pid}: {k} differs: {} {decl}",
                        jshow(v.get("status"))
                    );
                    bad = true;
                }
            }
        }
        bad |= !noa.is_empty() || !nor.is_empty() || !kd.is_empty();
        println!(
            "{pid}: {} constants, agree {}, nitrolean-only reject {}, nitrolean-only accept {}",
            jint(r.get("constants")),
            jint(c.get("agree")),
            nor.len(),
            noa.len()
        );
        results.push(r);
    }
    let ver = Command::new(&nitro_arg)
        .arg("--version")
        .output()
        .with_context(|| format!("cannot run {}", nitro_arg.display()))?;
    let ver = String::from_utf8_lossy(&ver.stdout).into_owned();
    let commit = Command::new("git")
        .arg("-C")
        .arg(root())
        .args(["rev-parse", "HEAD"])
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_default();
    if !results.is_empty() {
        let v = if commit.is_empty() {
            ver
        } else {
            format!("{} at {commit}", ver.trim())
        };
        let path = a
            .results
            .clone()
            .unwrap_or_else(|| here().join("RESULTS.md"));
        write_results(&results, &path, &v)?;
    }
    if bad {
        return Err(exit_with(1, ""));
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// cargo xtask oracle all

fn all(a: RunArgs) -> Result<()> {
    util::need("oracle", &["cargo"], " (see README.md)")?;
    util::run(
        util::cmd_in("cargo", &root())
            .args(["build", "--release", "--locked", "--bin", "nitrolean"])
            .stdout(stderr()?),
    )?;
    build(BuildArgs {
        tier: a.tier,
        only: a.only.clone(),
        out: None,
        cache: None,
        update_pins: false,
    })
    .map_err(|e| prefix_error("build", e))?;
    run_main(a)
}
