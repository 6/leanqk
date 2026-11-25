//! `cargo xtask kc ...`: the kernel-computation benchmarks of
//! bench/kernel-compute (see its README.md).
//!
//! Sources, build trees and checker binaries go under the cache directory
//! (`KC_CACHE`, default bench/kernel-compute/cache), generated exports and
//! tables under the output directory (`KC_OUT`, default
//! bench/kernel-compute/out); both are git-ignored. `--update-pins` (or
//! `KC_UPDATE_PINS=1`) reports a content hash that differs from the pinned
//! one instead of stopping.

use std::collections::{BTreeMap, HashMap};
use std::fs::{self, File};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use anyhow::{Context, Result, anyhow, bail};
use clap::Subcommand;

use crate::util::{
    self, absolute, cmd_in, content_sha256, copy_into, describe, exit_with, git, is_executable,
    path_with, print_tail, read_tsv, root, sha256_file, unlimited_stack, utc_hms,
};

// Toolchains (installed with elan) and the lean4export commit that matches each.
pub(crate) const TC_MAIN: &str = "leanprover/lean4:v4.34.0"; // the published project and Mathlib
const TC_CATCHER: &str = "leanprover/lean4:v4.30.0"; // its lean/catcher subproject, and LRAT-Catcher
const TC_CHECK: &str = "leanprover/lean4:v4.36.0"; // leanchecker, the toolchain nitrolean targets
const LEAN4EXPORT_URL: &str = "https://github.com/leanprover/lean4export";
pub(crate) const LEAN4EXPORT_434: &str = "076e8e57707e813375e8f9da8bf989799ace9680"; // "bump toolchain to v4.34.0"
const LEAN4EXPORT_430: &str = "a3e35a584f59b390667db7269cd37fca8575e4bf"; // "bump toolchain to v4.30.0"

const ZIP_URL: &str = "https://zenodo.org/records/24467489/files/steinberg-c4-c9-v9.zip";
const ZIP_SHA256: &str = "e5f60791343376f3974642d836e7c0daf5a143a232584662e3a221d481c7df73";

const CADICAL_COMMIT: &str = "4198d817d0dcde5b1240eefbff70b555b7df2af9"; // rel-2.2.1 (no factoring)
const CADICAL_SHA256: &str = "6f9781faa6a03049e0448761a50a5f327ecaae6b74336b66a6e073abb6af01a5";
const GBD: &str = "https://benchmark-database.de/file";

const GRUSZKA_COMMIT: &str = "43d2d1277e6dfa72572caa871c67ef15f78193e9";
const GRUSZKA_SHA256: &str = "23e8d6fda27cdf09d495bf9f20196feb9140b334c40bf321599a4634f8d38e3a";
const NANO_COMMIT: &str = "b5602a4ba169f6d4aef34fcdc3011fc41cd777e8";
const NANO_SHA256: &str = "fff9b5e9c34246b14f6e54bd781e213c4ced8b161fd73578d216cee1034f5f2c";
const SUSZ_VERSION: &str = "0.4.0";

#[derive(Subcommand)]
pub enum Cmd {
    /// Build the published planar-graph result and export its declarations' closure.
    ///
    /// The result is doi:10.5281/zenodo.24467489, taken from its released file
    /// steinberg-c4-c9-v9.zip (SHA-256 pinned) and nothing else: a Lean v4.34.0 +
    /// Mathlib project (the Mathlib revision is in its lake-manifest.json; the Mathlib
    /// .olean files come from `lake exe cache get`) and its `lean/catcher` subproject on
    /// Lean v4.30.0. Both are built unchanged, then exported with the lean4export commit
    /// that matches each toolchain.
    ///
    /// Writes, in OUT/zenodo: steinberg-main.ndjson (closure of the project's own
    /// declarations, Lean v4.34.0); steinberg-main-deps.ndjson (the same without the own
    /// declarations: closure of the constants they use directly; subtract the checking
    /// time of this from that of the full export to time the own ones);
    /// steinberg-main.own-names.txt (the own declarations: modules LocalRup, Steinberg,
    /// Check, PublishedInput, Challenge; names without `_` components); and
    /// steinberg-catcher*.ndjson, steinberg-catcher.own-names.txt, the same for
    /// lean/catcher (Lean v4.30.0; modules PublishedCatcher, RupPieces, PublishedInput).
    /// Needs curl, unzip, git, elan. Takes a few minutes; downloads about 6 GB of
    /// Mathlib build.
    FetchZenodo {
        #[command(flatten)]
        dirs: Dirs,
        /// Report a pinned hash that differs instead of stopping.
        #[arg(long)]
        update_pins: bool,
    },
    /// Kernel-only LRAT proofs of growing size, as exports.
    ///
    /// For each instance of data/lrat-instances.tsv (public SAT Competition instances,
    /// fetched by their hash from benchmark-database.de, content checked against a
    /// pinned SHA-256): solve it with the pinned CaDiCaL (`--lrat --no-binary`), trim
    /// the proof (`kc lrat-trim`), state it as a theorem with the `+kernel` mode of
    /// LRAT-Catcher (checker `LRATCatcher.checkKernel`, run by the kernel through
    /// `of_decide_eq_true (Eq.refl true)`), and export the theorem's closure with the
    /// lean4export that matches the toolchain (Lean v4.30.0).
    ///
    /// The theorem is added to the environment with `debug.skipKernelTC true`, which
    /// leaves out the kernel's check of the proof; checking it is what the exports are
    /// for. The term is built by BenchLrat.Cmd's `kernel_lrat`, which writes the same
    /// term as `lrat_reflect +kernel` without going through the elaborator. `base` is
    /// the same theorem for LRAT-Catcher's own 4-clause example, the export every other
    /// one contains.
    ///
    /// Then the same for the pigeonhole formulas of data/php-instances.tsv (PHP(n+1, n),
    /// made by LRAT-Catcher's examples/gen_php.py, refuted by the CaDiCaL of the v4.30.0
    /// toolchain).
    ///
    /// Writes OUT/lrat/NAME.ndjson and OUT/lrat/manifest.tsv (label, GBD hash, CNF
    /// bytes, LRAT bytes, export bytes, LRAT SHA-256). Needs git, curl, xz, make, a C++
    /// compiler, elan, python3.
    FetchLrat {
        #[command(flatten)]
        dirs: Dirs,
        /// Only these labels (comma-separated); the manifest keeps the rows of the others.
        #[arg(long, value_name = "LABEL,...")]
        only: Option<String>,
        /// Report a pinned hash that differs instead of stopping.
        #[arg(long)]
        update_pins: bool,
    },
    /// Export Mathlib declarations whose proofs are dominated by kernel computation.
    ///
    /// The 150 declarations are listed in data/mathlib-decide-names.txt. They are
    /// theorems of the Mathlib revision the published planar-graph result pins (so run
    /// `kc fetch-zenodo` first: this reuses its build), whose proof terms use
    /// `of_decide_eq_true` and are slow to check for their size: mostly matrix and
    /// finite-group computations. None depends on an axiom beyond propext,
    /// Classical.choice and Quot.sound (no native_decide).
    ///
    /// Writes, in OUT/mathlib: mathlib-decide.ndjson (the closure of the 150
    /// declarations, Lean v4.34.0), mathlib-decide-deps.ndjson (the closure of the
    /// constants they use directly, without them), mathlib-decide.names.txt (the 150
    /// names). The export is about 800 MB.
    FetchMathlibDecide {
        #[command(flatten)]
        dirs: Dirs,
        /// Instead, time the kernel on every Mathlib theorem whose proof uses
        /// `of_decide_eq_true` (about 780; a few minutes, timings vary by machine) and
        /// write the selection `kc select-decide` makes from that to
        /// OUT/mathlib/rerank.names.txt; data/mathlib-decide-names.txt is the
        /// selection from the run the baselines use.
        #[arg(long)]
        rerank: bool,
    },
    /// Build the four checkers that `kc measure` compares, each at a pinned commit.
    ///
    /// nitrolean is built from this checkout (or --nitrolean DIR), its commit
    /// recorded, not pinned; gruszka (github.com/jasisz/gruszka) with `susz`
    /// (crates.io, pinned version), which converts an export to the binary form gruszka
    /// reads; nano-lean (github.com/sdiehl/nano-lean), the `nl-fast` binary;
    /// leanchecker, the one of the Lean toolchain nitrolean targets (v4.36.0), not
    /// built but installed with elan.
    ///
    /// Writes CACHE/bin/{nitrolean,gruszka,susz,nl-fast,leanchecker} and
    /// CACHE/bin/versions.tsv. Needs git, curl, elan and a Rust toolchain; a checker
    /// that fails to build is reported and skipped, the others are still built.
    BuildCheckers {
        /// Sources, build trees and binaries.
        #[arg(long, value_name = "DIR")]
        cache: Option<PathBuf>,
        /// The nitrolean checkout to build (default: this one).
        #[arg(long, value_name = "DIR")]
        nitrolean: Option<PathBuf>,
        /// Report a pinned hash that differs instead of stopping.
        #[arg(long)]
        update_pins: bool,
    },
    /// Time the checkers on exports and write the results as a TSV.
    ///
    /// Columns: export, export_bytes, checker, limit_s, verdict, exit, wall_s,
    /// peak_rss_mib. verdict is accepted, rejected, timeout (over the limit), oom (over
    /// the memory limit), error (anything else: the checker could not read the export,
    /// crashed, ...) or unavailable (the checker was not built). The checker's output
    /// is kept in OUT/logs/. gruszka reads a binary form of the export: `susz pack`
    /// makes it once, outside the measured time, into CACHE/susz/. The memory limit is
    /// a limit on the resident set, sampled every 50 ms (`kc run-limited`).
    Measure {
        /// Wall-clock limit per run, in seconds.
        #[arg(long, default_value = "60", value_name = "SECONDS")]
        timeout: String,
        /// Resident-memory limit per run; a run above it is killed.
        #[arg(long, default_value_t = 4096, value_name = "MIB")]
        mem_mib: u64,
        /// Comma list from leanchecker,gruszka,nano-lean,nitrolean.
        #[arg(
            long,
            default_value = "leanchecker,gruszka,nano-lean,nitrolean",
            value_name = "LIST"
        )]
        checkers: String,
        /// The TSV (default: OUT/measurements.tsv); replaced unless --append.
        #[arg(long, value_name = "FILE")]
        out: Option<PathBuf>,
        /// Add to the TSV instead of replacing it.
        #[arg(long)]
        append: bool,
        /// Where `kc build-checkers` put the binaries.
        #[arg(long, value_name = "DIR")]
        cache: Option<PathBuf>,
        /// The exports.
        #[arg(value_name = "EXPORT.ndjson")]
        files: Vec<PathBuf>,
    },
    /// Summarize the TSV of `kc measure`.
    ///
    /// Prints, per export, each checker's verdict, wall time and peak resident memory,
    /// and, for the LRAT series (when its manifest is given), the largest LRAT each
    /// checker accepts within the 60 s and 4 GiB limits of the rows with limit_s 60.
    Summarize {
        measurements: PathBuf,
        lrat_manifest: Option<PathBuf>,
    },
    /// Run a command with a wall-clock limit and a resident-memory limit.
    ///
    /// The command runs under `/usr/bin/time -v`, its stdout and stderr go to LOGFILE,
    /// and one line is printed: STATUS<TAB>EXIT<TAB>WALL_SECONDS<TAB>PEAK_RSS_MIB.
    /// STATUS is `exited` (EXIT is the command's exit status), `timeout` or `oom`. The
    /// memory limit is enforced by sampling the resident set of the whole process group
    /// every 50 ms and killing it above the limit; `ulimit -v` is not used, because
    /// checkers that reserve address space up front (gruszka does) cannot start under it.
    RunLimited {
        timeout_seconds: f64,
        mem_mib: u64,
        logfile: PathBuf,
        #[arg(last = true, required = true)]
        command: Vec<String>,
    },
    /// Trim a text-format LRAT proof.
    ///
    /// Keeps only the lemmas the final empty clause depends on, drops deletion lines,
    /// and numbers the remaining lemmas consecutively after the clauses of the formula
    /// (the LRAT checker of the standard library requires consecutive ids). The result
    /// is a valid LRAT proof of the same formula.
    LratTrim { input: PathBuf, output: PathBuf },
    /// Choose the Mathlib declarations whose proofs are dominated by kernel computation.
    ///
    /// RANK.tsv is the output of lean/RankDecide.lean: per theorem whose proof term uses
    /// `of_decide_eq_true`, the time the kernel takes to check it and the number of
    /// distinct objects of its proof term. A proof that is small but slow to check is
    /// spending its time computing, so the theorems are ranked by nanoseconds per
    /// object, among those that take at least 1 ms, and the COUNT highest are printed,
    /// sorted by name.
    SelectDecide {
        rank: PathBuf,
        #[arg(default_value_t = 150)]
        count: usize,
    },
}

#[derive(clap::Args)]
pub struct Dirs {
    /// Where the exports go (default: $KC_OUT or bench/kernel-compute/out).
    #[arg(long, value_name = "DIR")]
    pub(crate) out: Option<PathBuf>,
    /// Sources and build trees (default: $KC_CACHE or bench/kernel-compute/cache).
    #[arg(long, value_name = "DIR")]
    pub(crate) cache: Option<PathBuf>,
}

pub fn main(c: Cmd) -> Result<()> {
    let name = match &c {
        Cmd::FetchZenodo { .. } => "fetch-zenodo",
        Cmd::FetchLrat { .. } => "fetch-lrat",
        Cmd::FetchMathlibDecide { .. } => "fetch-mathlib-decide",
        Cmd::BuildCheckers { .. } => "build-checkers",
        Cmd::Measure { .. } => "measure",
        Cmd::Summarize { .. } => "summarize",
        Cmd::RunLimited { .. } => "run-limited",
        Cmd::LratTrim { .. } => "lrat-trim",
        Cmd::SelectDecide { .. } => "select-decide",
    };
    let update_env = std::env::var("KC_UPDATE_PINS").is_ok_and(|v| v == "1");
    let r = match c {
        Cmd::FetchZenodo { dirs, update_pins } => {
            let k = Kc::new(name, &dirs, update_pins || update_env);
            fetch_zenodo(&k)
        }
        Cmd::FetchLrat {
            dirs,
            only,
            update_pins,
        } => {
            let k = Kc::new(name, &dirs, update_pins || update_env);
            fetch_lrat(&k, only.as_deref().unwrap_or(""))
        }
        Cmd::FetchMathlibDecide { dirs, rerank } => {
            let k = Kc::new(name, &dirs, update_env);
            fetch_mathlib_decide(&k, rerank)
        }
        Cmd::BuildCheckers {
            cache,
            nitrolean,
            update_pins,
        } => {
            let dirs = Dirs { out: None, cache };
            let k = Kc::new(name, &dirs, update_pins || update_env);
            build_checkers(&k, nitrolean.unwrap_or_else(root))
        }
        Cmd::Measure {
            timeout,
            mem_mib,
            checkers,
            out,
            append,
            cache,
            files,
        } => {
            let k = Kc::new(name, &Dirs { out: None, cache }, update_env);
            let tsv = out.unwrap_or_else(|| k.out.join("measurements.tsv"));
            measure(&k, &timeout, mem_mib, &checkers, &tsv, append, &files)
        }
        Cmd::Summarize {
            measurements,
            lrat_manifest,
        } => summarize(&measurements, lrat_manifest.as_deref()),
        Cmd::RunLimited {
            timeout_seconds,
            mem_mib,
            logfile,
            command,
        } => run_limited(timeout_seconds, mem_mib, &logfile, &command).map(|r| println!("{r}")),
        Cmd::LratTrim { input, output } => lrat_trim(&input, &output),
        Cmd::SelectDecide { rank, count } => select_decide(&rank, count).map(|names| {
            for n in names {
                println!("{n}");
            }
        }),
    };
    r.map_err(|e| match e.downcast::<util::Exit>() {
        Ok(x) => x.into(),
        Err(e) => exit_with(1, format!("{name}: error: {e:#}")),
    })
}

/// Where a command's output and messages go: ours, or a log file.
pub(crate) struct Io(pub(crate) Option<File>);

impl Io {
    /// Standard error, or the log; also for `>&2`.
    fn err(&self) -> Stdio {
        match &self.0 {
            Some(f) => f
                .try_clone()
                .map(Stdio::from)
                .unwrap_or_else(|_| Stdio::null()),
            None => stderr_stdio(),
        }
    }

    fn msg(&self, s: &str) {
        match &self.0 {
            Some(f) => {
                let _ = writeln!(&*f, "{s}");
            }
            None => eprintln!("{s}"),
        }
    }
}

fn stderr_stdio() -> Stdio {
    use std::os::fd::AsFd;
    std::io::stderr()
        .as_fd()
        .try_clone_to_owned()
        .map(Stdio::from)
        .unwrap_or_else(|_| Stdio::inherit())
}

/// The context of one command: its name, directories and pin policy.
pub(crate) struct Kc {
    name: &'static str,
    here: PathBuf,
    pub(crate) cache: PathBuf,
    pub(crate) out: PathBuf,
    update: bool,
}

impl Kc {
    pub(crate) fn new(name: &'static str, dirs: &Dirs, update: bool) -> Kc {
        let here = root().join("bench/kernel-compute");
        let env = |v: &str| {
            std::env::var_os(v)
                .filter(|s| !s.is_empty())
                .map(PathBuf::from)
        };
        let cache = dirs
            .cache
            .clone()
            .or_else(|| env("KC_CACHE"))
            .unwrap_or_else(|| here.join("cache"));
        let out = dirs
            .out
            .clone()
            .or_else(|| env("KC_OUT"))
            .unwrap_or_else(|| here.join("out"));
        Kc {
            name,
            here,
            cache,
            out,
            update,
        }
    }

    pub(crate) fn log(&self, io: &Io, msg: &str) {
        io.msg(&format!("{} {}: {msg}", utc_hms(), self.name));
    }

    fn need(&self, tools: &[&str]) -> Result<()> {
        for t in tools {
            if util::which(t).is_none() {
                bail!("{t} not found (see README.md)");
            }
        }
        Ok(())
    }

    /// A checkout of URL at COMMIT in CACHE/src/NAME (no history beyond that
    /// commit), checked against the pinned content hash.
    fn fetch_git(&self, io: &Io, name: &str, url: &str, commit: &str, want: &str) -> Result<()> {
        let dir = self.cache.join("src").join(name);
        if !dir.join(".git").is_dir() {
            let _ = fs::remove_dir_all(&dir);
            fs::create_dir_all(&dir)?;
            quiet(io, git(&dir).args(["init", "-q"]))?;
            quiet(io, git(&dir).args(["remote", "add", "origin", url]))?;
        }
        let have = git(&dir)
            .args(["cat-file", "-e", &format!("{commit}^{{commit}}")])
            .stderr(Stdio::null())
            .status()
            .is_ok_and(|s| s.success());
        if !have {
            self.log(io, &format!("fetching {name} at {commit}"));
            quiet(
                io,
                git(&dir).args(["fetch", "-q", "--depth", "1", "origin", commit]),
            )?;
        }
        quiet(
            io,
            git(&dir).args([
                "-c",
                "advice.detachedHead=false",
                "checkout",
                "-q",
                "--force",
                commit,
            ]),
        )?;
        quiet(io, git(&dir).args(["clean", "-qfdx"]))?;
        let head = util::output(git(&dir).args(["rev-parse", "HEAD"]))?;
        if head.trim() != commit {
            bail!("{name}: not at {commit}");
        }
        let got = content_sha256(&dir, &["."], &["./.git"])?;
        if got != want {
            if self.update {
                self.log(
                    io,
                    &format!("{name}: content SHA-256 is {got} (pinned: {want})"),
                );
            } else {
                bail!("{name}: content SHA-256 is {got}, expected {want}");
            }
        }
        Ok(())
    }

    /// lean4export built with the matching toolchain, in CACHE/lean4export-NAME.
    pub(crate) fn build_exporter(&self, name: &str, commit: &str, tc: &str) -> Result<PathBuf> {
        let dir = self.cache.join(format!("lean4export-{name}"));
        let exe = dir.join(".lake/build/bin/lean4export");
        if !is_executable(&exe) {
            let io = Io(None);
            let _ = fs::remove_dir_all(&dir);
            fs::create_dir_all(&dir)?;
            quiet(&io, git(&dir).args(["init", "-q"]))?;
            quiet(
                &io,
                git(&dir).args(["remote", "add", "origin", LEAN4EXPORT_URL]),
            )?;
            quiet(
                &io,
                git(&dir).args(["fetch", "-q", "--depth", "1", "origin", commit]),
            )?;
            quiet(
                &io,
                git(&dir).args(["-c", "advice.detachedHead=false", "checkout", "-q", commit]),
            )?;
            let have = read_trimmed(&dir.join("lean-toolchain"))?;
            if have != tc {
                bail!("lean4export {commit} is for {have}, not {tc}");
            }
            util::run(
                cmd_in("elan", &dir)
                    .args(["run", tc, "lake", "build"])
                    .stdout(stderr_stdio()),
            )?;
        }
        Ok(exe)
    }
}

/// Runs a command with its output going to `io` (stdout to stderr).
fn quiet(io: &Io, cmd: &mut Command) -> Result<()> {
    util::run(cmd.stdout(io.err()).stderr(io.err()))
}

/// The contents of a file without trailing newlines, as `$(cat FILE)`.
fn read_trimmed(p: &Path) -> Result<String> {
    Ok(fs::read_to_string(p)
        .with_context(|| format!("{}: cannot read", p.display()))?
        .trim_end_matches('\n')
        .to_string())
}

/// `elan toolchain install TC` (loudly to `io` if it fails quietly), then
/// the directory with the toolchain's lean, lake and leanchecker.
pub(crate) fn tc_bin(io: &Io, tc: &str) -> Result<PathBuf> {
    let ok = Command::new("elan")
        .args(["toolchain", "install", tc])
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|s| s.success());
    if !ok {
        quiet(io, Command::new("elan").args(["toolchain", "install", tc]))?;
    }
    let prefix = Command::new("elan")
        .args(["run", tc, "lean", "--print-prefix"])
        .stderr(io.err())
        .output()
        .context("cannot run elan")?;
    if !prefix.status.success() {
        bail!("elan run {tc} lean --print-prefix failed");
    }
    Ok(PathBuf::from(String::from_utf8_lossy(&prefix.stdout).trim()).join("bin"))
}

/// Downloads URL to FILE unless FILE already has that hash.
fn fetch_url(url: &str, want: &str, file: &Path) -> Result<()> {
    if file.is_file() && sha256_file(file)? == want {
        return Ok(());
    }
    if let Some(d) = file.parent() {
        fs::create_dir_all(d)?;
    }
    let part = PathBuf::from(format!("{}.part", file.display()));
    util::run(
        Command::new("curl")
            .args(["-fsSL", "--retry", "3", "-o"])
            .arg(&part)
            .arg(url),
    )?;
    if sha256_file(&part)? != want {
        bail!("{url}: SHA-256 mismatch");
    }
    fs::rename(&part, file)?;
    Ok(())
}

/// Runs the commands in turn with their output in LOG; on a failure prints
/// its last `tail` lines and fails with `msg`.
pub(crate) fn run_logged_seq(
    cmds: &mut [&mut Command],
    log: &Path,
    tail: usize,
    msg: &str,
) -> Result<()> {
    let f = File::create(log).with_context(|| format!("{}: cannot create", log.display()))?;
    for c in cmds.iter_mut() {
        let st = c
            .stdout(f.try_clone()?)
            .stderr(f.try_clone()?)
            .status()
            .with_context(|| format!("cannot run {}", describe(c)))?;
        if !st.success() {
            print_tail(log, tail);
            bail!("{msg}");
        }
    }
    Ok(())
}

/// Runs `cmd` with its standard output written to the file `out`.
pub(crate) fn run_to_file(cmd: &mut Command, out: &Path) -> Result<()> {
    let f = File::create(out).with_context(|| format!("{}: cannot create", out.display()))?;
    util::run(cmd.stdout(f))
}

/// The whitespace-separated words of a file, as `$(tr '\n' ' ' <FILE)`.
fn words_of(p: &Path) -> Result<Vec<String>> {
    Ok(fs::read_to_string(p)
        .with_context(|| format!("{}: cannot read", p.display()))?
        .split_whitespace()
        .map(String::from)
        .collect())
}

/// `lake env ARGS...` in `dir` with an unlimited stack.
pub(crate) fn lake_env(dir: &Path) -> Command {
    let mut c = cmd_in("lake", dir);
    c.arg("env");
    unlimited_stack(&mut c);
    c
}

// ---------------------------------------------------------------------------
// a. fetch-zenodo

fn fetch_zenodo(k: &Kc) -> Result<()> {
    let io = Io(None);
    k.need(&["curl", "unzip", "git", "elan"])?;
    let out = util::abs_dir(&k.out)?;
    fs::create_dir_all(out.join("zenodo"))?;
    let cache = util::abs_dir(&k.cache)?;
    let k = Kc {
        out,
        cache,
        ..Kc::new(
            k.name,
            &Dirs {
                out: None,
                cache: None,
            },
            k.update,
        )
    };
    let z = k.cache.join("zenodo");
    fetch_url(ZIP_URL, ZIP_SHA256, &z.join("steinberg-c4-c9-v9.zip"))?;
    if !z.join("project").is_dir() {
        k.log(&io, "unpacking");
        let unpack = z.join("unpack");
        let _ = fs::remove_dir_all(&unpack);
        fs::create_dir_all(&unpack)?;
        util::run(
            Command::new("unzip")
                .arg("-q")
                .arg(z.join("steinberg-c4-c9-v9.zip"))
                .arg("-d")
                .arg(&unpack),
        )?;
        fs::rename(
            unpack.join("steinberg-c4-c9-v9/results/steinberg-c4-c9"),
            z.join("project"),
        )?;
        fs::remove_dir_all(&unpack)?;
    }
    let lean = z.join("project/lean");
    let tc = read_trimmed(&lean.join("lean-toolchain"))?;
    if tc != TC_MAIN {
        bail!("unexpected toolchain {tc}");
    }
    if read_trimmed(&lean.join("catcher/lean-toolchain"))? != TC_CATCHER {
        bail!("unexpected catcher toolchain");
    }

    k.log(
        &io,
        &format!("main project: lake exe cache get, lake build ({TC_MAIN})"),
    );
    let _ = Command::new("elan")
        .args(["toolchain", "install", TC_MAIN, TC_CATCHER])
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status();
    run_logged_seq(
        &mut [
            cmd_in("lake", &lean).args(["exe", "cache", "get"]),
            cmd_in("lake", &lean).arg("build"),
        ],
        &z.join("build-main.log"),
        30,
        "building the main project failed",
    )?;
    k.log(&io, &format!("catcher subproject ({TC_CATCHER})"));
    run_logged_seq(
        &mut [cmd_in("lake", &lean.join("catcher")).arg("build")],
        &z.join("build-catcher.log"),
        30,
        "building lean/catcher failed",
    )?;

    let exp434 = k.build_exporter("434", LEAN4EXPORT_434, TC_MAIN)?;
    let exp430 = k.build_exporter("430", LEAN4EXPORT_430, TC_CATCHER)?;

    let export_set = |dir: &Path, exporter: &Path, name: &str, roots: &str, prefixes: &str| {
        let roots: Vec<&str> = roots.split_whitespace().collect();
        let prefixes: Vec<&str> = prefixes.split_whitespace().collect();
        let zo = k.out.join("zenodo");
        k.log(&io, &format!("{name}: own declarations"));
        let own = zo.join(format!("{name}.own-names.txt"));
        run_to_file(
            lake_env(dir)
                .args(["lean", "--run"])
                .arg(k.here.join("lean/ListOwn.lean"))
                .args(&roots)
                .arg("--")
                .args(&prefixes),
            &own,
        )?;
        k.log(&io, &format!("{name}: export"));
        run_to_file(
            lake_env(dir)
                .arg(exporter)
                .args(&roots)
                .arg("--")
                .args(words_of(&own)?),
            &zo.join(format!("{name}.ndjson")),
        )?;
        let deps = k
            .cache
            .join("zenodo")
            .join(format!("{name}.deps-names.txt"));
        run_to_file(
            lake_env(dir)
                .args(["lean", "--run"])
                .arg(k.here.join("lean/ListDeps.lean"))
                .args(&roots)
                .arg("--")
                .args(&prefixes),
            &deps,
        )?;
        run_to_file(
            lake_env(dir)
                .arg(exporter)
                .args(&roots)
                .arg("--")
                .args(words_of(&deps)?),
            &zo.join(format!("{name}-deps.ndjson")),
        )
    };
    export_set(
        &lean,
        &exp434,
        "steinberg-main",
        "Challenge Check PublishedInput",
        "LocalRup Steinberg Check PublishedInput Challenge",
    )?;
    export_set(
        &lean.join("catcher"),
        &exp430,
        "steinberg-catcher",
        "PublishedCatcher RupPieces PublishedInput",
        "PublishedCatcher RupPieces PublishedInput",
    )?;

    // Line and byte counts of what was written, as `wc -lc` prints them.
    let zo = k.out.join("zenodo");
    let mut files: Vec<String> = Vec::new();
    for suffix in [".own-names.txt", ".ndjson"] {
        let mut names: Vec<String> = fs::read_dir(&zo)?
            .filter_map(|e| e.ok())
            .map(|e| e.file_name().to_string_lossy().into_owned())
            .filter(|n| n.ends_with(suffix) && !n.starts_with('.'))
            .map(|n| format!("./{n}"))
            .collect();
        names.sort();
        files.extend(names);
    }
    let wc = cmd_in("wc", &zo).arg("-lc").args(&files).output()?;
    for l in String::from_utf8_lossy(&wc.stdout).lines() {
        eprintln!("  {l}");
    }
    k.log(&io, &format!("wrote {}", zo.display()));
    Ok(())
}

// ---------------------------------------------------------------------------
// b. fetch-lrat

fn fetch_lrat(k: &Kc, only: &str) -> Result<()> {
    let io = Io(None);
    k.need(&["git", "curl", "xz", "make", "c++", "elan", "python3"])?;
    let out = util::abs_dir(&k.out)?;
    fs::create_dir_all(out.join("lrat"))?;
    let cache = util::abs_dir(&k.cache)?;
    let k = Kc {
        out,
        cache,
        ..Kc::new(
            k.name,
            &Dirs {
                out: None,
                cache: None,
            },
            k.update,
        )
    };
    // SAFETY: no other thread runs yet; every program started from here on gets it.
    unsafe { std::env::set_var("LC_ALL", "C") };
    let selected =
        |label: &str| only.is_empty() || format!(",{only},").contains(&format!(",{label},"));

    k.log(&io, &format!("cadical {CADICAL_COMMIT}"));
    k.fetch_git(
        &io,
        "cadical",
        "https://github.com/arminbiere/cadical",
        CADICAL_COMMIT,
        CADICAL_SHA256,
    )?;
    let src = k.cache.join("src/cadical");
    let cadical = src.join("build/cadical");
    if !is_executable(&cadical) {
        util::run(cmd_in("./configure", &src).stdout(Stdio::null()))?;
        util::run(
            cmd_in("make", &src)
                .arg(format!("-j{}", util::nproc()))
                .stdout(Stdio::null())
                .stderr(Stdio::null()),
        )?;
    }

    k.log(
        &io,
        &format!("BenchLrat (LRAT-Catcher + kernel_lrat) on {TC_CATCHER}"),
    );
    let tcdir = tc_bin(&io, TC_CATCHER)?;
    let path = path_with(&tcdir);
    let proj = k.cache.join("lrat-kernel");
    let _ = fs::remove_dir_all(&proj);
    copy_into(&k.here.join("lean/lrat-kernel"), &proj, false)?;
    run_logged_seq(
        &mut [cmd_in(tcdir.join("lake"), &proj)
            .arg("build")
            .env("PATH", &path)],
        &k.cache.join("lrat-kernel-build.log"),
        30,
        "building lean/lrat-kernel failed",
    )?;
    let exporter = k.build_exporter("430", LEAN4EXPORT_430, TC_CATCHER)?;
    let leanpath = util::output(
        cmd_in(tcdir.join("lake"), &proj)
            .args(["env", "printenv", "LEAN_PATH"])
            .env("PATH", &path),
    )?
    .trim_end_matches('\n')
    .to_string();

    let work = k.cache.join("lrat-work");
    fs::create_dir_all(&work)?;
    let lrat_out = k.out.join("lrat");
    // One manifest row per label, so --only keeps the others.
    let rows = lrat_out.join(".rows");
    fs::create_dir_all(&rows)?;

    // States and exports the theorem for the pair.
    let export_one = |label: &str, cnf: &Path, lrat: &Path| -> Result<()> {
        let d = work.join(label);
        fs::create_dir_all(&d)?;
        let src = d.join(format!("Bench_{label}.lean"));
        fs::write(
            &src,
            format!(
                "import BenchLrat\nset_option debug.skipKernelTC true\nkernel_lrat bench_{label} \"{}\" \"{}\"\n",
                cnf.display(),
                lrat.display()
            ),
        )?;
        let mut c = cmd_in(tcdir.join("lake"), &proj);
        c.args(["env", "lean", "-R"])
            .arg(&d)
            .arg("-o")
            .arg(d.join(format!("Bench_{label}.olean")))
            .arg(&src)
            .env("PATH", &path);
        unlimited_stack(&mut c);
        util::run(&mut c)?;
        let mut c = cmd_in(&exporter, &proj);
        c.arg(format!("Bench_{label}"))
            .arg("--")
            .arg(format!("bench_{label}"))
            .env("LEAN_PATH", format!("{}:{leanpath}", d.display()))
            .env("PATH", &path);
        unlimited_stack(&mut c);
        run_to_file(&mut c, &lrat_out.join(format!("{label}.ndjson")))
    };
    let size = |p: &Path| util::file_size(p);
    let check = |label: &str, what: &str, got: &str, want: &str| -> Result<()> {
        if got != want && !k.update {
            bail!("{label}: {what} SHA-256 is {got}, expected {want}");
        }
        Ok(())
    };

    k.log(&io, "base");
    let tests = proj.join(".lake/packages/LRATCatcher/LRATCatcher/Tests");
    fs::copy(tests.join("tiny.cnf"), work.join("tiny.cnf"))?;
    fs::copy(tests.join("tiny.lrat"), work.join("tiny.lrat"))?;
    export_one("base", &work.join("tiny.cnf"), &work.join("tiny.lrat"))?;
    fs::write(
        rows.join("base"),
        format!(
            "base\t-\t{}\t{}\t{}\t{}\n",
            size(&work.join("tiny.cnf"))?,
            size(&work.join("tiny.lrat"))?,
            size(&lrat_out.join("base.ndjson"))?,
            sha256_file(&work.join("tiny.lrat"))?
        ),
    )?;

    for row in data_rows(&k.here.join("data/lrat-instances.tsv"))? {
        let [label, hash, cnf_sha, lrat_sha] = &row[..] else {
            bail!("bad row in data/lrat-instances.tsv");
        };
        if !selected(label) {
            continue;
        }
        let d = work.join(label);
        fs::create_dir_all(&d)?;
        k.log(&io, &format!("{label}: instance {hash}"));
        util::run(
            Command::new("curl")
                .args(["-fsSL", "--retry", "3", "-o"])
                .arg(d.join("f.xz"))
                .arg(format!("{GBD}/{hash}")),
        )?;
        run_to_file(
            Command::new("xz").arg("-dc").arg(d.join("f.xz")),
            &d.join("f.cnf"),
        )?;
        check(label, "CNF", &sha256_file(&d.join("f.cnf"))?, cnf_sha)?;
        solve(label, &cadical, &d)?;
        lrat_trim(&d.join("f.lrat"), &d.join("f.trim.lrat"))?;
        let got = sha256_file(&d.join("f.trim.lrat"))?;
        check(label, "LRAT", &got, lrat_sha)?;
        export_one(label, &d.join("f.cnf"), &d.join("f.trim.lrat"))?;
        fs::write(
            rows.join(label),
            format!(
                "{label}\t{hash}\t{}\t{}\t{}\t{got}\n",
                size(&d.join("f.cnf"))?,
                size(&d.join("f.trim.lrat"))?,
                size(&lrat_out.join(format!("{label}.ndjson")))?
            ),
        )?;
        // Large; regenerated deterministically.
        let _ = fs::remove_file(d.join("f.xz"));
        let _ = fs::remove_file(d.join("f.lrat"));
    }
    // The pigeonhole formulas PHP(n+1, n), from LRAT-Catcher's generator, refuted by
    // the CaDiCaL of the v4.30.0 toolchain (2.1.2): a second series, with one proof
    // family growing ~9x a step.
    let gen_php = proj.join(".lake/packages/LRATCatcher/examples/gen_php.py");
    for row in data_rows(&k.here.join("data/php-instances.tsv"))? {
        let [label, holes, cnf_sha, lrat_sha] = &row[..] else {
            bail!("bad row in data/php-instances.tsv");
        };
        if !selected(label) {
            continue;
        }
        let holes: u64 = holes
            .parse()
            .with_context(|| format!("{label}: bad holes"))?;
        let d = work.join(label);
        fs::create_dir_all(&d)?;
        k.log(&io, &format!("{label}: PHP({}, {holes})", holes + 1));
        run_to_file(
            Command::new("python3")
                .arg("-I")
                .arg(&gen_php)
                .arg((holes + 1).to_string())
                .arg(holes.to_string()),
            &d.join("f.cnf"),
        )?;
        solve(label, &tcdir.join("cadical"), &d)?;
        check(label, "cnf", &sha256_file(&d.join("f.cnf"))?, cnf_sha)?;
        check(label, "lrat", &sha256_file(&d.join("f.lrat"))?, lrat_sha)?;
        export_one(label, &d.join("f.cnf"), &d.join("f.lrat"))?;
        fs::write(
            rows.join(label),
            format!(
                "{label}\t-\t{}\t{}\t{}\t{}\n",
                size(&d.join("f.cnf"))?,
                size(&d.join("f.lrat"))?,
                size(&lrat_out.join(format!("{label}.ndjson")))?,
                sha256_file(&d.join("f.lrat"))?
            ),
        )?;
        let _ = fs::remove_file(d.join("f.lrat"));
    }

    // The rows, ordered by LRAT bytes (then bytewise, as `sort -t TAB -k4,4n`).
    let mut names: Vec<PathBuf> = fs::read_dir(&rows)?
        .filter_map(|e| e.ok())
        .filter(|e| !e.file_name().to_string_lossy().starts_with('.'))
        .map(|e| e.path())
        .collect();
    names.sort();
    let mut lines = Vec::new();
    for n in names {
        lines.extend(fs::read_to_string(&n)?.lines().map(String::from));
    }
    let key = |l: &str| -> u64 {
        let f = l.split('\t').nth(3).unwrap_or("");
        let digits: String = f
            .trim_start()
            .chars()
            .take_while(char::is_ascii_digit)
            .collect();
        digits.parse().unwrap_or(0)
    };
    lines.sort_by(|a, b| {
        key(a)
            .cmp(&key(b))
            .then_with(|| a.as_bytes().cmp(b.as_bytes()))
    });
    let mut text =
        String::from("label\tgbd_hash\tcnf_bytes\tlrat_bytes\texport_bytes\tlrat_sha256\n");
    for l in lines {
        text.push_str(&l);
        text.push('\n');
    }
    fs::write(lrat_out.join("manifest.tsv"), text)?;
    k.log(&io, &format!("wrote {}", lrat_out.display()));
    Ok(())
}

/// The data rows (after the header) of a pinned TSV, split on tabs (empty
/// cells dropped, as `IFS=$'\t' read` does).
fn data_rows(p: &Path) -> Result<Vec<Vec<String>>> {
    let text = fs::read_to_string(p).with_context(|| format!("{}: cannot read", p.display()))?;
    Ok(text
        .lines()
        .skip(1)
        .map(|l| {
            l.split('\t')
                .filter(|c| !c.is_empty())
                .map(String::from)
                .collect()
        })
        .collect())
}

/// `CADICAL -q --lrat --no-binary f.cnf f.lrat` in `d`: must exit 0 or 20
/// and say the formula is unsatisfiable.
fn solve(label: &str, cadical: &Path, d: &Path) -> Result<()> {
    let out = d.join("cadical.out");
    let mut c = Command::new(cadical);
    c.args(["-q", "--lrat", "--no-binary"])
        .arg(d.join("f.cnf"))
        .arg(d.join("f.lrat"))
        .stdout(File::create(&out)?);
    let st = c
        .status()
        .with_context(|| format!("cannot run {}", describe(&c)))?;
    if !st.success() && st.code() != Some(20) {
        bail!("{} failed ({st})", describe(&c));
    }
    let text = fs::read(&out)?;
    if !text
        .split(|&b| b == b'\n')
        .any(|l| l.starts_with(b"s UNSATISFIABLE"))
    {
        bail!("{label}: not unsatisfiable");
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// c. fetch-mathlib-decide

fn fetch_mathlib_decide(k: &Kc, rerank: bool) -> Result<()> {
    let io = Io(None);
    k.need(&["elan"])?;
    let out = util::abs_dir(&k.out)?;
    let ml = out.join("mathlib");
    fs::create_dir_all(&ml)?;
    let cache = fs::canonicalize(&k.cache).unwrap_or_else(|_| k.cache.clone());
    let k = Kc {
        out,
        cache,
        ..Kc::new(
            k.name,
            &Dirs {
                out: None,
                cache: None,
            },
            k.update,
        )
    };
    let lean = k.cache.join("zenodo/project/lean");
    if !lean.join(".lake/build").is_dir() {
        bail!("run `cargo xtask kc fetch-zenodo` first (it builds the Mathlib this uses)");
    }
    let exp434 = k.build_exporter("434", LEAN4EXPORT_434, TC_MAIN)?;

    if rerank {
        k.log(&io, "timing the kernel on the candidates");
        util::run(
            lake_env(&lean)
                .args(["lean", "--run"])
                .arg(k.here.join("lean/RankDecide.lean"))
                .arg(ml.join("rank.tsv"))
                .args(["Mathlib", "Mathlib"]),
        )?;
        let names = select_decide(&ml.join("rank.tsv"), 150)?;
        let mut text = String::new();
        for n in names {
            text.push_str(&n);
            text.push('\n');
        }
        fs::write(ml.join("rerank.names.txt"), text)?;
        k.log(
            &io,
            &format!("wrote {}", ml.join("rerank.names.txt").display()),
        );
        return Ok(());
    }

    let names = ml.join("mathlib-decide.names.txt");
    fs::copy(k.here.join("data/mathlib-decide-names.txt"), &names)?;
    k.log(&io, "dependencies of the declarations (and their axioms)");
    let deps = k.cache.join("mathlib-decide.deps-names.txt");
    run_to_file(
        lake_env(&lean)
            .args(["lean", "--run"])
            .arg(k.here.join("lean/ListDepsOfNames.lean"))
            .arg(&names)
            .arg("Mathlib"),
        &deps,
    )?;
    k.log(&io, "export");
    run_to_file(
        lake_env(&lean)
            .arg(&exp434)
            .args(["Mathlib", "--"])
            .args(words_of(&names)?),
        &ml.join("mathlib-decide.ndjson"),
    )?;
    run_to_file(
        lake_env(&lean)
            .arg(&exp434)
            .args(["Mathlib", "--"])
            .args(words_of(&deps)?),
        &ml.join("mathlib-decide-deps.ndjson"),
    )?;
    let _ = Command::new("ls")
        .arg("-l")
        .arg(&ml)
        .stdout(stderr_stdio())
        .status();
    k.log(&io, &format!("wrote {}", ml.display()));
    Ok(())
}

// ---------------------------------------------------------------------------
// build-checkers

fn build_checkers(k: &Kc, nitrolean: PathBuf) -> Result<()> {
    k.need(&["git", "curl", "elan", "cargo"])?;
    let cache = util::abs_dir(&k.cache.join("bin"))?
        .parent()
        .expect("bin has a parent")
        .to_path_buf();
    let k = Kc {
        cache,
        ..Kc::new(
            k.name,
            &Dirs {
                out: None,
                cache: None,
            },
            k.update,
        )
    };
    let bin = k.cache.join("bin");
    let versions = bin.join("versions.tsv");
    fs::write(&versions, "")?;
    let ver = |name: &str, v: &str| -> Result<()> {
        let mut f = fs::OpenOptions::new().append(true).open(&versions)?;
        writeln!(f, "{name}\t{v}")?;
        Ok(())
    };
    let cargo_release = |dir: &Path, target: &str, io: &Io, extra: &[&str]| -> Result<()> {
        quiet(
            io,
            cmd_in("cargo", dir)
                .args(["build", "--release", "--locked"])
                .args(extra)
                .env("CARGO_TARGET_DIR", k.cache.join("target").join(target)),
        )
    };
    let copy = |from: PathBuf, to: &str| -> Result<()> {
        let dst = bin.join(to);
        let _ = fs::remove_file(&dst);
        fs::copy(&from, &dst).with_context(|| format!("cannot copy {}", from.display()))?;
        Ok(())
    };

    // Runs a step with its output in CACHE/build-NAME.log; a failure is
    // reported instead of stopping.
    let try_step = |name: &str, f: &dyn Fn(&Io) -> Result<()>| -> Result<()> {
        let log = k.cache.join(format!("build-{name}.log"));
        let io = Io(Some(File::create(&log)?));
        let r = f(&io);
        let stderr = Io(None);
        match r {
            Ok(()) => k.log(&stderr, &format!("{name}: built")),
            Err(e) => {
                io.msg(&format!("build-checkers: error: {e:#}"));
                k.log(
                    &stderr,
                    &format!("{name}: BUILD FAILED (log: {})", log.display()),
                );
                ver(name, "build failed")?;
            }
        }
        Ok(())
    };

    try_step("leanchecker", &|io| {
        let d = tc_bin(io, TC_CHECK)?;
        let link = bin.join("leanchecker");
        let _ = fs::remove_file(&link);
        std::os::unix::fs::symlink(d.join("leanchecker"), &link)?;
        let v = Command::new(d.join("lean"))
            .arg("--version")
            .stderr(io.err())
            .output()?;
        ver(
            "leanchecker",
            String::from_utf8_lossy(&v.stdout).trim_end_matches('\n'),
        )
    })?;
    try_step("nitrolean", &|io| {
        cargo_release(&nitrolean, "nitrolean", io, &[])?;
        copy(
            k.cache.join("target/nitrolean/release/nitrolean"),
            "nitrolean",
        )?;
        let rev = git(&nitrolean)
            .args(["rev-parse", "HEAD"])
            .stderr(Stdio::null())
            .output()
            .ok()
            .filter(|o| o.status.success())
            .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
            .unwrap_or_else(|| "unknown".into());
        ver("nitrolean", &rev)
    })?;
    try_step("gruszka", &|io| {
        k.fetch_git(
            io,
            "gruszka",
            "https://github.com/jasisz/gruszka",
            GRUSZKA_COMMIT,
            GRUSZKA_SHA256,
        )?;
        cargo_release(&k.cache.join("src/gruszka"), "gruszka", io, &[])?;
        copy(k.cache.join("target/gruszka/release/gruszka"), "gruszka")?;
        ver("gruszka", GRUSZKA_COMMIT)?;
        quiet(
            io,
            Command::new("cargo")
                .args([
                    "install",
                    "susz",
                    "--version",
                    SUSZ_VERSION,
                    "--locked",
                    "--root",
                ])
                .arg(k.cache.join("susz"))
                .env("CARGO_TARGET_DIR", k.cache.join("target/susz")),
        )?;
        copy(k.cache.join("susz/bin/susz"), "susz")?;
        ver("susz", SUSZ_VERSION)
    })?;
    try_step("nano-lean", &|io| {
        k.fetch_git(
            io,
            "nano-lean",
            "https://github.com/sdiehl/nano-lean",
            NANO_COMMIT,
            NANO_SHA256,
        )?;
        cargo_release(
            &k.cache.join("src/nano-lean"),
            "nano",
            io,
            &["--bin", "nl-fast"],
        )?;
        copy(k.cache.join("target/nano/release/nl-fast"), "nl-fast")?;
        ver("nano-lean", NANO_COMMIT)
    })?;
    print!("{}", fs::read_to_string(&versions)?);
    Ok(())
}

// ---------------------------------------------------------------------------
// measure

#[allow(clippy::too_many_arguments)]
pub(crate) fn measure(
    k: &Kc,
    timeout: &str,
    mem_mib: u64,
    checkers: &str,
    tsv: &Path,
    append: bool,
    files: &[PathBuf],
) -> Result<()> {
    let io = Io(None);
    if files.is_empty() {
        bail!("no exports given");
    }
    let limit: f64 = timeout
        .parse()
        .map_err(|_| anyhow!("--timeout {timeout}: not a number"))?;
    let bin = k.cache.join("bin");
    let logs = k.out.join("logs");
    fs::create_dir_all(&logs)?;
    if let Some(d) = tsv.parent().filter(|d| !d.as_os_str().is_empty()) {
        fs::create_dir_all(d)?;
    }
    let susz_dir = k.cache.join("susz");
    fs::create_dir_all(&susz_dir)?;
    if !(append && tsv.is_file()) {
        fs::write(
            tsv,
            "export\texport_bytes\tchecker\tlimit_s\tverdict\texit\twall_s\tpeak_rss_mib\n",
        )?;
    }
    let row = |line: String| -> Result<()> {
        let mut f = fs::OpenOptions::new().append(true).open(tsv)?;
        writeln!(f, "{line}")?;
        Ok(())
    };

    for f in files {
        if !f.is_file() {
            bail!("{}: no such file", f.display());
        }
        let f = absolute(f);
        let base = f
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_default();
        let name = match base.strip_suffix(".ndjson") {
            Some(s) if !s.is_empty() => s.to_string(),
            _ => base.clone(),
        };
        let bytes = util::file_size(&f)?;
        for c in checkers.split(',').filter(|c| !c.is_empty()) {
            let mut exe = bin.join(c);
            let mut cmd: Vec<std::ffi::OsString> = Vec::new();
            let mut susz_ok = true;
            match c {
                "leanchecker" => {
                    cmd = vec![exe.clone().into(), "--from-export".into(), f.clone().into()]
                }
                "nitrolean" => cmd = vec![exe.clone().into(), "check".into(), f.clone().into()],
                "nano-lean" => {
                    exe = bin.join("nl-fast");
                    cmd = vec![exe.clone().into(), f.clone().into()];
                }
                "gruszka" => {
                    exe = bin.join("gruszka");
                    let susz = susz_dir.join(format!("{name}.susz"));
                    if is_executable(&bin.join("susz")) {
                        if !susz.is_file() {
                            let log = File::create(logs.join(format!("{name}.susz-pack.log")))?;
                            let ok = Command::new(bin.join("susz"))
                                .args(["pack", "--no-index"])
                                .arg(&f)
                                .arg(&susz)
                                .stdout(log.try_clone()?)
                                .stderr(log)
                                .status()
                                .is_ok_and(|s| s.success());
                            if !ok {
                                let _ = fs::remove_file(&susz);
                            }
                        }
                        cmd = vec![exe.clone().into(), susz.clone().into()];
                    }
                    susz_ok = susz.is_file();
                }
                _ => bail!("unknown checker {c}"),
            }
            if !is_executable(&exe) || cmd.is_empty() || !susz_ok {
                row(format!(
                    "{name}\t{bytes}\t{c}\t{timeout}\tunavailable\t\t\t"
                ))?;
                continue;
            }
            k.log(
                &io,
                &format!("{name}: {c} (limit {timeout}s, {mem_mib} MiB)"),
            );
            let logf = logs.join(format!("{name}.{c}.t{timeout}.log"));
            let r = run_limited_os(limit, mem_mib, &logf, &cmd, false)?;
            let v = verdict(c, &r.status, &r.code, &logf)?;
            row(format!(
                "{name}\t{bytes}\t{c}\t{timeout}\t{v}\t{}\t{}\t{}",
                r.code, r.wall, r.peak
            ))?;
        }
    }
    k.log(&io, &format!("wrote {}", tsv.display()));
    Ok(())
}

/// The verdict of a checker's run from its status, exit code and log.
fn verdict(checker: &str, status: &str, code: &str, log: &Path) -> Result<&'static str> {
    if status == "timeout" {
        return Ok("timeout");
    }
    if status == "oom" {
        return Ok("oom");
    }
    let text = fs::read(log).unwrap_or_default();
    let text = String::from_utf8_lossy(&text);
    let has = |s: &str| text.contains(s);
    let line_starts = |s: &str| text.lines().any(|l| l.starts_with(s));
    Ok(match checker {
        "leanchecker" => {
            if has("accepts the solution") {
                "accepted"
            } else if code == "1" {
                "rejected"
            } else {
                "error"
            }
        }
        "nitrolean" => {
            if line_starts("accepted") {
                "accepted"
            } else if line_starts("rejected") || line_starts("nitrolean: rejected") {
                "rejected"
            } else {
                "error"
            }
        }
        "gruszka" => {
            // `tail -n1`: the last line.
            let body = text.strip_suffix('\n').unwrap_or(&text);
            let last = body.rsplit('\n').next().unwrap_or("");
            let lower = text.to_lowercase();
            if last == "accepted" {
                "accepted"
            } else if lower.contains("rejected") || lower.contains("failed") {
                "rejected"
            } else {
                "error"
            }
        }
        "nano-lean" => {
            if code == "0" && has(" 0 failures") {
                "accepted"
            } else if code == "1" {
                "rejected"
            } else {
                "error"
            }
        }
        _ => "error",
    })
}

// ---------------------------------------------------------------------------
// run-limited

/// The line `kc run-limited` prints, in its parts.
pub(crate) struct Limited {
    pub(crate) status: String,
    pub(crate) code: String,
    pub(crate) wall: String,
    pub(crate) peak: String,
}

impl std::fmt::Display for Limited {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}\t{}\t{}\t{}",
            self.status, self.code, self.wall, self.peak
        )
    }
}

fn run_limited(timeout: f64, mem_mib: u64, log: &Path, cmd: &[String]) -> Result<Limited> {
    let cmd: Vec<std::ffi::OsString> = cmd.iter().map(Into::into).collect();
    run_limited_os(timeout, mem_mib, log, &cmd, false)
}

/// Runs `cmd` under `/usr/bin/time -v` in its own process group with its
/// output in `log`, killing it past `timeout` seconds or when its resident
/// memory goes over `mem_mib`; with `stack_unlimited`, its soft stack limit is
/// raised to the hard one.
pub(crate) fn run_limited_os(
    timeout: f64,
    mem_mib: u64,
    log: &Path,
    cmd: &[std::ffi::OsString],
    stack_unlimited: bool,
) -> Result<Limited> {
    let r = crate::limited::run_limited(cmd, log, timeout, mem_mib as i64, None, stack_unlimited)?;
    Ok(Limited {
        status: r.status,
        code: r.exit,
        wall: format!("{:.2}", r.wall_s),
        peak: r.peak_mib.to_string(),
    })
}

// ---------------------------------------------------------------------------
// summarize

fn summarize(measurements: &Path, manifest_path: Option<&Path>) -> Result<()> {
    let rows = read_tsv(measurements)?;
    let get = |r: &HashMap<String, String>, c: &str| -> Result<String> {
        r.get(c)
            .cloned()
            .ok_or_else(|| anyhow!("{}: a row has no {c}", measurements.display()))
    };
    let mut checkers: Vec<String> = Vec::new();
    for r in &rows {
        let c = get(r, "checker")?;
        if !checkers.contains(&c) {
            checkers.push(c);
        }
    }
    type Row = HashMap<String, String>;
    let mut by: BTreeMap<(String, i64, String), HashMap<String, &Row>> = BTreeMap::new();
    for r in &rows {
        let limit = get(r, "limit_s")?;
        let n: i64 = limit
            .trim()
            .parse()
            .map_err(|_| anyhow!("limit_s {limit}: not an integer"))?;
        by.entry((get(r, "export")?, n, limit))
            .or_default()
            .insert(get(r, "checker")?, r);
    }
    let mut manifest: HashMap<String, HashMap<String, String>> = HashMap::new();
    if let Some(p) = manifest_path {
        for r in read_tsv(p)? {
            manifest.insert(get(&r, "label")?, r);
        }
    }
    println!("export (LRAT bytes) @limit | {}", checkers.join(" | "));
    for ((export, _, limit), per) in &by {
        let size = manifest
            .get(export)
            .and_then(|m| m.get("lrat_bytes"))
            .map(String::as_str)
            .unwrap_or("");
        let mut cells = Vec::new();
        for c in &checkers {
            match per.get(c) {
                None => cells.push("-".to_string()),
                Some(r) => {
                    let v = get(r, "verdict")?;
                    if ["accepted", "rejected", "error"].contains(&v.as_str()) {
                        let wall: f64 = get(r, "wall_s")?
                            .trim()
                            .parse()
                            .map_err(|_| anyhow!("wall_s of {export}: not a number"))?;
                        cells.push(format!("{v} {wall:.1}s {}MiB", get(r, "peak_rss_mib")?));
                    } else {
                        cells.push(v);
                    }
                }
            }
        }
        println!("{export} ({size}) @{limit}s | {}", cells.join(" | "));
    }
    if !manifest.is_empty() {
        println!();
        for c in &checkers {
            let mut best: Option<(u64, String)> = None;
            for ((export, _, limit), per) in &by {
                let Some(r) = per.get(c) else { continue };
                if limit == "60"
                    && get(r, "verdict")? == "accepted"
                    && export != "base"
                    && let Some(m) = manifest.get(export)
                {
                    let n: u64 = m
                        .get("lrat_bytes")
                        .and_then(|s| s.trim().parse().ok())
                        .ok_or_else(|| anyhow!("{export}: bad lrat_bytes"))?;
                    let cand = (n, export.clone());
                    best = Some(match best {
                        Some(b) if b >= cand => b,
                        _ => cand,
                    });
                }
            }
            let what = match best {
                Some((n, e)) => format!("{n} bytes ({e})"),
                None => "none".into(),
            };
            println!("largest LRAT {c} accepts within 60 s and 4 GiB: {what}");
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// lrat-trim, select-decide

fn lrat_trim(input: &Path, output: &Path) -> Result<()> {
    let text =
        fs::read_to_string(input).with_context(|| format!("{}: cannot read", input.display()))?;
    let int =
        |s: &str| -> Result<i64> { s.parse().map_err(|_| anyhow!("lrat_trim: bad number {s}")) };
    // (id, hint ids, tokens) of the addition lines, in file order
    let mut lines: Vec<(i64, Vec<i64>, Vec<&str>)> = Vec::new();
    for raw in text.split_inclusive('\n') {
        let tok: Vec<&str> = raw.split_whitespace().collect();
        if tok.len() < 3 || tok[1] == "d" {
            continue;
        }
        let z = tok
            .iter()
            .position(|t| *t == "0")
            .ok_or_else(|| anyhow!("lrat_trim: no 0 in a line"))?;
        let hints = tok
            .get(z + 1..tok.len() - 1)
            .unwrap_or(&[])
            .iter()
            .map(|h| int(h).map(i64::abs))
            .collect::<Result<_>>()?;
        lines.push((int(tok[0])?, hints, tok));
    }
    match lines.last() {
        Some((id, _, tok)) if *id != 0 && tok.len() >= 2 && tok[1] == "0" => {}
        _ => {
            return Err(exit_with(
                1,
                "lrat_trim: the proof does not end with the empty clause",
            ));
        }
    }
    let mut needed = std::collections::HashSet::new();
    needed.insert(lines.last().unwrap().0);
    let mut keep = Vec::new();
    for l in lines.iter().rev() {
        if needed.contains(&l.0) {
            needed.extend(l.1.iter().copied());
            keep.push(l);
        }
    }
    keep.reverse();
    let first = lines[0].0; // the formula's clauses are 1 .. first - 1
    let new: HashMap<i64, i64> = keep
        .iter()
        .enumerate()
        .map(|(i, l)| (l.0, first + i as i64))
        .collect();
    let mut out = String::new();
    for (cid, _, tok) in keep {
        let z = tok.iter().position(|t| *t == "0").unwrap();
        let mut parts = vec![new[cid].to_string()];
        parts.extend(tok[1..=z].iter().map(|s| s.to_string()));
        for h in tok.get(z + 1..tok.len() - 1).unwrap_or(&[]) {
            let h = int(h)?;
            let sign = if h > 0 { 1 } else { -1 };
            parts.push((sign * new.get(&h.abs()).copied().unwrap_or(h.abs())).to_string());
        }
        parts.push("0".into());
        out.push_str(&parts.join(" "));
        out.push('\n');
    }
    fs::write(output, out).with_context(|| format!("{}: cannot write", output.display()))
}

fn select_decide(rank: &Path, count: usize) -> Result<Vec<String>> {
    let text =
        fs::read_to_string(rank).with_context(|| format!("{}: cannot read", rank.display()))?;
    let mut rows: Vec<(f64, String)> = Vec::new();
    for line in text.split_inclusive('\n') {
        let line = line.strip_suffix('\n').unwrap_or(line);
        let f: Vec<&str> = line.split('\t').collect();
        let [name, ns, _module, ok, objs] = f[..] else {
            bail!("select_decide: bad line: {line}");
        };
        let ns: i64 = ns.trim().parse().map_err(|_| anyhow!("bad time {ns}"))?;
        let objs: i64 = objs
            .trim()
            .parse()
            .map_err(|_| anyhow!("bad count {objs}"))?;
        if ok == "true" && ns >= 1_000_000 && objs > 0 {
            rows.push((ns as f64 / objs as f64, name.to_string()));
        }
    }
    rows.sort_by(|a, b| b.0.total_cmp(&a.0).then_with(|| a.1.cmp(&b.1)));
    let mut names: Vec<String> = rows.into_iter().take(count).map(|r| r.1).collect();
    names.sort();
    Ok(names)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tmp(name: &str) -> PathBuf {
        let d = std::env::temp_dir().join(format!("kc-test-{}-{name}", std::process::id()));
        fs::create_dir_all(&d).unwrap();
        d
    }

    #[test]
    fn trims_lrat() {
        let d = tmp("trim");
        // Lemma 5 is not needed for the empty clause 7; 6 and 7 are renumbered.
        fs::write(
            d.join("in.lrat"),
            "5 1 0 1 2 0\n5 d 1 0\n6 2 0 3 -4 0\n7 0 6 1 0\n",
        )
        .unwrap();
        lrat_trim(&d.join("in.lrat"), &d.join("out.lrat")).unwrap();
        assert_eq!(
            fs::read_to_string(d.join("out.lrat")).unwrap(),
            "5 2 0 3 -4 0\n6 0 5 1 0\n"
        );
        fs::remove_dir_all(d).unwrap();
    }

    #[test]
    fn selects_decide() {
        let d = tmp("select");
        fs::write(
            d.join("rank.tsv"),
            "b\t2000000\tM\ttrue\t2\na\t2000000\tM\ttrue\t2\nc\t500\tM\ttrue\t1\nd\t9000000\tM\tfalse\t1\ne\t3000000\tM\ttrue\t1\n",
        )
        .unwrap();
        assert_eq!(select_decide(&d.join("rank.tsv"), 2).unwrap(), ["a", "e"]);
        fs::remove_dir_all(d).unwrap();
    }

    #[test]
    fn verdicts() {
        let d = tmp("verdict");
        let log = d.join("log");
        fs::write(&log, "x\naccepted\n").unwrap();
        assert_eq!(verdict("gruszka", "exited", "0", &log).unwrap(), "accepted");
        assert_eq!(
            verdict("nitrolean", "exited", "0", &log).unwrap(),
            "accepted"
        );
        assert_eq!(verdict("nitrolean", "oom", "", &log).unwrap(), "oom");
        fs::write(
            &log,
            "nitrolean: rejected: declaration 'x': type mismatch\n",
        )
        .unwrap();
        assert_eq!(
            verdict("nitrolean", "exited", "1", &log).unwrap(),
            "rejected"
        );
        fs::write(&log, "Check FAILED\nmore\n").unwrap();
        assert_eq!(verdict("gruszka", "exited", "1", &log).unwrap(), "rejected");
        assert_eq!(
            verdict("leanchecker", "exited", "1", &log).unwrap(),
            "rejected"
        );
        assert_eq!(
            verdict("leanchecker", "exited", "3", &log).unwrap(),
            "error"
        );
        fs::remove_dir_all(d).unwrap();
    }
}
