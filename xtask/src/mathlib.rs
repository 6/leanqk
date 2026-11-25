//! `cargo xtask mathlib ...`: the benchmark on all of Mathlib.
//!
//!   fetch     build the NDJSON export of Mathlib v4.36.0
//!   run       time a checker on an export at several thread counts
//!
//! `fetch` clones Mathlib at the v4.36.0 tag, fetches its prebuilt .olean
//! files with `lake exe cache get` and runs the `leanexport` of the pinned
//! toolchain: about five minutes and 14 GB of memory once the cache is
//! downloaded. Needs git and elan. `run` prints one tab-separated line per
//! thread count: checker, threads, wall seconds, CPU seconds (user and
//! system), peak RSS in MiB, exit status and the checker's last line of
//! output.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use anyhow::{Context, Result, bail};
use clap::{Args, Subcommand, ValueEnum};

use crate::proc::run_timed;
use crate::util::{absolute, elan_install, git, log, need, nproc, output, root, sha256_file};

/// Mathlib's v4.36.0 tag.
const MATHLIB_URL: &str = "https://github.com/leanprover-community/mathlib4";
const MATHLIB_REV: &str = "fc4f59e577feb1a4956671bc04ac18aaaf8cd842";
/// The export `fetch` makes: 6,326,141,213 bytes, 112,081,718 lines.
const EXPORT_SHA256: &str = "f749dfd084fc0727d107c7aaded7d492cebfc0b517cfaa7337d8a7578a6c0dec";

#[derive(Subcommand)]
pub enum Cmd {
    /// Build the NDJSON export of Mathlib v4.36.0 and check its SHA-256.
    Fetch(FetchArgs),
    /// Time a checker on an export at several thread counts.
    Run(RunArgs),
}

#[derive(Args)]
pub struct FetchArgs {
    /// Where the export goes.
    out: PathBuf,
    /// Mathlib's checkout (default: a mathlib4 directory next to OUT).
    #[arg(long)]
    work: Option<PathBuf>,
}

#[derive(Clone, Copy, ValueEnum)]
enum Checker {
    Nitrolean,
    /// Reads a Susz file: give it the .susz that `susz pack --no-index` makes.
    Gruszka,
    NanoLean,
}

#[derive(Args)]
pub struct RunArgs {
    /// The export (a .susz file for gruszka).
    export: PathBuf,
    /// Thread counts (default: 1 2 4 8, and all cores if more).
    threads: Vec<usize>,
    #[arg(long, value_enum, default_value = "nitrolean")]
    checker: Checker,
    /// The checker's binary (default: target/release/nitrolean for
    /// nitrolean, else `gruszka` or `nl-fast` on PATH).
    #[arg(long)]
    bin: Option<PathBuf>,
}

pub fn main(cmd: Cmd) -> Result<()> {
    match cmd {
        Cmd::Fetch(a) => fetch(a),
        Cmd::Run(a) => run(a),
    }
}

fn fetch(a: FetchArgs) -> Result<()> {
    need(
        "mathlib",
        &["git", "elan"],
        " (elan: https://github.com/leanprover/elan)",
    )?;
    let out = absolute(&a.out);
    let work = match a.work {
        Some(w) => absolute(&w),
        None => out.parent().unwrap_or(Path::new(".")).join("mathlib4"),
    };
    if !work.is_dir() {
        crate::util::run(
            Command::new("git")
                .args(["clone", "--filter=blob:none", MATHLIB_URL])
                .arg(&work),
        )?;
    }
    crate::util::run(git(&work).args(["checkout", "-q", MATHLIB_REV]))?;
    let tc = fs::read_to_string(work.join("lean-toolchain")).context("Mathlib's lean-toolchain")?;
    elan_install(tc.trim(), true)?;
    crate::util::run(
        Command::new("lake")
            .args(["exe", "cache", "get"])
            .current_dir(&work),
    )?;
    let leanexport = output(
        Command::new("elan")
            .args(["which", "leanexport"])
            .current_dir(&work),
    )?;
    let tmp = out.with_extension("ndjson.tmp");
    let f = fs::File::create(&tmp).with_context(|| format!("{}: cannot create", tmp.display()))?;
    log("mathlib", "exporting Mathlib (a few minutes)");
    crate::util::run(
        Command::new("lake")
            .arg("env")
            .arg(leanexport.trim())
            .arg("Mathlib")
            .current_dir(&work)
            .stdout(f),
    )?;
    fs::rename(&tmp, &out)?;
    let sum = sha256_file(&out)?;
    if sum != EXPORT_SHA256 {
        bail!(
            "{} has SHA-256 {sum}, expected {EXPORT_SHA256}",
            out.display()
        );
    }
    log(
        "mathlib",
        &format!("{} matches the expected SHA-256", out.display()),
    );
    Ok(())
}

fn run(a: RunArgs) -> Result<()> {
    let mut threads = a.threads;
    if threads.is_empty() {
        threads = vec![1, 2, 4, 8];
        let all = nproc();
        if all > 8 {
            threads.push(all);
        }
    }
    let bin = match (&a.bin, a.checker) {
        (Some(b), _) => b.clone(),
        (None, Checker::Nitrolean) => root().join("target/release/nitrolean"),
        (None, Checker::Gruszka) => PathBuf::from("gruszka"),
        (None, Checker::NanoLean) => PathBuf::from("nl-fast"),
    };
    let name = match a.checker {
        Checker::Nitrolean => "nitrolean",
        Checker::Gruszka => "gruszka",
        Checker::NanoLean => "nano-lean",
    };
    let out_file = std::env::temp_dir().join(format!("xtask-mathlib-{}.out", std::process::id()));
    println!("checker\tthreads\twall_s\tcpu_s\trss_mib\tstatus\tlast_line");
    for j in threads {
        let mut cmd = Command::new(&bin);
        let js = j.to_string();
        match a.checker {
            Checker::Nitrolean => cmd.arg("check").args(["-j", &js]).arg(&a.export),
            Checker::Gruszka => cmd.arg(&a.export).arg(&js),
            Checker::NanoLean => cmd.args(["-q", "-j", &js]).arg(&a.export),
        };
        let f = fs::File::create(&out_file)?;
        cmd.stdout(f.try_clone()?).stderr(Stdio::from(f));
        let o = run_timed(&mut cmd, None, false, 0, true)?;
        let text = fs::read_to_string(&out_file).unwrap_or_default();
        let last = text.lines().last().unwrap_or("").trim().to_string();
        println!(
            "{name}\t{j}\t{:.2}\t{:.1}\t{}\t{}\t{last}",
            o.wall,
            o.cpu,
            o.maxrss_kib / 1024,
            o.code
        );
    }
    let _ = fs::remove_file(&out_file);
    Ok(())
}
