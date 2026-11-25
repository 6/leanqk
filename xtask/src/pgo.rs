//! `cargo xtask pgo EXPORT...`: a profile-guided release build.
//!
//! Builds nitrolean instrumented (in `target/pgo/gen`), checks each export
//! with it on one thread to record a profile, merges the profiles with the
//! toolchain's `llvm-profdata` (`rustup component add llvm-tools`), and
//! builds `target/release/nitrolean` with the merged profile. The profile is
//! also left in `target/pgo/nitrolean.profdata`, for `--use` on a later build.
//!
//! Good training sets are the exports of Lean's `Init` and `Std` (the
//! arena's `init` and `std` tests); a prefix of Mathlib's export (whole
//! lines, e.g. `head -n 20000000`) is a valid export too, as each line
//! refers only to the lines before it.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, bail};

use crate::util::{absolute, log, output, root, run};

const T: &str = "pgo";

#[derive(clap::Args)]
pub struct Args {
    /// Exports to train on.
    #[arg(required_unless_present = "use_profile")]
    exports: Vec<PathBuf>,
    /// Build with this merged profile instead of training (no exports needed).
    #[arg(long = "use", value_name = "PROFDATA")]
    use_profile: Option<PathBuf>,
    /// Further flags for rustc, for both builds (e.g. `-C target-cpu=native`).
    #[arg(long, default_value = "", allow_hyphen_values = true)]
    rustflags: String,
}

pub fn main(a: Args) -> Result<()> {
    let root = root();
    let dir = root.join("target/pgo");
    let profile = match &a.use_profile {
        Some(p) => absolute(p),
        None => train(&root, &dir, &a)?,
    };
    if !profile.is_file() {
        bail!("{T}: error: {}: no such profile", profile.display());
    }
    log(T, "building target/release/nitrolean with the profile");
    let flags = format!("{} -Cprofile-use={}", a.rustflags, profile.display());
    run(&mut cargo_build(&root, &flags, None))?;
    log(T, "done: target/release/nitrolean");
    Ok(())
}

/// The instrumented build, its runs on the exports, and the merged profile.
fn train(root: &Path, dir: &Path, a: &Args) -> Result<PathBuf> {
    let profdata = llvm_profdata()?;
    let raw = dir.join("raw");
    if raw.exists() {
        fs::remove_dir_all(&raw).with_context(|| format!("{}: cannot remove", raw.display()))?;
    }
    fs::create_dir_all(&raw)?;
    log(T, "building nitrolean instrumented");
    let flags = format!("{} -Cprofile-generate={}", a.rustflags, raw.display());
    let gen_dir = dir.join("gen");
    run(&mut cargo_build(root, &flags, Some(&gen_dir)))?;
    let bin = gen_dir.join("release/nitrolean");
    for e in &a.exports {
        log(T, &format!("training on {}", e.display()));
        let st = Command::new(&bin)
            .args(["check", "--threads", "1"])
            .arg(absolute(e))
            .stdout(std::process::Stdio::null())
            .status()
            .with_context(|| format!("cannot run {}", bin.display()))?;
        // A rejected export still trains; only a crash is an error.
        if st.code().is_none_or(|c| c > 2) {
            bail!("{T}: error: {} on {}: {st}", bin.display(), e.display());
        }
    }
    let merged = dir.join("nitrolean.profdata");
    let mut cmd = Command::new(profdata);
    cmd.args(["merge", "-o"]).arg(&merged).arg(&raw);
    run(&mut cmd)?;
    Ok(merged)
}

/// `cargo build --release` of nitrolean, with `flags` added to RUSTFLAGS.
fn cargo_build(root: &Path, flags: &str, target_dir: Option<&Path>) -> Command {
    let mut all = std::env::var_os("RUSTFLAGS").unwrap_or_default();
    all.push(" ");
    all.push(flags);
    let mut cmd = Command::new(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()));
    cmd.current_dir(root)
        .args(["build", "--release", "--locked", "--package", "nitrolean"])
        .env("RUSTFLAGS", all);
    if let Some(d) = target_dir {
        cmd.arg("--target-dir").arg(d);
    }
    cmd
}

/// The toolchain's `llvm-profdata` (from the `llvm-tools` component).
fn llvm_profdata() -> Result<PathBuf> {
    let sysroot = output(Command::new("rustc").args(["--print", "sysroot"]))?;
    let vv = output(Command::new("rustc").arg("-vV"))?;
    let host = vv
        .lines()
        .find_map(|l| l.strip_prefix("host: "))
        .context("rustc -vV: no host")?;
    let p = Path::new(sysroot.trim()).join(format!("lib/rustlib/{host}/bin/llvm-profdata"));
    if !p.is_file() {
        bail!(
            "{T}: error: {} not found (rustup component add llvm-tools)",
            p.display()
        );
    }
    Ok(p)
}
