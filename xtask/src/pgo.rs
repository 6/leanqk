//! `cargo xtask pgo EXPORT...`: a profile-guided release build.
//!
//! Builds nitrolean instrumented (in `target/pgo/gen`), checks each export
//! with it on one thread to record a profile, merges the profiles with the
//! toolchain's `llvm-profdata` (`rustup component add llvm-tools`), and
//! builds `target/release/nitrolean` with the merged profile. The profile is
//! also left in `target/pgo/nitrolean.profdata`, for `--use` on a later build.
//!
//! Good training sets are the exports of Lean's `Init` and `Std` (the
//! arena's `init` and `std` tests); a prefix of an export (whole lines,
//! e.g. `head -n 20000000` of Mathlib's) is a valid export too, as each line
//! refers only to the lines before it. `--repo` trains on what the
//! repository holds: the exports of `tests/kernel` and a prefix of `Init`'s
//! export (`bench/arena/pgo`, unpacked with `xz`), for builds with no other
//! exports at hand, such as the arena's.
//!
//! `--bolt` then lays out the profile-guided binary's code again with
//! LLVM's post-link optimizer: it is linked with its relocations kept
//! (`-Wl,--emit-relocs`), a BOLT profile is recorded on the same exports,
//! one thread each, and `llvm-bolt` reorders its blocks and functions and
//! moves cold code apart. The profile is sampled with `perf record -e
//! cycles:u -j any,u` where the machine records last branches, and else
//! recorded by a copy of the binary that `llvm-bolt -instrument` made
//! (`--bolt-profile` picks one). `llvm-bolt`, `merge-fdata` (and, for
//! sampling, `perf` and `perf2bolt`) come from LLVM's BOLT, found on PATH
//! as `NAME` or `NAME-VERSION`, or in `--bolt-dir`. The binary before BOLT
//! stays in `target/pgo/nitrolean.pre-bolt`; the build fails unless both
//! give the same output (exit status, standard output and error) on every
//! training export at `-j 1` and `-j 4`.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, bail};

use crate::util::{absolute, is_executable, log, output, root, run, which};

const T: &str = "pgo";

#[derive(clap::Args)]
pub struct Args {
    /// Exports to train on.
    #[arg(required_unless_present_any = ["use_profile", "repo"])]
    exports: Vec<PathBuf>,
    /// Train on the exports in the repository (as well).
    #[arg(long)]
    repo: bool,
    /// Build with this merged profile instead of training (no exports needed).
    #[arg(long = "use", value_name = "PROFDATA")]
    use_profile: Option<PathBuf>,
    /// Further flags for rustc, for both builds (e.g. `-C target-cpu=native`).
    #[arg(long, default_value = "", allow_hyphen_values = true)]
    rustflags: String,
    /// Optimize the binary's code layout with BOLT after the build.
    #[arg(long)]
    bolt: bool,
    /// How to record BOLT's profile: perf's last-branch samples, an
    /// instrumented binary, or the first that works (perf when it can
    /// record branch stacks).
    #[arg(long, value_enum, default_value = "auto")]
    bolt_profile: BoltProfile,
    /// The directory holding llvm-bolt and merge-fdata (else PATH).
    #[arg(long, value_name = "DIR")]
    bolt_dir: Option<PathBuf>,
}

#[derive(Clone, Copy, PartialEq, Eq, clap::ValueEnum)]
enum BoltProfile {
    Auto,
    Perf,
    Instrument,
}

/// llvm-bolt's layout options.
const BOLT_OPTS: &[&str] = &[
    "-reorder-blocks=ext-tsp",
    "-reorder-functions=cdsort",
    "-split-functions",
    "-split-all-cold",
    "-split-eh",
    "-icf=all",
    "-dyno-stats",
];

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
    let bolt = if a.bolt {
        Some(Bolt::find(a.bolt_dir.as_deref())?)
    } else {
        None
    };
    if bolt.is_some() && a.exports.is_empty() && !a.repo {
        bail!("{T}: error: --bolt trains on exports: give some, or --repo");
    }
    log(T, "building target/release/nitrolean with the profile");
    let mut flags = format!("{} -Cprofile-use={}", a.rustflags, profile.display());
    if bolt.is_some() {
        flags.push_str(" -Clink-arg=-Wl,--emit-relocs");
    }
    run(&mut cargo_build(&root, &flags, None))?;
    if let Some(b) = bolt {
        let exports = exports(&root, &dir, &a)?;
        b.optimize(
            &dir,
            &root.join("target/release/nitrolean"),
            &exports,
            a.bolt_profile,
        )?;
    }
    log(T, "done: target/release/nitrolean");
    Ok(())
}

/// The exports to train on: those given, and with `--repo` the repository's.
fn exports(root: &Path, dir: &Path, a: &Args) -> Result<Vec<PathBuf>> {
    let mut exports: Vec<PathBuf> = a.exports.iter().map(|e| absolute(e)).collect();
    if a.repo {
        exports.extend(repo_exports(root, dir)?);
    }
    Ok(exports)
}

/// Checks `e` with `bin` on one thread, as training does; a rejected
/// export still trains, only a crash is an error.
fn train_run(mut cmd: Command, bin: &Path, e: &Path) -> Result<()> {
    let st = cmd
        .args(["check", "--threads", "1", "--jobs", "1"])
        .arg(e)
        .stdout(std::process::Stdio::null())
        .status()
        .with_context(|| format!("cannot run {}", bin.display()))?;
    if st.code().is_none_or(|c| c > 2) {
        bail!("{T}: error: {} on {}: {st}", bin.display(), e.display());
    }
    Ok(())
}

/// LLVM's BOLT tools.
struct Bolt {
    bolt: PathBuf,
    merge: PathBuf,
    perf2bolt: Option<PathBuf>,
}

impl Bolt {
    fn find(dir: Option<&Path>) -> Result<Bolt> {
        let find = |name: &str| -> Option<PathBuf> {
            if let Some(d) = dir {
                let p = d.join(name);
                return is_executable(&p).then_some(p);
            }
            which(name).or_else(|| (14..=40).rev().find_map(|v| which(&format!("{name}-{v}"))))
        };
        let need = |name: &str| {
            find(name).with_context(|| {
                format!("{T}: error: {name} not found (LLVM's BOLT: e.g. apt install llvm-bolt, or --bolt-dir)")
            })
        };
        Ok(Bolt {
            bolt: need("llvm-bolt")?,
            merge: need("merge-fdata")?,
            perf2bolt: find("perf2bolt"),
        })
    }

    /// Records a profile of `bin` on `exports` and replaces `bin` with its
    /// optimized layout.
    fn optimize(
        &self,
        dir: &Path,
        bin: &Path,
        exports: &[PathBuf],
        how: BoltProfile,
    ) -> Result<()> {
        let bdir = dir.join("bolt");
        if bdir.exists() {
            fs::remove_dir_all(&bdir)
                .with_context(|| format!("{}: cannot remove", bdir.display()))?;
        }
        fs::create_dir_all(&bdir)?;
        let pre = dir.join("nitrolean.pre-bolt");
        fs::copy(bin, &pre).with_context(|| format!("{}: cannot copy", bin.display()))?;
        let use_perf = match how {
            BoltProfile::Perf => true,
            BoltProfile::Instrument => false,
            BoltProfile::Auto => self.perf2bolt.is_some() && lbr_works(&bdir),
        };
        let mut fdata = Vec::new();
        if use_perf {
            let p2b = self.perf2bolt.as_ref().context("perf2bolt not found")?;
            log(
                T,
                "recording BOLT's profile with perf (last branch records)",
            );
            for (i, e) in exports.iter().enumerate() {
                log(T, &format!("BOLT training on {}", e.display()));
                let data = bdir.join(format!("perf-{i}.data"));
                let mut cmd = Command::new("perf");
                cmd.args(["record", "-q", "-e", "cycles:u", "-j", "any,u", "-o"])
                    .arg(&data)
                    .arg("--")
                    .arg(&pre);
                train_run(cmd, &pre, e)?;
                let out = bdir.join(format!("perf-{i}.fdata"));
                let mut cmd = Command::new(p2b);
                cmd.arg("-p").arg(&data).arg("-o").arg(&out).arg(&pre);
                run(cmd.stdout(std::process::Stdio::null()))?;
                fs::remove_file(&data)?;
                fdata.push(out);
            }
        } else {
            log(T, "recording BOLT's profile with an instrumented binary");
            let inst = bdir.join("nitrolean.instrumented");
            let mut cmd = Command::new(&self.bolt);
            cmd.arg(&pre)
                .arg("-instrument")
                .arg(format!(
                    "-instrumentation-file={}",
                    bdir.join("prof").display()
                ))
                .arg("-instrumentation-file-append-pid")
                .arg("-o")
                .arg(&inst);
            run(cmd.stdout(std::process::Stdio::null()))?;
            for e in exports {
                log(T, &format!("BOLT training on {}", e.display()));
                train_run(Command::new(&inst), &inst, e)?;
            }
            for f in fs::read_dir(&bdir)? {
                let p = f?.path();
                if p.extension().is_some_and(|x| x == "fdata") {
                    fdata.push(p);
                }
            }
            fdata.sort();
            if fdata.len() != exports.len() {
                bail!(
                    "{T}: error: {} BOLT profiles from {} runs",
                    fdata.len(),
                    exports.len()
                );
            }
        }
        let merged = dir.join("nitrolean.fdata");
        let f = fs::File::create(&merged)
            .with_context(|| format!("{}: cannot create", merged.display()))?;
        let mut cmd = Command::new(&self.merge);
        cmd.args(&fdata).stdout(f);
        run(&mut cmd)?;
        log(T, "optimizing target/release/nitrolean's layout with BOLT");
        let out = bdir.join("nitrolean.bolt");
        let mut cmd = Command::new(&self.bolt);
        cmd.arg(&pre)
            .arg("-o")
            .arg(&out)
            .arg(format!("-data={}", merged.display()));
        cmd.args(BOLT_OPTS);
        run(&mut cmd)?;
        same_output(&pre, &out, exports)?;
        fs::rename(&out, bin).with_context(|| format!("{}: cannot replace", bin.display()))?;
        Ok(())
    }
}

/// Fails unless `a` and `b` give the same exit status, standard output and
/// standard error on each export, on one and on four threads.
fn same_output(a: &Path, b: &Path, exports: &[PathBuf]) -> Result<()> {
    let out = |bin: &Path, j: &str, e: &Path| -> Result<(Option<i32>, Vec<u8>, Vec<u8>)> {
        let o = Command::new(bin)
            .args(["check", "--jobs", j])
            .arg(e)
            .output()
            .with_context(|| format!("cannot run {}", bin.display()))?;
        Ok((o.status.code(), o.stdout, o.stderr))
    };
    for j in ["1", "4"] {
        for e in exports {
            if out(a, j, e)? != out(b, j, e)? {
                bail!(
                    "{T}: error: BOLT's binary differs from {} on {} (-j {j})",
                    a.display(),
                    e.display()
                );
            }
        }
    }
    log(
        T,
        &format!(
            "BOLT's binary gives the same output on {} exports at -j 1 and -j 4",
            exports.len()
        ),
    );
    Ok(())
}

/// Whether perf can sample user-space branch stacks here.
fn lbr_works(dir: &Path) -> bool {
    Command::new("perf")
        .args(["record", "-q", "-e", "cycles:u", "-j", "any,u", "-o"])
        .arg(dir.join("probe.data"))
        .args(["--", "true"])
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .is_ok_and(|s| s.success())
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
    for e in &exports(root, dir, a)? {
        log(T, &format!("training on {}", e.display()));
        train_run(Command::new(&bin), &bin, e)?;
    }
    let merged = dir.join("nitrolean.profdata");
    let mut cmd = Command::new(profdata);
    cmd.args(["merge", "-o"]).arg(&merged).arg(&raw);
    run(&mut cmd)?;
    Ok(merged)
}

/// The repository's training exports: `tests/kernel`'s, and the prefix of
/// `Init`'s export, unpacked into `dir`.
fn repo_exports(root: &Path, dir: &Path) -> Result<Vec<PathBuf>> {
    let kernel = root.join("tests/kernel/exports");
    let mut out: Vec<PathBuf> = fs::read_dir(&kernel)
        .with_context(|| format!("{}: cannot read", kernel.display()))?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "ndjson"))
        .collect();
    out.sort();
    let packed = root.join("bench/arena/pgo/init-prefix.ndjson.xz");
    let prefix = dir.join("init-prefix.ndjson");
    let f = fs::File::create(&prefix)
        .with_context(|| format!("{}: cannot create", prefix.display()))?;
    let mut cmd = Command::new("xz");
    cmd.arg("-dc").arg(&packed).stdout(f);
    run(&mut cmd).context("xz is needed to unpack the Init prefix")?;
    out.push(prefix);
    Ok(out)
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
