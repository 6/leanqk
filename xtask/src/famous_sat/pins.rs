//! The toolchains, sources and checkouts the exports are made with, pinned
//! as `cargo xtask kc` pins them, and where things go.

use std::path::PathBuf;
use std::process::{Command, Stdio};

use super::util::{Res, err, log, mkdir, output, run};
use crate::util::{content_sha256, git};

/// The Lean of LRAT-Catcher and of `BenchLrat`, and so of the exports.
pub const TC_CATCHER: &str = "leanprover/lean4:v4.30.0";
pub const LEAN4EXPORT_URL: &str = "https://github.com/leanprover/lean4export";
/// "bump toolchain to v4.30.0"
pub const LEAN4EXPORT_430: &str = "a3e35a584f59b390667db7269cd37fca8575e4bf";
/// CaDiCaL rel-2.2.1, as `cargo xtask kc fetch-lrat` pins it.
pub const CADICAL_COMMIT: &str = "4198d817d0dcde5b1240eefbff70b555b7df2af9";
pub const CADICAL_SHA256: &str = "6f9781faa6a03049e0448761a50a5f327ecaae6b74336b66a6e073abb6af01a5";

/// Directories: this benchmark's (`bench/famous-sat`), kernel-compute's
/// (whose Lean helpers and checker builds it uses), the cache and the
/// output. The cache and output default to kernel-compute's, so that both
/// share sources and builds (`KC_CACHE`, `KC_OUT` override them).
pub struct Dirs {
    pub fs: PathBuf,
    pub kc: PathBuf,
    pub cache: PathBuf,
    pub out: PathBuf,
}

impl Dirs {
    pub fn new(cache: Option<PathBuf>, out: Option<PathBuf>) -> Res<Dirs> {
        let fs = crate::util::root().join("bench/famous-sat");
        let kc = crate::util::root().join("bench/kernel-compute");
        let pick = |opt: Option<PathBuf>, var: &str, dflt: &str| {
            opt.or_else(|| std::env::var_os(var).map(PathBuf::from))
                .unwrap_or_else(|| kc.join(dflt))
        };
        let cache = super::util::abs(&pick(cache, "KC_CACHE", "cache"))?;
        let out = super::util::abs(&pick(out, "KC_OUT", "out"))?;
        Ok(Dirs { fs, kc, cache, out })
    }
}

/// A checkout of `url` at `commit` in CACHE/src/NAME, checked against its
/// pinned content hash (with `update_pins`, a mismatch is only reported).
pub fn fetch_git(
    d: &Dirs,
    name: &str,
    url: &str,
    commit: &str,
    want: &str,
    update_pins: bool,
) -> Res<PathBuf> {
    let dir = d.cache.join("src").join(name);
    if !dir.join(".git").is_dir() {
        let _ = std::fs::remove_dir_all(&dir);
        mkdir(&dir)?;
        run(git(&dir).args(["init", "-q"]))?;
        run(git(&dir).args(["remote", "add", "origin", url]))?;
    }
    let have = git(&dir)
        .args(["cat-file", "-e", &format!("{commit}^{{commit}}")])
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|s| s.success());
    if !have {
        log(format!("fetching {name} at {commit}"));
        run(git(&dir).args(["fetch", "-q", "--depth", "1", "origin", commit]))?;
    }
    run(git(&dir).args([
        "-c",
        "advice.detachedHead=false",
        "checkout",
        "-q",
        "--force",
        commit,
    ]))?;
    run(git(&dir).args(["clean", "-qfdx"]))?;
    if output(git(&dir).args(["rev-parse", "HEAD"]))?.trim() != commit {
        return err(format!("{name}: not at {commit}"));
    }
    let got = content_sha256(&dir, &["."], &["./.git"])?;
    if got != want {
        if !update_pins {
            return err(format!("{name}: content SHA-256 is {got}, expected {want}"));
        }
        log(format!("{name}: content SHA-256 is {got} (pinned: {want})"));
    }
    Ok(dir)
}

/// lean4export built with the toolchain it is for; the binary.
pub fn build_exporter(d: &Dirs, name: &str, commit: &str, tc: &str) -> Res<PathBuf> {
    let dir = d.cache.join(format!("lean4export-{name}"));
    let bin = dir.join(".lake/build/bin/lean4export");
    if bin.is_file() {
        return Ok(bin);
    }
    let _ = std::fs::remove_dir_all(&dir);
    mkdir(&dir)?;
    run(git(&dir).args(["init", "-q"]))?;
    run(git(&dir).args(["remote", "add", "origin", LEAN4EXPORT_URL]))?;
    run(git(&dir).args(["fetch", "-q", "--depth", "1", "origin", commit]))?;
    run(git(&dir).args(["-c", "advice.detachedHead=false", "checkout", "-q", commit]))?;
    let have = super::util::read(&dir.join("lean-toolchain"))?;
    if have.trim() != tc {
        return err(format!(
            "lean4export {commit} is for {}, not {tc}",
            have.trim()
        ));
    }
    run(Command::new("elan")
        .args(["run", tc, "lake", "build"])
        .current_dir(&dir))?;
    Ok(bin)
}
