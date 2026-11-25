//! Small helpers of `famous-sat`; the rest come from `crate::util`.

use std::fmt::Display;
use std::path::{Path, PathBuf};
use std::process::Command;

pub use anyhow::Result as Res;
use anyhow::{Context, anyhow};

pub use crate::util::{output, path_with, read_tsv as tsv, run, sha256_file};

pub fn err<T>(msg: impl Display) -> Res<T> {
    Err(anyhow!("{msg}"))
}

/// `HH:MM:SS famous-sat: MSG` on stderr.
pub fn log(msg: impl Display) {
    crate::util::log("famous-sat", &msg.to_string());
}

pub fn size(p: &Path) -> u64 {
    std::fs::metadata(p).map_or(0, |m| m.len())
}

pub fn read(p: &Path) -> Res<String> {
    std::fs::read_to_string(p).with_context(|| format!("{}: cannot read", p.display()))
}

pub fn write(p: &Path, s: impl AsRef<[u8]>) -> Res<()> {
    if let Some(d) = p.parent() {
        mkdir(d)?;
    }
    std::fs::write(p, s).with_context(|| format!("{}: cannot write", p.display()))
}

pub fn mkdir(p: &Path) -> Res<()> {
    std::fs::create_dir_all(p).with_context(|| format!("{}: cannot create", p.display()))
}

/// `p`, made if missing, as an absolute path.
pub fn abs(p: &Path) -> Res<PathBuf> {
    mkdir(p)?;
    p.canonicalize().with_context(|| p.display().to_string())
}

pub fn need(tools: &[&str]) -> Res<()> {
    crate::util::need("famous-sat", tools, " (see bench/famous-sat/README.md)")
}

/// Run with stdout and stderr to `log`; on failure the end of the log is
/// printed.
pub fn run_logged(c: &mut Command, log: &Path) -> Res<()> {
    let msg = format!(
        "{} failed (log: {})",
        crate::util::describe(c),
        log.display()
    );
    crate::util::run_logged(c, log, 30, &msg)
}

/// Download `url` to `file` unless it already has SHA-256 `want`. A
/// mismatch is an error unless `update_pins` (then it is reported).
pub fn fetch_url(url: &str, want: &str, file: &Path, update_pins: bool) -> Res<()> {
    if file.is_file() && sha256_file(file)? == want {
        return Ok(());
    }
    log(format!("fetching {url}"));
    let part = file.with_extension("part");
    if let Some(d) = file.parent() {
        mkdir(d)?;
    }
    run(Command::new("curl")
        .args(["-fsSL", "--retry", "5", "--retry-delay", "10", "-o"])
        .arg(&part)
        .arg(url))?;
    let got = sha256_file(&part)?;
    if got != want {
        if !update_pins {
            return err(format!("{url}: SHA-256 is {got}, expected {want}"));
        }
        log(format!("{url}: SHA-256 is {got} (pinned: {want})"));
    }
    std::fs::rename(&part, file)?;
    Ok(())
}

/// `c` with an unlimited stack (`ulimit -s unlimited`): Lean's elaborator
/// and the exporter recurse on the proof terms.
pub fn unlimited_stack(c: &mut Command) -> &mut Command {
    crate::util::unlimited_stack(c);
    c
}
