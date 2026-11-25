//! `cargo xtask install-elan`: installs elan from its release archive,
//! checked against a pinned SHA-256, for the CI workflows.

use std::path::PathBuf;
use std::process::Command;

use anyhow::{Result, bail};

use crate::util::{run, sha256_file};

#[derive(clap::Args)]
pub struct InstallElanArgs {
    /// The elan release (e.g. v4.4.0)
    #[arg(long, env = "ELAN_VERSION")]
    version: String,
    /// The SHA-256 of its x86_64 Linux archive
    #[arg(long, env = "ELAN_SHA256")]
    sha256: String,
    /// Also install this toolchain
    #[arg(long)]
    toolchain: Option<String>,
}

pub fn install_elan(a: InstallElanArgs) -> Result<()> {
    let home = PathBuf::from(std::env::var_os("HOME").unwrap_or_default());
    let bin = home.join(".elan/bin");
    if !crate::util::is_executable(&bin.join("elan")) {
        let tmp = std::env::temp_dir().join(format!("elan-{}", std::process::id()));
        std::fs::create_dir_all(&tmp)?;
        let archive = tmp.join("elan.tar.gz");
        let url = format!(
            "https://github.com/leanprover/elan/releases/download/{}/elan-x86_64-unknown-linux-gnu.tar.gz",
            a.version
        );
        run(Command::new("curl")
            .args(["-sSfL", "-o"])
            .arg(&archive)
            .arg(&url))?;
        let got = sha256_file(&archive)?;
        if got != a.sha256 {
            bail!("install-elan: {url}: SHA-256 {got}, expected {}", a.sha256);
        }
        run(Command::new("tar")
            .arg("-xzf")
            .arg(&archive)
            .arg("-C")
            .arg(&tmp))?;
        run(Command::new(tmp.join("elan-init")).args([
            "-y",
            "--no-modify-path",
            "--default-toolchain",
            "none",
        ]))?;
        let _ = std::fs::remove_dir_all(&tmp);
    }
    if let Some(p) = std::env::var_os("GITHUB_PATH") {
        use std::io::Write;
        let mut f = std::fs::OpenOptions::new()
            .append(true)
            .create(true)
            .open(p)?;
        writeln!(f, "{}", bin.display())?;
    }
    if let Some(tc) = a.toolchain {
        run(Command::new(bin.join("elan")).args(["toolchain", "install", &tc]))?;
    }
    Ok(())
}
