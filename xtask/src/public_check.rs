//! `cargo xtask public-check [RANGE | --tree-only]`: checks that the
//! repository holds nothing that shouldn't be public, and
//! `cargo xtask public-check-test`: tests that on planted violations.
//!
//! The tree is every tracked file plus every untracked file that isn't
//! ignored, so that it can run before a commit. Exits 1 after reporting every
//! violation. Binary files and files over 1 MB are refused unless their path
//! (or a glob matching it) is listed in xtask/public-check.allow.

use std::fs;
use std::path::Path;
use std::process::Command;

use anyhow::{Context, Result};

use crate::util::{exit_with, glob_match, root};

/// The allowlist, relative to the repository root.
pub const ALLOW_FILE: &str = "xtask/public-check.allow";

const README_LINE: &str = "`nitrolean` - Independent Lean 4 proof checker in Rust, focused on speed and low memory use (work in progress)";
const BOT_TRAILER: &str = "Co-Authored-By: 6[bot] <129682364+6[bot]@users.noreply.github.com>";
const HOME_PATHS: &str = "/(home|Users)/[A-Za-z0-9_]";
const IPV4: &str = r"\b([0-9]{1,3}\.){3}[0-9]{1,3}\b";

#[derive(clap::Args)]
pub struct Args {
    /// Check the tree only, not commit messages.
    #[arg(long)]
    tree_only: bool,
    /// The commits whose messages are checked.
    #[arg(default_value = "origin/main..HEAD", conflicts_with = "tree_only")]
    range: String,
}

pub fn main(a: Args) -> Result<()> {
    let range = (!a.tree_only).then_some(a.range.as_str());
    let r = check(&root(), range)?;
    for l in &r.errors {
        eprintln!("public-check: {l}");
    }
    if !r.errors.is_empty() {
        return Err(exit_with(
            1,
            format!("public-check: {} violation(s)", r.errors.len()),
        ));
    }
    println!("{}", r.ok_line);
    Ok(())
}

/// The outcome of a check: the violations, and the line printed if none.
pub struct Report {
    pub errors: Vec<String>,
    pub ok_line: String,
}

/// Lines of the output of a git command run in `dir`, split on `sep`
/// (its failures are ignored, as `2>/dev/null` did).
fn git_lines(dir: &Path, args: &[&str], sep: u8) -> Vec<String> {
    let out = Command::new("git").arg("-C").arg(dir).args(args).output();
    let Ok(out) = out else { return Vec::new() };
    out.stdout
        .split(|&b| b == sep)
        .filter(|l| !l.is_empty())
        .map(|l| String::from_utf8_lossy(l).into_owned())
        .collect()
}

/// Checks the repository at `dir`, and the messages of the commits in
/// `range` unless it is `None`.
pub fn check(dir: &Path, range: Option<&str>) -> Result<Report> {
    let mut errors = Vec::new();

    // 1. README.md is exactly one line, ending in a newline.
    match fs::read(dir.join("README.md")) {
        Err(_) => errors.push("README.md is missing".into()),
        Ok(data) => {
            let stripped = data.strip_suffix_all(b'\n');
            let lines = data.iter().filter(|&&b| b == b'\n').count();
            if stripped != README_LINE.as_bytes() || lines != 1 {
                errors.push(format!(
                    "README.md must be exactly the one line '{README_LINE}'"
                ));
            }
        }
    }

    // 2. Home directory paths.
    for m in git_lines(
        dir,
        &["grep", "--untracked", "-nIE", HOME_PATHS, "--", "."],
        b'\n',
    ) {
        errors.push(format!("home directory path: {m}"));
    }

    // IPv4 addresses outside the documentation ranges of RFC 5737.
    for m in git_lines(
        dir,
        &["grep", "--untracked", "-nIoE", IPV4, "--", "."],
        b'\n',
    ) {
        let Some((at, ip)) = m.rsplit_once(':') else {
            continue;
        };
        let parts: Vec<u32> = ip.split('.').filter_map(|p| p.parse().ok()).collect();
        if parts.len() != 4 || parts.iter().any(|&p| p > 255) {
            continue;
        }
        if matches!(
            (parts[0], parts[1], parts[2]),
            (192, 0, 2) | (198, 51, 100) | (203, 0, 113)
        ) {
            continue;
        }
        errors.push(format!("IPv4 address: {at}: {ip}"));
    }

    // 3. Build artifacts, binaries and large files.
    let mut allow = Vec::new();
    if let Ok(text) = fs::read_to_string(dir.join(ALLOW_FILE)) {
        for line in text.lines() {
            let line = line.split('#').next().unwrap_or("").trim_end();
            if !line.is_empty() {
                allow.push(line.to_string());
            }
        }
    }
    let allowed = |f: &str| allow.iter().any(|p| glob_match(p, f));
    let text: std::collections::HashSet<String> =
        git_lines(dir, &["grep", "--untracked", "-IlzE", "", "--", "."], 0)
            .into_iter()
            .collect();
    for f in git_lines(
        dir,
        &[
            "ls-files",
            "-z",
            "--cached",
            "--others",
            "--exclude-standard",
        ],
        0,
    ) {
        let p = dir.join(&f);
        let Ok(md) = fs::symlink_metadata(&p) else {
            continue;
        };
        if !md.is_file() {
            continue;
        }
        let slashed = format!("/{f}");
        if slashed.contains("/.lake/") || slashed.contains("/target/") {
            errors.push(format!("build directory: {f}"));
            continue;
        }
        if [".olean", ".ilean", ".ir", ".o", ".so", ".dylib", ".a"]
            .iter()
            .any(|e| f.ends_with(e))
        {
            errors.push(format!("build artifact: {f}"));
            continue;
        }
        let size = md.len();
        if size > 0 && !text.contains(&f) && !allowed(&f) {
            errors.push(format!(
                "binary file: {f} (list it in {ALLOW_FILE} if it belongs here)"
            ));
        }
        if size > 1048576 && !allowed(&f) {
            errors.push(format!(
                "file over 1 MB: {f} ({size} bytes; list it in {ALLOW_FILE} if it belongs here)"
            ));
        }
    }

    // 4. Commit messages.
    let mut ncommits = 0;
    if let Some(range) = range {
        let out = Command::new("git")
            .arg("-C")
            .arg(dir)
            .args(["rev-list", range])
            .stderr(std::process::Stdio::null())
            .output()
            .context("cannot run git")?;
        if !out.status.success() {
            errors.push(format!(
                "cannot list the commits in '{range}' (fetch the base, or pass --tree-only)"
            ));
        } else {
            let commits = String::from_utf8_lossy(&out.stdout).into_owned();
            for c in commits.lines().filter(|l| !l.is_empty()) {
                ncommits += 1;
                let msg = Command::new("git")
                    .arg("-C")
                    .arg(dir)
                    .args(["log", "-1", "--format=%B", c])
                    .output()
                    .context("cannot run git")?;
                let msg = String::from_utf8_lossy(&msg.stdout).into_owned();
                let short = &c[..c.len().min(12)];
                for m in msg.trim_end_matches('\n').lines() {
                    let lower = m.trim_start().to_ascii_lowercase();
                    if lower.starts_with("co-authored-by:") && m != BOT_TRAILER {
                        errors.push(format!("commit {short}: co-author trailer: {m}"));
                    }
                }
            }
        }
    }

    let ok_line = match range {
        Some(r) => format!("public-check: OK (tree and {ncommits} commit(s) in {r})"),
        None => "public-check: OK (tree)".to_string(),
    };
    Ok(Report { errors, ok_line })
}

trait StripAll {
    fn strip_suffix_all(&self, b: u8) -> &[u8];
}

impl StripAll for Vec<u8> {
    /// Without its trailing `b` bytes, as `$(cat FILE)` drops newlines.
    fn strip_suffix_all(&self, b: u8) -> &[u8] {
        let mut s = &self[..];
        while let [rest @ .., last] = s {
            if *last != b {
                break;
            }
            s = rest;
        }
        s
    }
}

/// In a temporary git repository, a clean tree passes, and one planted
/// violation of each kind is caught. Planted paths and addresses are joined
/// at run time so that this file passes the check itself.
pub fn self_test() -> Result<()> {
    let tmp = std::env::temp_dir().join(format!(
        "public-check-test-{}-{}",
        std::process::id(),
        crate::util::utc_hms().replace(':', "")
    ));
    let res = self_test_in(&tmp);
    let _ = fs::remove_dir_all(&tmp);
    let failures = res?;
    if failures > 0 {
        println!("public-check-test: {failures} failure(s)");
        return Err(exit_with(1, ""));
    }
    println!("public-check-test: OK");
    Ok(())
}

struct T<'a> {
    repo: &'a Path,
    failures: usize,
}

impl T<'_> {
    fn g(&self, args: &[&str]) -> Result<()> {
        let st = Command::new("git")
            .arg("-C")
            .arg(self.repo)
            .args([
                "-c",
                "user.name=test",
                "-c",
                "user.email=test@example.com",
                "-c",
                "commit.gpgsign=false",
            ])
            .args(args)
            .status()?;
        anyhow::ensure!(st.success(), "git {} failed", args.join(" "));
        Ok(())
    }

    fn write(&self, rel: &str, data: impl AsRef<[u8]>) -> Result<()> {
        let p = self.repo.join(rel);
        if let Some(d) = p.parent() {
            fs::create_dir_all(d)?;
        }
        fs::write(p, data)?;
        Ok(())
    }

    fn plant(&self, rel: &str, text: &str) -> Result<()> {
        self.write(rel, format!("{text}\n"))?;
        self.g(&["add", "-f", rel])
    }

    fn commit(&self, msg: &str) -> Result<()> {
        self.g(&["commit", "-q", "--allow-empty", "-m", msg])
    }

    fn reset(&self) -> Result<()> {
        self.g(&["reset", "-q", "--hard", "base"])?;
        self.g(&["clean", "-qfdx"])
    }

    fn run(&self) -> Result<(bool, String)> {
        let r = check(self.repo, Some("base..HEAD"))?;
        let mut out: Vec<String> = r
            .errors
            .iter()
            .map(|e| format!("public-check: {e}"))
            .collect();
        if r.errors.is_empty() {
            out.push(r.ok_line);
        } else {
            out.push(format!("public-check: {} violation(s)", r.errors.len()));
        }
        Ok((r.errors.is_empty(), out.join("\n") + "\n"))
    }

    fn expect_fail(&mut self, label: &str, msg: &str) -> Result<()> {
        let (ok, out) = self.run()?;
        if ok {
            println!("FAIL: {label}: not caught");
            self.failures += 1;
        } else if !out.contains(msg) {
            println!("FAIL: {label}: no '{msg}' in:");
            for l in out.lines() {
                println!("  {l}");
            }
            self.failures += 1;
        } else {
            println!("ok: {label}");
        }
        self.reset()
    }

    fn expect_pass(&mut self, label: &str) -> Result<()> {
        let (ok, out) = self.run()?;
        if ok {
            println!("ok: {label}");
        } else {
            println!("FAIL: {label}: flagged:");
            for l in out.lines() {
                println!("  {l}");
            }
            self.failures += 1;
        }
        self.reset()
    }
}

fn self_test_in(tmp: &Path) -> Result<usize> {
    let repo = tmp.join("repo");
    fs::create_dir_all(&repo)?;
    let mut t = T {
        repo: &repo,
        failures: 0,
    };
    t.g(&["init", "-q"])?;
    t.write(
        ALLOW_FILE,
        "# test allowlist\nallowed.bin\nbig-allowed.txt  # trailing comment\n",
    )?;
    t.write("README.md", format!("{README_LINE}\n"))?;
    t.write(
        "notes.txt",
        "documentation address 192.0.2.17, version 4.36.0\n",
    )?;
    t.g(&["add", "-A"])?;
    t.g(&["commit", "-qm", "Initial commit"])?;
    t.g(&["tag", "base"])?;

    t.expect_pass("clean tree")?;

    t.write("README.md", format!("{README_LINE}\nmore\n"))?;
    t.expect_fail("README with two lines", "README.md must be exactly")?;

    t.write("README.md", README_LINE)?;
    t.expect_fail(
        "README without a final newline",
        "README.md must be exactly",
    )?;

    t.write("README.md", format!("{}\n", README_LINE.replace('`', "")))?;
    t.expect_fail("README without the backticks", "README.md must be exactly")?;

    t.plant("a.txt", concat!("see /ho", "me/alice/x"))?;
    t.expect_fail("home path", "home directory path: a.txt:1")?;

    t.plant("a.txt", concat!("see /Us", "ers/alice/x"))?;
    t.expect_fail("macOS home path", "home directory path: a.txt:1")?;

    t.plant("a.txt", concat!("server at 10.1.2", ".3"))?;
    t.expect_fail(
        "IPv4 address",
        concat!("IPv4 address: a.txt:1: 10.1.2", ".3"),
    )?;

    t.write("b.txt", concat!("see /ho", "me/bob/y\n"))?;
    t.expect_fail("untracked file", "home directory path: b.txt:1")?;

    t.commit("Fix it\n\nCo-Authored-By: Someone <someone@example.com>")?;
    t.expect_fail("co-author trailer", "co-author trailer")?;

    t.commit(&format!("Fix it (#9)\n\n{BOT_TRAILER}"))?;
    t.expect_pass("squash trailer")?;

    t.plant("Foo.olean", "x")?;
    t.expect_fail(".olean file", "build artifact: Foo.olean")?;

    t.plant("lib.a", "x")?;
    t.expect_fail(".a file", "build artifact: lib.a")?;

    t.plant(".lake/build/x.txt", "x")?;
    t.expect_fail(".lake directory", "build directory: .lake/build/x.txt")?;

    t.plant("target/debug/x.txt", "x")?;
    t.expect_fail("target directory", "build directory: target/debug/x.txt")?;

    t.write("blob.bin", b"a\0b")?;
    t.g(&["add", "blob.bin"])?;
    t.expect_fail("binary file", "binary file: blob.bin")?;

    t.write("allowed.bin", b"a\0b")?;
    t.g(&["add", "allowed.bin"])?;
    t.expect_pass("allowlisted binary file")?;

    t.write("big.txt", vec![b'a'; 1048577])?;
    t.g(&["add", "big.txt"])?;
    t.expect_fail("file over 1 MB", "file over 1 MB: big.txt")?;

    t.write("big-allowed.txt", vec![b'a'; 1048577])?;
    t.g(&["add", "big-allowed.txt"])?;
    t.expect_pass("allowlisted file over 1 MB")?;

    Ok(t.failures)
}

#[cfg(test)]
mod tests {
    #[test]
    fn planted_violations_are_caught() {
        let tmp = std::env::temp_dir().join(format!("public-check-unit-{}", std::process::id()));
        let r = super::self_test_in(&tmp);
        let _ = std::fs::remove_dir_all(&tmp);
        assert_eq!(r.unwrap(), 0);
    }
}
