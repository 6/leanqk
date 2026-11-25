//! `cargo xtask kernel-cases`: generates the kernel test cases under
//! tests/kernel.
//!
//! Each case starts from a valid export written by Lean's `leanexport` (Lean
//! is pinned in tests/kernel/lean-toolchain) and applies one targeted
//! mutation, or builds a small export from scratch. The cases are defined in
//! `cases.rs`. A few are exported from Lean v4.34.0 instead
//! (lean/KCases434.lean, with the lean4export commit pinned below, fetched and
//! built on first use); all are checked with the pinned toolchain's
//! leanchecker.
//!
//!   cargo xtask kernel-cases            write tests/kernel/out/cases/*.ndjson
//!   cargo xtask kernel-cases --lean     also run `leanchecker --from-export`
//!   cargo xtask kernel-cases --update   refresh cases.tsv and the committed small exports
//!   cargo xtask kernel-cases --check    fail if cases.tsv or the committed exports are stale

mod cases;
mod export;

use std::collections::{BTreeSet, HashMap, HashSet};
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use anyhow::{Context, Result, bail};

use crate::util::{exit_with, root};
use export::Export;

const SMALL: usize = 16 * 1024; // exports up to this size are committed
const LEAN_TIMEOUT: Duration = Duration::from_secs(600);
/// Lean v4.34.0 and the lean4export commit for it ("bump toolchain to v4.34.0").
const OLD_TOOLCHAIN: &str = "leanprover/lean4:v4.34.0";
const OLD_EXPORTER_URL: &str = "https://github.com/leanprover/lean4export";
const OLD_EXPORTER_COMMIT: &str = "076e8e57707e813375e8f9da8bf989799ace9680";

#[derive(clap::Args)]
pub struct Args {
    /// Run leanchecker on every case.
    #[arg(long)]
    lean: bool,
    /// Rewrite cases.tsv and exports/.
    #[arg(long)]
    update: bool,
    /// Check that cases.tsv and exports/ are current.
    #[arg(long)]
    check: bool,
    /// Comma-separated case ids.
    #[arg(long)]
    only: Option<String>,
}

fn here() -> PathBuf {
    root().join("tests/kernel")
}

fn out_dir() -> PathBuf {
    here().join("out")
}

fn build_dir() -> PathBuf {
    out_dir().join("build")
}

/// A Lean toolchain with the case module built, and its exporter.
pub struct Toolchain {
    bin: PathBuf,
    dir: PathBuf,
    module: String,
    exporter: PathBuf,
    lean_path: std::ffi::OsString,
    cache: HashMap<(Vec<String>, bool), String>,
    old_tc: Option<Box<Toolchain>>,
}

fn run_ok(cmd: &mut Command) -> Result<Vec<u8>> {
    let out = cmd
        .stderr(Stdio::piped())
        .output()
        .with_context(|| format!("cannot run {}", crate::util::describe(cmd)))?;
    if !out.status.success() {
        bail!(
            "{} failed ({}):\n{}",
            crate::util::describe(cmd),
            out.status,
            String::from_utf8_lossy(&out.stderr)
        );
    }
    Ok(out.stdout)
}

fn mtime(p: &Path) -> Option<std::time::SystemTime> {
    fs::metadata(p).and_then(|m| m.modified()).ok()
}

impl Toolchain {
    fn new(bin: PathBuf, dir: PathBuf, module: &str, exporter: Option<PathBuf>) -> Result<Self> {
        let exporter = exporter.unwrap_or_else(|| bin.join("leanexport"));
        let lean_path =
            std::env::join_paths([bin.join("..").join("lib").join("lean"), dir.clone()])?;
        Ok(Toolchain {
            bin,
            dir,
            module: module.to_string(),
            exporter,
            lean_path,
            cache: HashMap::new(),
            old_tc: None,
        })
    }

    /// The toolchain of tests/kernel/lean-toolchain.
    fn pinned() -> Result<Self> {
        let out = run_ok(
            Command::new("elan")
                .args(["which", "lean"])
                .current_dir(here()),
        )?;
        let lean = PathBuf::from(String::from_utf8(out)?.trim());
        let bin = lean
            .parent()
            .context("elan which lean: no directory")?
            .to_path_buf();
        Toolchain::new(bin, build_dir(), "KCases", None)
    }

    /// The environment of the toolchain's commands. They run in
    /// tests/kernel, as `cd tests/kernel` did for the Python generator: Lean
    /// names a module given as a file by its path from the working
    /// directory, and private names contain the module name.
    fn env(&self, c: &mut Command) {
        c.env("LEAN_PATH", &self.lean_path).current_dir(here());
    }

    fn build(&self) -> Result<()> {
        fs::create_dir_all(&self.dir)?;
        let src = here().join("lean").join(format!("{}.lean", self.module));
        let olean = self.dir.join(format!("{}.olean", self.module));
        if mtime(&olean).is_none() || mtime(&olean) < mtime(&src) {
            let mut c = Command::new(self.bin.join("lean"));
            c.arg("-o").arg(&olean).arg(&src).stdout(Stdio::null());
            self.env(&mut c);
            crate::util::run(&mut c)?;
        }
        Ok(())
    }

    /// The Lean v4.34.0 toolchain, for the cases of lean/KCases434.lean.
    pub fn old(&mut self) -> Result<&mut Toolchain> {
        if self.old_tc.is_none() {
            let st = Command::new("elan")
                .args(["toolchain", "install", OLD_TOOLCHAIN])
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .status()?;
            anyhow::ensure!(
                st.success(),
                "elan toolchain install {OLD_TOOLCHAIN} failed"
            );
            let out = run_ok(Command::new("elan").args([
                "run",
                OLD_TOOLCHAIN,
                "lean",
                "--print-prefix",
            ]))?;
            let lean = PathBuf::from(String::from_utf8(out)?.trim());
            let src = out_dir().join(format!("lean4export-{}", &OLD_EXPORTER_COMMIT[..12]));
            let exe = src.join(".lake/build/bin/lean4export");
            if !exe.exists() {
                let _ = fs::remove_dir_all(&src);
                fs::create_dir_all(&src)?;
                let git = || {
                    let mut c = Command::new("git");
                    c.arg("-C").arg(&src);
                    c
                };
                crate::util::run(git().args(["init", "-q"]))?;
                crate::util::run(git().args([
                    "fetch",
                    "-q",
                    "--depth",
                    "1",
                    OLD_EXPORTER_URL,
                    OLD_EXPORTER_COMMIT,
                ]))?;
                crate::util::run(git().args([
                    "-c",
                    "advice.detachedHead=false",
                    "checkout",
                    "-q",
                    "FETCH_HEAD",
                ]))?;
                crate::util::run(
                    Command::new("elan")
                        .args(["run", OLD_TOOLCHAIN, "lake", "build"])
                        .current_dir(&src)
                        .stdout(Stdio::null()),
                )?;
            }
            let mut dir = build_dir().into_os_string();
            dir.push("-v4.34.0");
            let tc = Toolchain::new(lean.join("bin"), dir.into(), "KCases434", Some(exe))?;
            tc.build()?;
            self.old_tc = Some(Box::new(tc));
        }
        Ok(self.old_tc.as_mut().unwrap())
    }

    /// The closure of `consts` as exported by the toolchain's exporter.
    pub fn export(&mut self, consts: &[&str], unsafe_: bool) -> Result<Export> {
        let key = (consts.iter().map(|s| s.to_string()).collect(), unsafe_);
        if !self.cache.contains_key(&key) {
            let mut c = Command::new(&self.exporter);
            if unsafe_ {
                c.arg("--export-unsafe");
            }
            c.arg(&self.module).arg("--").args(consts);
            self.env(&mut c);
            let out = String::from_utf8(run_ok(&mut c)?)?;
            self.cache.insert(key.clone(), out);
        }
        Ok(Export::new(&self.cache[&key]))
    }

    /// leanchecker's verdict on an export, and its message.
    fn check(&self, path: &Path) -> Result<(String, String)> {
        let mut c = Command::new(self.bin.join("leanchecker"));
        c.arg("--from-export")
            .arg(path)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        self.env(&mut c);
        let mut child = c.spawn().context("cannot run leanchecker")?;
        let mut so = child.stdout.take().unwrap();
        let mut se = child.stderr.take().unwrap();
        let t1 = std::thread::spawn(move || {
            let mut b = Vec::new();
            let _ = so.read_to_end(&mut b);
            b
        });
        let t2 = std::thread::spawn(move || {
            let mut b = Vec::new();
            let _ = se.read_to_end(&mut b);
            b
        });
        let start = Instant::now();
        let status = loop {
            if let Some(st) = child.try_wait()? {
                break Some(st);
            }
            if start.elapsed() > LEAN_TIMEOUT {
                let _ = child.kill();
                let _ = child.wait();
                break None;
            }
            std::thread::sleep(Duration::from_millis(20));
        };
        let out = [t1.join().unwrap_or_default(), t2.join().unwrap_or_default()].concat();
        let Some(status) = status else {
            return Ok(("timeout".into(), String::new()));
        };
        let msg = String::from_utf8_lossy(&out)
            .trim()
            .replace(['\n', '\t'], " ");
        if status.success() {
            return Ok(("accept".into(), msg));
        }
        if msg.contains("rejects") || msg.contains("uncaught exception") {
            return Ok(("reject".into(), msg));
        }
        let code = status.code().unwrap_or(-1);
        Ok((format!("error({code})"), msg))
    }
}

fn tsv_rows(results: &HashMap<String, String>) -> String {
    let mut rows = vec!["id\trule\texpected\tlean\twhy".to_string()];
    for c in cases::cases() {
        let lean = results.get(c.id).map(String::as_str).unwrap_or("?");
        rows.push([c.id, c.rule, c.expected, lean, c.why].join("\t"));
    }
    rows.join("\n") + "\n"
}

fn read_tsv(tsv: &Path) -> Result<HashMap<String, String>> {
    let mut out = HashMap::new();
    if !tsv.exists() {
        return Ok(out);
    }
    for ln in fs::read_to_string(tsv)?.lines().skip(1) {
        let parts: Vec<&str> = ln.split('\t').collect();
        out.insert(parts[0].to_string(), parts[3].to_string());
    }
    Ok(out)
}

/// Whether Lean's verdict is the expected one.
fn agrees(expected: &str, lean: &str) -> bool {
    expected == "either" || expected == lean
}

pub fn main(args: Args) -> Result<()> {
    let here = here();
    let tsv = here.join("cases.tsv");
    let committed = here.join("exports");
    let mut tc = Toolchain::pinned()?;
    tc.build()?;
    let outdir = out_dir().join("cases");
    fs::create_dir_all(&outdir)?;
    let only: Option<HashSet<String>> = args
        .only
        .as_ref()
        .map(|s| s.split(',').map(str::to_string).collect());
    let all = cases::cases();
    let mut seen = HashSet::new();
    let dup: BTreeSet<&str> = all
        .iter()
        .map(|c| c.id)
        .filter(|i| !seen.insert(*i))
        .collect();
    if !dup.is_empty() {
        let list: Vec<String> = dup.iter().map(|i| format!("'{i}'")).collect();
        return Err(exit_with(
            1,
            format!("duplicate case ids: [{}]", list.join(", ")),
        ));
    }

    let mut texts: Vec<(&str, String)> = Vec::new();
    for c in &all {
        if only.as_ref().is_some_and(|o| !o.contains(c.id)) {
            continue;
        }
        let t = (c.build)(&mut tc).with_context(|| format!("case {}", c.id))?;
        fs::write(outdir.join(format!("{}.ndjson", c.id)), &t)?;
        texts.push((c.id, t));
    }

    let mut results = read_tsv(&tsv)?;
    if args.lean {
        for (id, _) in &texts {
            let c = all.iter().find(|c| c.id == *id).unwrap();
            let (verdict, msg) = tc.check(&outdir.join(format!("{id}.ndjson")))?;
            let flag = if agrees(c.expected, &verdict) {
                ""
            } else {
                "   <-- differs from expected"
            };
            println!(
                "{:<36} expected {:<7} lean {:<7}{}",
                id, c.expected, verdict, flag
            );
            if !flag.is_empty() && !msg.is_empty() {
                println!("    {}", msg.chars().take(300).collect::<String>());
            }
            results.insert(id.to_string(), verdict);
        }
    }

    let small: HashMap<&str, &String> = texts
        .iter()
        .filter(|(_, t)| t.len() <= SMALL)
        .map(|(i, t)| (*i, t))
        .collect();
    if args.update {
        fs::write(&tsv, tsv_rows(&results))?;
        if only.is_none() {
            let _ = fs::remove_dir_all(&committed);
        }
        fs::create_dir_all(&committed)?;
        for (i, t) in &small {
            fs::write(committed.join(format!("{i}.ndjson")), t)?;
        }
    }
    if args.check {
        let mut bad = Vec::new();
        if fs::read_to_string(&tsv)? != tsv_rows(&results) {
            bad.push("cases.tsv".to_string());
        }
        let want: BTreeSet<String> = small.keys().map(|i| format!("{i}.ndjson")).collect();
        let have: BTreeSet<String> = match fs::read_dir(&committed) {
            Ok(d) => d
                .filter_map(|e| e.ok())
                .map(|e| e.file_name().to_string_lossy().into_owned())
                .collect(),
            Err(_) => BTreeSet::new(),
        };
        bad.extend(want.symmetric_difference(&have).cloned());
        for f in want.intersection(&have) {
            let id = &f[..f.len() - ".ndjson".len()];
            if fs::read_to_string(committed.join(f))? != *small[id] {
                bad.push(f.clone());
            }
        }
        if !bad.is_empty() {
            return Err(exit_with(1, format!("stale: {}", bad.join(", "))));
        }
    }
    println!(
        "{} cases, {} small enough to commit",
        texts.len(),
        small.len()
    );
    Ok(())
}
