//! `matcert exports` and `matcert measure`.

use crate::certgen;
use sha2::{Digest, Sha256};
use std::fs;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

const EXPORTS_HELP: &str =
    "usage: matcert exports [--out DIR] [--cache DIR] [--only LABEL,...] [--update-pins]

For each row of data/certificates.tsv: make the certificate (as `matcert gen`; synthetic,
seeded; its SHA-256 is pinned in the table), state it as a theorem with `mat_cert`
(MatCert/Cmd.lean: `MatCert.InvertibleMod p n A` or `MatCert.Nonsingular n A`, proved by
running the checker `MatCert.check` in the kernel), and export the theorem's closure with
the lean4export that matches the toolchain. The toolchain (TC_MAIN, Lean v4.34.0) and the
lean4export commit (LEAN4EXPORT_434) are read from bench/kernel-compute/common.sh, so the
pins are shared with the other benchmarks.

A label ending in -corrupt is the same certificate with one entry of B changed, so that
its theorem is false: a checker has to reject that export.

Certificates with n <= 16 are added with Lean's kernel check on, so Lean's kernel has
accepted what those exports contain. The larger ones are added with
`debug.skipKernelTC true` (Lean's kernel needs about 30 s and 8 GB for n = 64 already);
checking them is what the exports are for.

Writes OUT/certificates/LABEL.ndjson and OUT/certificates/manifest.tsv (label, kind, n,
certificate bytes, export bytes, certificate SHA-256). OUT and CACHE default to
$KC_OUT and $KC_CACHE, else bench/kernel-compute/out and bench/kernel-compute/cache, as
for the other benchmarks. --update-pins reports a SHA-256 that differs from the pinned one
instead of stopping. Needs git, elan (and through it lean and lake).";

const MEASURE_HELP: &str =
    "usage: matcert measure [--out DIR] [--only LABEL,...] [-- MEASURE.SH OPTIONS...]

Runs bench/kernel-compute/measure.sh on the exports that `matcert exports` wrote to
OUT/certificates/ (the rows of data/certificates.tsv, or the --only labels), in table order,
writing OUT/cert-measurements.tsv unless the options after `--` say otherwise (for example
`-- --timeout 600 --checkers nitrolean --append`). Then `matcert table` prints it.";

/// The directories and pins everything works with.
struct Env {
    certs: PathBuf,
    kc: PathBuf,
    out: PathBuf,
    cache: PathBuf,
}

impl Env {
    fn new(out: Option<String>, cache: Option<String>) -> Result<Env, String> {
        let certs = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
        let certs = certs
            .canonicalize()
            .map_err(|e| format!("{}: {e}", certs.display()))?;
        let kc = certs
            .join("../kernel-compute")
            .canonicalize()
            .map_err(|e| e.to_string())?;
        let pick = |opt: Option<String>, var: &str, dflt: &str| {
            opt.or_else(|| std::env::var(var).ok())
                .map(PathBuf::from)
                .unwrap_or_else(|| kc.join(dflt))
        };
        let out = pick(out, "KC_OUT", "out");
        let cache = pick(cache, "KC_CACHE", "cache");
        for d in [&out, &cache] {
            fs::create_dir_all(d).map_err(|e| format!("{}: {e}", d.display()))?;
        }
        let out = out.canonicalize().map_err(|e| e.to_string())?;
        let cache = cache.canonicalize().map_err(|e| e.to_string())?;
        Ok(Env {
            certs,
            kc,
            out,
            cache,
        })
    }

    /// A `NAME=value` assignment of bench/kernel-compute/common.sh.
    fn pin(&self, name: &str) -> Result<String, String> {
        let text = fs::read_to_string(self.kc.join("common.sh")).map_err(|e| e.to_string())?;
        text.lines()
            .find_map(|l| l.strip_prefix(&format!("{name}=")))
            .and_then(|v| v.split_whitespace().next())
            .map(str::to_string)
            .ok_or_else(|| format!("{name} not found in common.sh"))
    }
}

/// One row of data/certificates.tsv.
struct Row {
    label: String,
    kind: String,
    n: usize,
    param: u64,
    seed: u64,
    sha: String,
}

fn rows(certs: &Path, only: &Option<Vec<String>>) -> Result<Vec<Row>, String> {
    let text =
        fs::read_to_string(certs.join("data/certificates.tsv")).map_err(|e| e.to_string())?;
    let mut out = Vec::new();
    for line in text.lines().skip(1).filter(|l| !l.is_empty()) {
        let f: Vec<&str> = line.split('\t').collect();
        let [label, kind, n, param, seed, sha] = f[..] else {
            return Err(format!("certificates.tsv: bad row {line}"));
        };
        if only.as_ref().is_some_and(|o| !o.iter().any(|x| x == label)) {
            continue;
        }
        let num = |s: &str| {
            s.parse::<u64>()
                .map_err(|_| format!("certificates.tsv: {s}"))
        };
        out.push(Row {
            label: label.into(),
            kind: kind.into(),
            n: num(n)? as usize,
            param: num(param)?,
            seed: num(seed)?,
            sha: sha.into(),
        });
    }
    Ok(out)
}

fn log(msg: &str) {
    eprintln!("matcert: {msg}");
}

/// Runs `cmd`, with its output to `log` (appended) unless it is already redirected.
fn run(cmd: &mut Command, log: Option<&Path>) -> Result<(), String> {
    if let Some(l) = log {
        let f = fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(l)
            .map_err(|e| e.to_string())?;
        cmd.stdout(f.try_clone().map_err(|e| e.to_string())?)
            .stderr(f);
    }
    let st = cmd
        .status()
        .map_err(|e| format!("{:?}: {e}", cmd.get_program()))?;
    if st.success() {
        Ok(())
    } else {
        let more = log
            .map(|l| format!(" (log: {})", l.display()))
            .unwrap_or_default();
        Err(format!(
            "{:?} {:?} failed: {st}{more}",
            cmd.get_program(),
            cmd.get_args().collect::<Vec<_>>()
        ))
    }
}

fn output(cmd: &mut Command) -> Result<String, String> {
    let o = cmd
        .stderr(Stdio::inherit())
        .output()
        .map_err(|e| format!("{:?}: {e}", cmd.get_program()))?;
    if !o.status.success() {
        return Err(format!("{:?} failed: {}", cmd.get_program(), o.status));
    }
    Ok(String::from_utf8_lossy(&o.stdout).trim().to_string())
}

/// No stack limit for the child: elaborating and exporting deep list literals recurses deeply.
fn unlimited_stack(cmd: &mut Command) -> &mut Command {
    // SAFETY: setrlimit is async-signal-safe; nothing else runs between fork and exec.
    unsafe {
        cmd.pre_exec(|| {
            let lim = libc::rlimit {
                rlim_cur: libc::RLIM_INFINITY,
                rlim_max: libc::RLIM_INFINITY,
            };
            libc::setrlimit(libc::RLIMIT_STACK, &lim);
            Ok(())
        })
    }
}

fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

fn copy_dir(from: &Path, to: &Path) -> Result<(), String> {
    fs::create_dir_all(to).map_err(|e| e.to_string())?;
    for e in fs::read_dir(from).map_err(|e| e.to_string())? {
        let e = e.map_err(|e| e.to_string())?;
        let dst = to.join(e.file_name());
        if e.file_type().map_err(|e| e.to_string())?.is_dir() {
            copy_dir(&e.path(), &dst)?;
        } else {
            fs::copy(e.path(), dst).map_err(|e| e.to_string())?;
        }
    }
    Ok(())
}

/// lean4export at `commit`, built with `tc` (the same cache directory as common.sh's
/// `build_exporter 434`).
fn exporter(env: &Env, commit: &str, tc: &str) -> Result<PathBuf, String> {
    let dir = env.cache.join("lean4export-434");
    let bin = dir.join(".lake/build/bin/lean4export");
    if bin.exists() {
        return Ok(bin);
    }
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    let url = env.pin("LEAN4EXPORT_URL")?;
    let git = |args: &[&str]| run(Command::new("git").arg("-C").arg(&dir).args(args), None);
    git(&["init", "-q"])?;
    git(&["remote", "add", "origin", &url])?;
    git(&["fetch", "-q", "--depth", "1", "origin", commit])?;
    git(&["-c", "advice.detachedHead=false", "checkout", "-q", commit])?;
    let got = fs::read_to_string(dir.join("lean-toolchain")).map_err(|e| e.to_string())?;
    if got.trim() != tc {
        return Err(format!(
            "lean4export {commit} is for {}, not {tc}",
            got.trim()
        ));
    }
    run(
        Command::new("elan")
            .args(["run", tc, "lake", "build"])
            .current_dir(&dir),
        None,
    )?;
    Ok(bin)
}

/// `--out`, `--cache`, `--only` and the remaining arguments.
struct Common {
    out: Option<String>,
    cache: Option<String>,
    only: Option<Vec<String>>,
    rest: Vec<String>,
}

fn parse_common(args: &[String], extra: &[&str]) -> Result<Common, String> {
    let (mut out, mut cache, mut only, mut rest) = (None, None, None, Vec::new());
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let mut val = || it.next().cloned().ok_or(format!("{a} needs a value"));
        match a.as_str() {
            "--out" => out = Some(val()?),
            "--cache" => cache = Some(val()?),
            "--only" => only = Some(val()?.split(',').map(str::to_string).collect()),
            "--" => {
                rest.extend(it.by_ref().cloned());
            }
            x if extra.contains(&x) => rest.push(x.to_string()),
            x => return Err(format!("unknown argument {x}")),
        }
    }
    Ok(Common {
        out,
        cache,
        only,
        rest,
    })
}

pub fn exports(args: &[String]) -> Result<(), String> {
    if args.iter().any(|a| a == "-h" || a == "--help") {
        println!("{EXPORTS_HELP}");
        return Ok(());
    }
    let Common {
        out,
        cache,
        only,
        rest,
    } = parse_common(args, &["--update-pins"])?;
    let update = !rest.is_empty() || std::env::var("KC_UPDATE_PINS").is_ok_and(|v| v == "1");
    let env = Env::new(out, cache)?;
    let tc = env.pin("TC_MAIN")?;
    let commit = env.pin("LEAN4EXPORT_434")?;
    let pkg_tc = fs::read_to_string(env.certs.join("lean-toolchain")).map_err(|e| e.to_string())?;
    if pkg_tc.trim() != tc {
        return Err(format!("lean-toolchain is {}, not {tc}", pkg_tc.trim()));
    }

    log(&format!("MatCert on {tc}"));
    if run(
        Command::new("elan")
            .args(["toolchain", "install", &tc])
            .stdout(Stdio::null()),
        None,
    )
    .is_err()
    {
        log("elan toolchain install reported an error; trying the installed toolchain");
    }
    let prefix = output(Command::new("elan").args(["run", &tc, "lean", "--print-prefix"]))?;
    let tcdir = PathBuf::from(prefix).join("bin");
    let path = format!(
        "{}:{}",
        tcdir.display(),
        std::env::var("PATH").unwrap_or_default()
    );
    let proj = env.cache.join("matcert");
    let _ = fs::remove_dir_all(&proj);
    fs::create_dir_all(&proj).map_err(|e| e.to_string())?;
    for f in [
        "lakefile.toml",
        "lean-toolchain",
        "MatCert.lean",
        "lake-manifest.json",
    ] {
        fs::copy(env.certs.join(f), proj.join(f)).map_err(|e| format!("{f}: {e}"))?;
    }
    copy_dir(&env.certs.join("MatCert"), &proj.join("MatCert"))?;
    let build_log = env.cache.join("matcert-build.log");
    let _ = fs::remove_file(&build_log);
    run(
        Command::new("lake")
            .arg("build")
            .current_dir(&proj)
            .env("PATH", &path),
        Some(&build_log),
    )?;
    let exporter = exporter(&env, &commit, &tc)?;
    let lean_path = output(
        Command::new("lake")
            .args(["env", "printenv", "LEAN_PATH"])
            .current_dir(&proj)
            .env("PATH", &path),
    )?;

    let outdir = env.out.join("certificates");
    let rowdir = outdir.join(".rows");
    fs::create_dir_all(&rowdir).map_err(|e| e.to_string())?;
    let work = env.cache.join("certificates-work");
    for row in rows(&env.certs, &only)? {
        let d = work.join(&row.label);
        let _ = fs::remove_dir_all(&d);
        fs::create_dir_all(&d).map_err(|e| e.to_string())?;
        log(&format!("{}: {} n={}", row.label, row.kind, row.n));
        let mut cert = match row.kind.as_str() {
            "inverse" => certgen::inverse(row.param, row.n, row.seed)?,
            "nonsingular" => certgen::nonsingular(row.n, row.param, row.seed)?,
            k => return Err(format!("{}: unknown kind {k}", row.label)),
        };
        let corrupt = row.label.ends_with("-corrupt");
        if corrupt {
            cert.corrupt();
        }
        let text = cert.render();
        let got = sha256_hex(text.as_bytes());
        if got != row.sha {
            let msg = format!(
                "{}: certificate SHA-256 is {got}, expected {}",
                row.label, row.sha
            );
            if !update {
                return Err(msg);
            }
            log(&msg);
        }
        let cert_file = d.join("cert.txt");
        fs::write(&cert_file, &text).map_err(|e| e.to_string())?;
        let id = row.label.replace('-', "_");
        let (module, thm) = (format!("Bench_{id}"), format!("bench_{id}"));
        let skip = if row.n <= 16 && !corrupt {
            ""
        } else {
            "set_option debug.skipKernelTC true\n"
        };
        let src = format!(
            "import MatCert\n{skip}mat_cert {thm} \"{}\"\n",
            cert_file.display()
        );
        let lean_file = d.join(format!("{module}.lean"));
        fs::write(&lean_file, src).map_err(|e| e.to_string())?;
        run(
            unlimited_stack(
                Command::new("lake")
                    .args(["env", "lean", "-R"])
                    .arg(&d)
                    .arg("-o")
                    .arg(d.join(format!("{module}.olean")))
                    .arg(&lean_file)
                    .current_dir(&proj)
                    .env("PATH", &path),
            ),
            None,
        )?;
        let ndjson = outdir.join(format!("{}.ndjson", row.label));
        let f = fs::File::create(&ndjson).map_err(|e| e.to_string())?;
        run(
            unlimited_stack(
                Command::new(&exporter)
                    .args([module.as_str(), "--", thm.as_str()])
                    .current_dir(&proj)
                    .env("PATH", &path)
                    .env("LEAN_PATH", format!("{}:{lean_path}", d.display()))
                    .stdout(f),
            ),
            None,
        )?;
        let size = |p: &Path| fs::metadata(p).map(|m| m.len()).unwrap_or(0);
        fs::write(
            rowdir.join(&row.label),
            format!(
                "{}\t{}\t{}\t{}\t{}\t{got}\n",
                row.label,
                row.kind,
                row.n,
                text.len(),
                size(&ndjson)
            ),
        )
        .map_err(|e| e.to_string())?;
    }
    // the manifest: every row made so far (so --only keeps the others), by kind then n
    let mut lines: Vec<(String, usize, String)> = Vec::new();
    for e in fs::read_dir(&rowdir).map_err(|e| e.to_string())? {
        let t =
            fs::read_to_string(e.map_err(|e| e.to_string())?.path()).map_err(|e| e.to_string())?;
        let f: Vec<&str> = t.split('\t').collect();
        lines.push((f[1].to_string(), f[2].parse().unwrap_or(0), t));
    }
    lines.sort();
    let mut manifest = String::from("label\tkind\tn\tcert_bytes\texport_bytes\tcert_sha256\n");
    lines.iter().for_each(|(_, _, t)| manifest.push_str(t));
    fs::write(outdir.join("manifest.tsv"), manifest).map_err(|e| e.to_string())?;
    log(&format!("wrote {}", outdir.display()));
    Ok(())
}

pub fn measure(args: &[String]) -> Result<(), String> {
    if args.iter().any(|a| a == "-h" || a == "--help") {
        println!("{MEASURE_HELP}");
        return Ok(());
    }
    let Common {
        out, only, rest, ..
    } = parse_common(args, &[])?;
    let env = Env::new(out, None)?;
    let files: Vec<PathBuf> = rows(&env.certs, &only)?
        .iter()
        .map(|r| {
            env.out
                .join("certificates")
                .join(format!("{}.ndjson", r.label))
        })
        .filter(|p| p.exists())
        .collect();
    if files.is_empty() {
        return Err("no exports (run `matcert exports` first)".into());
    }
    let tsv = env.out.join("cert-measurements.tsv");
    run(
        Command::new(env.kc.join("measure.sh"))
            .arg("--out")
            .arg(&tsv)
            .args(&rest)
            .args(&files),
        None,
    )
}
