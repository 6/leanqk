//! `cargo xtask matcert`: the matrix certificates of bench/certificates.
//!
//! `gen` writes one certificate (`certgen.rs`); `exports` makes every certificate of
//! `bench/certificates/data/certificates.tsv`, checks its pinned SHA-256, states it with
//! the `mat_cert` command of the Lean package `MatCert` and exports the theorem's closure;
//! `measure` runs `kc measure` on those exports; `table` prints the measurements as a
//! Markdown table, one row per export and one column per checker.

mod certgen;

use crate::kc::{self, Dirs, Io, Kc};
use crate::util::{self, cell, cmd_in, read_tsv, root};
use anyhow::{Result, anyhow, bail};
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(clap::Subcommand)]
pub enum Cmd {
    /// Write one certificate.
    ///
    /// inverse: a pseudo-random N x N matrix A with entries in [0, P) and its inverse B
    /// modulo the prime P (Gauss-Jordan elimination mod P), so that A * B = 1 (mod P).
    /// nonsingular: a pseudo-random N x N integer matrix A with entries in [-BOUND, BOUND],
    /// its determinant d and its adjugate B (fraction-free Gauss-Jordan elimination), so
    /// that A * B = d * 1 over the integers, d != 0.
    ///
    /// The entries come from splitmix64 seeded with SEED, so the output depends only on
    /// the arguments; a seed whose matrix is singular is refused. The certificate is
    /// checked by multiplying it out before it is written. Output: a header line
    /// `inverse P N` or `nonsingular N D`, then the N rows of A and the N rows of B, one
    /// row per line, entries separated by single spaces.
    Gen {
        #[command(subcommand)]
        kind: GenKind,
    },
    /// Make, state and export every certificate of data/certificates.tsv.
    ///
    /// For each row: make the certificate (as `gen`; its SHA-256 is pinned in the table),
    /// state it as a theorem with `mat_cert` (MatCert/Cmd.lean: `MatCert.InvertibleMod p n
    /// A` or `MatCert.Nonsingular n A`, proved by running the checker `MatCert.check` in
    /// the kernel), and export the theorem's closure with the lean4export of Lean v4.34.0
    /// (the toolchain and lean4export pins of `kc`).
    ///
    /// A label ending in -corrupt is the same certificate with one entry of B changed, so
    /// that its theorem is false: a checker has to reject that export. Certificates with
    /// n <= 16 are added with Lean's kernel check on, so Lean's kernel has accepted what
    /// those exports contain; the larger ones with `debug.skipKernelTC true` (Lean's
    /// kernel needs about 30 s and 8 GB for n = 64 already).
    ///
    /// Writes OUT/certificates/LABEL.ndjson and OUT/certificates/manifest.tsv (label,
    /// kind, n, certificate bytes, export bytes, certificate SHA-256).
    Exports {
        #[command(flatten)]
        dirs: Dirs,
        /// Only these labels (comma list).
        #[arg(long, value_name = "LABELS")]
        only: Option<String>,
        /// Report a certificate SHA-256 that differs from its pin instead of stopping.
        #[arg(long)]
        update_pins: bool,
    },
    /// Time the checkers on the exports, with `kc measure`.
    ///
    /// The exports of data/certificates.tsv (or --only) that `exports` wrote, in table
    /// order; the TSV is OUT/cert-measurements.tsv unless --tsv says otherwise.
    Measure {
        #[command(flatten)]
        dirs: Dirs,
        /// Only these labels (comma list).
        #[arg(long, value_name = "LABELS")]
        only: Option<String>,
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
        /// The TSV (default: OUT/cert-measurements.tsv); replaced unless --append.
        #[arg(long, value_name = "FILE")]
        tsv: Option<PathBuf>,
        /// Add to the TSV instead of replacing it.
        #[arg(long)]
        append: bool,
    },
    /// Print the measurements as a Markdown table, one row per export (in manifest
    /// order) and one column per checker. A run with a longer limit follows the
    /// shortest one in its cell, as `timeout; 123 s, 456 at 600 s`.
    Table {
        measurements: PathBuf,
        manifest: PathBuf,
    },
}

#[derive(clap::Subcommand)]
pub enum GenKind {
    /// A matrix modulo the prime P and its inverse.
    Inverse {
        p: u64,
        n: usize,
        seed: u64,
        out: PathBuf,
        /// Add 1 to the last entry of B after checking (a wrong certificate).
        #[arg(long)]
        corrupt: bool,
    },
    /// An integer matrix, its determinant and its adjugate.
    Nonsingular {
        n: usize,
        bound: u64,
        seed: u64,
        out: PathBuf,
        /// Add 1 to the last entry of B after checking (a wrong certificate).
        #[arg(long)]
        corrupt: bool,
    },
}

pub fn main(c: Cmd) -> Result<()> {
    let update_env = std::env::var("KC_UPDATE_PINS").is_ok_and(|v| v == "1");
    match c {
        Cmd::Gen { kind } => {
            let (cert, out, corrupt) = match kind {
                GenKind::Inverse {
                    p,
                    n,
                    seed,
                    out,
                    corrupt,
                } => (certgen::inverse(p, n, seed), out, corrupt),
                GenKind::Nonsingular {
                    n,
                    bound,
                    seed,
                    out,
                    corrupt,
                } => (certgen::nonsingular(n, bound, seed), out, corrupt),
            };
            let mut cert = cert.map_err(|e| anyhow!("matcert gen: {e}"))?;
            if corrupt {
                cert.corrupt();
            }
            fs::write(&out, cert.render()).map_err(|e| anyhow!("{}: {e}", out.display()))
        }
        Cmd::Exports {
            dirs,
            only,
            update_pins,
        } => {
            let k = Kc::new("matcert-exports", &dirs, update_pins || update_env);
            exports(&k, only.as_deref(), update_pins || update_env)
        }
        Cmd::Measure {
            dirs,
            only,
            timeout,
            mem_mib,
            checkers,
            tsv,
            append,
        } => {
            let k = Kc::new("matcert-measure", &dirs, false);
            let tsv = tsv.unwrap_or_else(|| k.out.join("cert-measurements.tsv"));
            let files: Vec<PathBuf> = rows(only.as_deref())?
                .iter()
                .map(|r| {
                    k.out
                        .join("certificates")
                        .join(format!("{}.ndjson", r.label))
                })
                .filter(|p| p.is_file())
                .collect();
            if files.is_empty() {
                bail!("no exports (run `cargo xtask matcert exports` first)");
            }
            kc::measure(&k, &timeout, mem_mib, &checkers, &tsv, append, &files)
        }
        Cmd::Table {
            measurements,
            manifest,
        } => {
            print!("{}", table(&measurements, &manifest)?);
            Ok(())
        }
    }
}

fn certs_dir() -> PathBuf {
    root().join("bench/certificates")
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

fn rows(only: Option<&str>) -> Result<Vec<Row>> {
    let only: Option<Vec<&str>> = only.map(|o| o.split(',').collect());
    let mut out = Vec::new();
    for r in read_tsv(&certs_dir().join("data/certificates.tsv"))? {
        let label = cell(&r, "label");
        if only.as_ref().is_some_and(|o| !o.contains(&label)) {
            continue;
        }
        let num = |c: &str| {
            cell(&r, c)
                .parse::<u64>()
                .map_err(|_| anyhow!("certificates.tsv: {label}: bad {c}"))
        };
        out.push(Row {
            label: label.to_string(),
            kind: cell(&r, "kind").to_string(),
            n: num("n")? as usize,
            param: num("param")?,
            seed: num("seed")?,
            sha: cell(&r, "cert_sha256").to_string(),
        });
    }
    Ok(out)
}

fn exports(k: &Kc, only: Option<&str>, update: bool) -> Result<()> {
    let io = Io(None);
    let certs = certs_dir();
    let tc = kc::TC_MAIN;
    let have = fs::read_to_string(certs.join("lean-toolchain"))?;
    if have.trim() != tc {
        bail!(
            "bench/certificates/lean-toolchain is {}, not {tc}",
            have.trim()
        );
    }
    k.log(&io, &format!("MatCert on {tc}"));
    let tcdir = kc::tc_bin(&io, tc)?;
    let path = util::path_with(&tcdir);
    let proj = k.cache.join("matcert");
    let _ = fs::remove_dir_all(&proj);
    fs::create_dir_all(&proj)?;
    for f in [
        "lakefile.toml",
        "lean-toolchain",
        "MatCert.lean",
        "lake-manifest.json",
    ] {
        fs::copy(certs.join(f), proj.join(f)).map_err(|e| anyhow!("{f}: {e}"))?;
    }
    util::copy_tree(&certs.join("MatCert"), &proj.join("MatCert"), true)?;
    kc::run_logged_seq(
        &mut [cmd_in("lake", &proj).arg("build").env("PATH", &path)],
        &k.cache.join("matcert-build.log"),
        30,
        "building MatCert failed",
    )?;
    let exporter = k.build_exporter("434", kc::LEAN4EXPORT_434, tc)?;
    let lean_path = util::output(
        cmd_in("lake", &proj)
            .args(["env", "printenv", "LEAN_PATH"])
            .env("PATH", &path),
    )?;
    let lean_path = lean_path.trim();

    let outdir = k.out.join("certificates");
    let rowdir = outdir.join(".rows"); // one manifest row per label, so --only keeps the others
    fs::create_dir_all(&rowdir)?;
    let work = k.cache.join("certificates-work");
    for row in rows(only)? {
        let d = work.join(&row.label);
        let _ = fs::remove_dir_all(&d);
        fs::create_dir_all(&d)?;
        k.log(&io, &format!("{}: {} n={}", row.label, row.kind, row.n));
        let cert = match row.kind.as_str() {
            "inverse" => certgen::inverse(row.param, row.n, row.seed),
            "nonsingular" => certgen::nonsingular(row.n, row.param, row.seed),
            other => bail!("{}: unknown kind {other}", row.label),
        };
        let mut cert = cert.map_err(|e| anyhow!("{}: {e}", row.label))?;
        let corrupt = row.label.ends_with("-corrupt");
        if corrupt {
            cert.corrupt();
        }
        let text = cert.render();
        let got = util::sha256_hex(text.as_bytes());
        if got != row.sha {
            let msg = format!(
                "{}: certificate SHA-256 is {got}, expected {}",
                row.label, row.sha
            );
            if !update {
                bail!("{msg}");
            }
            k.log(&io, &msg);
        }
        let cert_file = d.join("cert.txt");
        fs::write(&cert_file, &text)?;
        let id = row.label.replace('-', "_");
        let (module, thm) = (format!("Bench_{id}"), format!("bench_{id}"));
        let skip = if row.n <= 16 && !corrupt {
            ""
        } else {
            "set_option debug.skipKernelTC true\n"
        };
        let lean_file = d.join(format!("{module}.lean"));
        fs::write(
            &lean_file,
            format!(
                "import MatCert\n{skip}mat_cert {thm} \"{}\"\n",
                cert_file.display()
            ),
        )?;
        util::run(
            kc::lake_env(&proj)
                .arg("lean")
                .arg("-R")
                .arg(&d)
                .arg("-o")
                .arg(d.join(format!("{module}.olean")))
                .arg(&lean_file)
                .env("PATH", &path),
        )?;
        let ndjson = outdir.join(format!("{}.ndjson", row.label));
        let mut exp = cmd_in(&exporter, &proj);
        exp.args([module.as_str(), "--", thm.as_str()])
            .env("PATH", &path)
            .env("LEAN_PATH", format!("{}:{lean_path}", d.display()));
        util::unlimited_stack(&mut exp);
        kc::run_to_file(&mut exp, &ndjson)?;
        fs::write(
            rowdir.join(&row.label),
            format!(
                "{}\t{}\t{}\t{}\t{}\t{got}\n",
                row.label,
                row.kind,
                row.n,
                text.len(),
                util::file_size(&ndjson)?
            ),
        )?;
    }
    // the manifest: every row made so far, by kind, then n, then label
    let mut lines: Vec<(String, usize, String)> = Vec::new();
    for e in fs::read_dir(&rowdir)? {
        let t = fs::read_to_string(e?.path())?;
        let f: Vec<&str> = t.split('\t').collect();
        if f.len() < 3 {
            continue;
        }
        lines.push((f[1].to_string(), f[2].parse().unwrap_or(0), t));
    }
    lines.sort();
    let mut manifest = String::from("label\tkind\tn\tcert_bytes\texport_bytes\tcert_sha256\n");
    lines.iter().for_each(|(_, _, t)| manifest.push_str(t));
    fs::write(outdir.join("manifest.tsv"), manifest)?;
    k.log(&io, &format!("wrote {}", outdir.display()));
    Ok(())
}

const CHECKERS: [&str; 4] = ["nitrolean", "leanchecker", "gruszka", "nano-lean"];

/// `1234567` as `1 234 567`.
fn grouped(s: &str) -> String {
    let digits: Vec<char> = s.chars().collect();
    let mut out = String::new();
    for (i, c) in digits.iter().enumerate() {
        if i > 0 && (digits.len() - i).is_multiple_of(3) {
            out.push(' ');
        }
        out.push(*c);
    }
    out
}

fn secs(s: &str) -> String {
    let x: f64 = s.parse().unwrap_or(f64::NAN);
    if x < 10.0 {
        format!("{x:.2} s")
    } else {
        format!("{x:.1} s")
    }
}

/// A cell: `time, MiB` when the checker answered, else the verdict; runs with a longer
/// limit follow, as `timeout; 123 s, 456 at 600 s`.
fn table_cell(runs: &mut [&HashMap<String, String>]) -> String {
    runs.sort_by_key(|r| cell(r, "limit_s").parse::<u64>().unwrap_or(0));
    let one = |r: &HashMap<String, String>| match cell(r, "verdict") {
        "accepted" => format!(
            "{}, {}",
            secs(cell(r, "wall_s")),
            grouped(cell(r, "peak_rss_mib"))
        ),
        v => v.to_string(),
    };
    let mut out = one(runs[0]);
    for r in &runs[1..] {
        out.push_str(&format!("; {} at {} s", one(r), cell(r, "limit_s")));
    }
    out
}

fn table(measurements: &Path, manifest: &Path) -> Result<String> {
    let meas = read_tsv(measurements)?;
    let manifest = read_tsv(manifest)?;
    let mut out = format!(
        "| export | n | certificate bytes | {} |\n| --- | ---: | ---: |{}\n",
        CHECKERS.join(" | "),
        " --- |".repeat(CHECKERS.len())
    );
    for m in &manifest {
        let label = cell(m, "label");
        let cells: Vec<String> = CHECKERS
            .iter()
            .map(|c| {
                let mut runs: Vec<_> = meas
                    .iter()
                    .filter(|r| cell(r, "export") == label && cell(r, "checker") == *c)
                    .collect();
                if runs.is_empty() {
                    "-".into()
                } else {
                    table_cell(&mut runs)
                }
            })
            .collect();
        out.push_str(&format!(
            "| {label} | {} | {} | {} |\n",
            cell(m, "n"),
            grouped(cell(m, "cert_bytes")),
            cells.join(" | ")
        ));
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn certificates_match_their_pins() {
        // the small rows of the table (the large ones take seconds in a debug build)
        for r in rows(None).unwrap().iter().filter(|r| r.n <= 32) {
            let mut c = match r.kind.as_str() {
                "inverse" => certgen::inverse(r.param, r.n, r.seed),
                _ => certgen::nonsingular(r.n, r.param, r.seed),
            }
            .unwrap();
            if r.label.ends_with("-corrupt") {
                c.corrupt();
            }
            assert_eq!(
                util::sha256_hex(c.render().as_bytes()),
                r.sha,
                "{}",
                r.label
            );
        }
    }

    #[test]
    fn known_inverse() {
        let a = vec![vec![2, 1], vec![1, 1]];
        assert_eq!(
            certgen::inverse_mod(&a, 7).unwrap(),
            vec![vec![1, 6], vec![6, 2]]
        );
        let (d, b) = certgen::det_adjugate(&[vec![2, 1], vec![1, 3]]).unwrap();
        assert_eq!(d, 5.into());
        assert_eq!(
            b,
            vec![vec![3.into(), (-1).into()], vec![(-1).into(), 2.into()]]
        );
    }

    #[test]
    fn formats_cells() {
        assert_eq!(grouped("1234567"), "1 234 567");
        assert_eq!(grouped("123"), "123");
        let row = |limit: &str, verdict: &str, wall: &str, rss: &str| {
            [
                ("limit_s", limit),
                ("verdict", verdict),
                ("wall_s", wall),
                ("peak_rss_mib", rss),
            ]
            .into_iter()
            .map(|(a, b)| (a.to_string(), b.to_string()))
            .collect::<HashMap<_, _>>()
        };
        let (a, b) = (
            row("600", "accepted", "130.68", "192"),
            row("60", "timeout", "60.04", "159"),
        );
        assert_eq!(table_cell(&mut [&a, &b]), "timeout; 130.7 s, 192 at 600 s");
    }
}
