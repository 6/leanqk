//! `fetch`: the exports of `data/cubes.tsv`.
//!
//! For each cube: its subproblem (the formula and the cube's literals as
//! unit clauses), solved by the pinned CaDiCaL (`--lrat --no-binary`), the
//! proof trimmed and restricted to the formula clauses it uses, both checked
//! against their pinned SHA-256, and stated as `(core).Unsat` with the
//! `+kernel` mode of LRAT-Catcher by `kernel_lrat`
//! (`../kernel-compute/lean/lrat-kernel`) under `debug.skipKernelTC`, then
//! exported with the lean4export of the same Lean.

use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use super::pins::{self, Dirs, TC_CATCHER};
use super::sat;
use super::util::{
    Res, err, fetch_url, log, mkdir, need, output, read, run, run_logged, sha256_file, size, tsv,
    unlimited_stack, write,
};

pub struct Opts {
    pub only: Vec<String>,
    pub bundles: bool,
    pub update_pins: bool,
}

struct Ctx<'a> {
    opts: &'a Opts,
    cadical: PathBuf,
    tcdir: PathBuf,
    proj: PathBuf,
    exporter: PathBuf,
    lean_path: String,
    work: PathBuf,
    outdir: PathBuf,
    files: HashMap<(String, String), PathBuf>,
}

pub fn fetch(d: &Dirs, opts: &Opts) -> Res<()> {
    need(&["git", "curl", "make", "c++", "elan"])?;
    let outdir = d.out.join("famous-sat");
    mkdir(&outdir)?;

    log(format!("cadical {}", pins::CADICAL_COMMIT));
    let src = pins::fetch_git(
        d,
        "cadical",
        "https://github.com/arminbiere/cadical",
        pins::CADICAL_COMMIT,
        pins::CADICAL_SHA256,
        opts.update_pins,
    )?;
    let cadical = src.join("build/cadical");
    if !cadical.is_file() {
        let jobs = std::thread::available_parallelism()
            .map_or(1, |n| n.get())
            .to_string();
        run_logged(
            Command::new("./configure").current_dir(&src),
            &d.cache.join("cadical-configure.log"),
        )?;
        run_logged(
            Command::new("make").arg("-j").arg(jobs).current_dir(&src),
            &d.cache.join("cadical-build.log"),
        )?;
    }

    // The public files, by SHA-256, each to CACHE/famous-sat/src/PROBLEM/ROLE.
    let mut files = HashMap::new();
    for r in tsv(&d.fs.join("data/sources.tsv"))? {
        let f = d
            .cache
            .join("famous-sat/src")
            .join(&r["problem"])
            .join(&r["role"]);
        fetch_url(&r["url"], &r["sha256"], &f, opts.update_pins)?;
        files.insert((r["problem"].clone(), r["role"].clone()), f);
    }

    log(format!(
        "BenchLrat (LRAT-Catcher + kernel_lrat) on {TC_CATCHER}"
    ));
    let tcdir = crate::util::tc_bin(TC_CATCHER)?;
    let proj = d.cache.join("lrat-kernel");
    let lean_src = d.kc.join("lean/lrat-kernel");
    if !proj.join(".lake/build").is_dir() || !same_tree(&lean_src, &proj)? {
        let _ = std::fs::remove_dir_all(&proj);
        copy_tree(&lean_src, &proj)?;
    }
    let path = super::util::path_with(&tcdir);
    run_logged(
        Command::new("lake")
            .arg("build")
            .current_dir(&proj)
            .env("PATH", &path),
        &d.cache.join("lrat-kernel-build.log"),
    )?;
    let exporter = pins::build_exporter(d, "430", pins::LEAN4EXPORT_430, TC_CATCHER)?;
    let lean_path = output(
        Command::new("lake")
            .args(["env", "printenv", "LEAN_PATH"])
            .current_dir(&proj)
            .env("PATH", &path),
    )?
    .trim()
    .to_string();

    let work = d.cache.join("famous-sat/work");
    mkdir(&work)?;
    let cx = Ctx {
        opts,
        cadical,
        tcdir,
        proj,
        exporter,
        lean_path,
        work,
        outdir,
        files,
    };

    log("base");
    let tests = cx.proj.join(".lake/packages/LRATCatcher/LRATCatcher/Tests");
    let b = cx.work.join("base");
    mkdir(&b)?;
    for (from, to) in [("tiny.cnf", "p.cnf"), ("tiny.lrat", "p.lrat")] {
        std::fs::copy(tests.join(from), b.join(to)).map_err(|e| anyhow::anyhow!("{from}: {e}"))?;
    }
    write(&b.join("solve_s"), "0.00")?;
    cx.export_set("base", &["base".to_string()])?;
    cx.row("base", "base", "-", "-", &["base".to_string()])?;

    let only = |s: &str| opts.only.is_empty() || opts.only.iter().any(|o| o == s);
    let mut bundles: BTreeMap<String, (String, Vec<String>)> = BTreeMap::new();
    for r in tsv(&d.fs.join("data/cubes.tsv"))? {
        let (label, set, problem, cube) = (&r["label"], &r["set"], &r["problem"], &r["cube"]);
        let pins = (r["cnf_sha256"].as_str(), r["lrat_sha256"].as_str());
        if matches!(set.as_str(), "sample" | "full" | "renumbered") {
            if !only(label) {
                continue;
            }
            log(format!("{label}: {problem} cube {cube}"));
            cx.solve(label, problem, cube, pins, set)?;
            cx.export_set(label, std::slice::from_ref(label))?;
            cx.row(label, set, problem, cube, std::slice::from_ref(label))?;
        } else {
            if !opts.bundles || !only(set) {
                continue;
            }
            log(format!("{set}: {label}, {problem} cube {cube}"));
            let how = if set.ends_with("-renumbered") {
                "renumbered"
            } else if set.ends_with("-full") {
                "full"
            } else {
                "sample"
            };
            cx.solve(label, problem, cube, pins, how)?;
            let e = bundles
                .entry(set.clone())
                .or_insert_with(|| (problem.clone(), Vec::new()));
            e.1.push(label.clone());
        }
    }
    for (b, (problem, labels)) in &bundles {
        log(format!("{b}: {} theorems", labels.len()));
        cx.export_set(b, labels)?;
        cx.row(b, "bundle", problem, "-", labels)?;
    }

    // The manifest: every row so far (an --only run keeps the others).
    let rows_dir = cx.outdir.join(".rows");
    let mut rows: Vec<Vec<String>> = Vec::new();
    for e in std::fs::read_dir(&rows_dir)?.flatten() {
        rows.push(
            read(&e.path())?
                .trim_end()
                .split('\t')
                .map(str::to_string)
                .collect(),
        );
    }
    rows.sort_by(|a, b| {
        (&a[2], a[6].parse::<u64>().unwrap_or(0)).cmp(&(&b[2], b[6].parse::<u64>().unwrap_or(0)))
    });
    let mut s = String::from(
        "label\tset\tproblem\tcube\ttheorems\tcnf_bytes\tlrat_bytes\traw_lrat_bytes\texport_bytes\tsolve_s\n",
    );
    for r in rows {
        s.push_str(&r.join("\t"));
        s.push('\n');
    }
    write(&cx.outdir.join("manifest.tsv"), s)?;
    log(format!("wrote {}", cx.outdir.display()));
    Ok(())
}

impl Ctx<'_> {
    /// Leaves WORK/LABEL/{p.cnf,p.lrat}: the core and its trimmed proof (with
    /// `how` `full`, the whole formula; with `renumbered`, the core with its
    /// variables renamed).
    fn solve(
        &self,
        label: &str,
        problem: &str,
        cube: &str,
        pins: (&str, &str),
        how: &str,
    ) -> Res<()> {
        let d = self.work.join(label);
        mkdir(&d)?;
        let file = |role: &str| {
            self.files
                .get(&(problem.to_string(), role.to_string()))
                .ok_or_else(|| {
                    anyhow::anyhow!("{label}: no {role} for {problem} in data/sources.tsv")
                })
        };
        let index: usize = cube
            .parse()
            .map_err(|_| anyhow::anyhow!("{label}: bad cube {cube}"))?;
        let (f_cnf, f_lrat, trim) = (d.join("f.cnf"), d.join("f.lrat"), d.join("f.trim.lrat"));
        sat::cube_cnf(file("formula")?, file("cubes")?, index, &f_cnf)?;
        let start = Instant::now();
        let out = Command::new(&self.cadical)
            .args(["-q", "--lrat", "--no-binary"])
            .arg(&f_cnf)
            .arg(&f_lrat)
            .output()
            .map_err(|e| anyhow::anyhow!("cadical: {e}"))?;
        write(
            &d.join("solve_s"),
            format!("{:.2}", start.elapsed().as_secs_f64()),
        )?;
        if !String::from_utf8_lossy(&out.stdout)
            .lines()
            .any(|l| l.starts_with("s UNSATISFIABLE"))
        {
            return err(format!("{label}: cube {cube} is not unsatisfiable"));
        }
        write(&d.join("raw_bytes"), size(&f_lrat).to_string())?;
        sat::lrat_trim(&f_lrat, &trim)?;
        let (p_cnf, p_lrat) = (d.join("p.cnf"), d.join("p.lrat"));
        match how {
            "full" => {
                std::fs::rename(&f_cnf, &p_cnf)?;
                std::fs::rename(&trim, &p_lrat)?;
            }
            "renumbered" => {
                let (c_cnf, c_lrat) = (d.join("c.cnf"), d.join("c.lrat"));
                sat::lrat_core(&f_cnf, &trim, &c_cnf, &c_lrat)?;
                sat::renumber(&c_cnf, &c_lrat, &p_cnf, &p_lrat)?;
                for f in [&c_cnf, &c_lrat] {
                    let _ = std::fs::remove_file(f);
                }
            }
            _ => sat::lrat_core(&f_cnf, &trim, &p_cnf, &p_lrat)?,
        }
        for f in [&f_cnf, &f_lrat, &trim] {
            let _ = std::fs::remove_file(f);
        }
        let got = (sha256_file(&p_cnf)?, sha256_file(&p_lrat)?);
        write(
            &d.join("sha256"),
            format!("{label}\t{}\t{}\n", got.0, got.1),
        )?;
        for (what, got, want) in [("cnf", &got.0, pins.0), ("lrat", &got.1, pins.1)] {
            if got != want {
                if !self.opts.update_pins {
                    return err(format!("{label}: {what} SHA-256 is {got}, expected {want}"));
                }
                log(format!("{label}: {what} SHA-256 is {got} (pinned: {want})"));
            }
        }
        Ok(())
    }

    /// One module with a theorem `bench_LABEL` per label, exported to
    /// OUT/famous-sat/NAME.ndjson.
    fn export_set(&self, name: &str, labels: &[String]) -> Res<()> {
        let m = format!("Famous_{}", name.replace('-', "_"));
        let dir = self.work.join("modules");
        let mut src = String::from("import BenchLrat\nset_option debug.skipKernelTC true\n");
        let names: Vec<String> = labels
            .iter()
            .map(|l| format!("bench_{}", l.replace('-', "_")))
            .collect();
        for (l, n) in labels.iter().zip(&names) {
            let p = self.work.join(l);
            src.push_str(&format!(
                "kernel_lrat {n} \"{}\" \"{}\"\n",
                p.join("p.cnf").display(),
                p.join("p.lrat").display()
            ));
        }
        let lean = dir.join(format!("{m}.lean"));
        write(&lean, src)?;
        let path = super::util::path_with(&self.tcdir);
        run(unlimited_stack(
            Command::new("lake")
                .arg("env")
                .arg("lean")
                .arg("-R")
                .arg(&dir)
                .arg("-o")
                .arg(dir.join(format!("{m}.olean")))
                .arg(&lean)
                .current_dir(&self.proj)
                .env("PATH", &path),
        ))?;
        let out = std::fs::File::create(self.outdir.join(format!("{name}.ndjson")))?;
        run(unlimited_stack(
            Command::new(&self.exporter)
                .arg(&m)
                .arg("--")
                .args(&names)
                .current_dir(&self.proj)
                .env("PATH", &path)
                .env("LEAN_PATH", format!("{}:{}", dir.display(), self.lean_path))
                .stdout(out),
        ))
    }

    /// The manifest row of an export.
    fn row(&self, name: &str, set: &str, problem: &str, cube: &str, labels: &[String]) -> Res<()> {
        let (mut cnf, mut lrat, mut raw, mut secs) = (0u64, 0u64, 0u64, 0f64);
        for l in labels {
            let p = self.work.join(l);
            cnf += size(&p.join("p.cnf"));
            let l_bytes = size(&p.join("p.lrat"));
            lrat += l_bytes;
            raw += read(&p.join("raw_bytes"))
                .ok()
                .and_then(|s| s.trim().parse().ok())
                .unwrap_or(l_bytes);
            secs += read(&p.join("solve_s"))?
                .trim()
                .parse::<f64>()
                .unwrap_or(0.0);
        }
        let exp = size(&self.outdir.join(format!("{name}.ndjson")));
        write(
            &self.outdir.join(".rows").join(name),
            format!(
                "{name}\t{set}\t{problem}\t{cube}\t{}\t{cnf}\t{lrat}\t{raw}\t{exp}\t{secs:.2}\n",
                labels.len()
            ),
        )
    }
}

fn same_tree(a: &Path, b: &Path) -> Res<bool> {
    let Ok(rd) = std::fs::read_dir(a) else {
        return Ok(false);
    };
    for e in rd.flatten() {
        let (pa, pb) = (e.path(), b.join(e.file_name()));
        if pa.is_dir() {
            if !same_tree(&pa, &pb)? {
                return Ok(false);
            }
        } else if std::fs::read(&pa).ok() != std::fs::read(&pb).ok() {
            return Ok(false);
        }
    }
    Ok(true)
}

fn copy_tree(a: &Path, b: &Path) -> Res<()> {
    mkdir(b)?;
    for e in std::fs::read_dir(a)?.flatten() {
        let (pa, pb) = (e.path(), b.join(e.file_name()));
        if pa.is_dir() {
            copy_tree(&pa, &pb)?;
        } else {
            std::fs::copy(&pa, &pb).map_err(|e| anyhow::anyhow!("{}: {e}", pa.display()))?;
        }
    }
    Ok(())
}
