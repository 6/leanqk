//! `coverage` and `scaling`: the tables of README.md from the TSVs.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use super::util::{Res, err, read, tsv};

const PROBLEMS: [(&str, &str, u64); 4] = [
    ("schur5", "Schur number five", 10_330_615),
    ("keller7", "Keller, dimension 7", 21_557),
    ("ptn", "Pythagorean triples", 1_000_000),
    ("hexagon30", "Empty hexagon", 312_418),
];

fn fmt_bytes(b: f64) -> String {
    for (unit, k) in [
        ("PB", 1e15),
        ("TB", 1e12),
        ("GB", 1e9),
        ("MB", 1e6),
        ("KB", 1e3),
    ] {
        if b >= k {
            return format!("{} {unit}", sig3(b / k));
        }
    }
    format!("{b:.0} B")
}

fn fmt_time(s: f64) -> String {
    for (unit, k) in [
        ("years", 365.25 * 86400.0),
        ("days", 86400.0),
        ("hours", 3600.0),
        ("min", 60.0),
    ] {
        if s >= k {
            return format!("{} {unit}", sig3(s / k));
        }
    }
    format!("{} s", sig3(s))
}

fn sig3(x: f64) -> String {
    if x >= 100.0 {
        format!("{x:.0}")
    } else if x >= 10.0 {
        format!("{x:.1}")
    } else {
        format!("{x:.2}")
    }
}

fn sig2(x: f64) -> String {
    format!("{x:.1e}")
}

/// Per-cube published proof bytes from a log: (column of the cube index,
/// column of the bytes, columns a row must have).
fn published(path: &Path, bytes_col: usize, cols: Option<usize>) -> Res<(f64, HashMap<u64, f64>)> {
    let mut total = 0.0;
    let mut per = HashMap::new();
    for line in read(path)?.lines() {
        let t: Vec<&str> = line.split_whitespace().collect();
        if cols.is_some_and(|c| t.len() != c) || t.len() <= bytes_col {
            continue;
        }
        if let (Ok(i), Ok(b)) = (t[0].parse::<u64>(), t[bytes_col].parse::<f64>()) {
            per.insert(i, b);
            total += b;
        }
    }
    Ok((total, per))
}

fn num(r: &HashMap<String, String>, k: &str) -> f64 {
    r.get(k).and_then(|v| v.parse().ok()).unwrap_or(0.0)
}

/// How much of each whole proof the sample is and how long the whole proof
/// would take at nitrolean's rate on the sample. The whole proof, in bytes
/// of LRAT as the exports state it, is the published size times a factor:
/// for Keller and the Pythagorean triples (per-cube logs) the survey's LRAT
/// bytes over the published bytes of the same cubes, over cubes above 1 MB;
/// for the empty hexagon (180 TB of LRAT) and Schur (2 PB of DRAT) the
/// sample's LRAT bytes over the raw LRAT CaDiCaL wrote, over sample cubes
/// above 1 MB. The rate is LRAT bytes over wall time minus that of `base`,
/// over the sample cubes nitrolean accepts (its longest-limit run).
pub fn coverage(manifest: &Path, survey: &Path, src: &Path, measurements: &[PathBuf]) -> Res<()> {
    let manifest = tsv(manifest)?;
    let survey = tsv(survey)?;
    let mut wall: HashMap<String, (f64, f64)> = HashMap::new();
    for m in measurements {
        for r in tsv(m)? {
            if r["checker"] == "nitrolean" && r["verdict"] == "accepted" {
                let (lim, w) = (num(&r, "limit_s"), num(&r, "wall_s"));
                let e = wall.entry(r["export"].clone()).or_insert((lim, w));
                if lim >= e.0 {
                    *e = (lim, w);
                }
            }
        }
    }
    let Some(&(_, base)) = wall.get("base") else {
        return err("no accepted nitrolean run of base");
    };
    println!(
        "| result | cubes | sampled | sample LRAT | whole proof (published) | whole proof as LRAT here (factor) | sample share | nitrolean rate | whole proof at that rate |"
    );
    println!("| --- | ---: | ---: | ---: | --- | --- | ---: | ---: | ---: |");
    for (p, title, cubes) in PROBLEMS {
        let mine: Vec<_> = manifest
            .iter()
            .filter(|r| r["set"] == "sample" && r["problem"] == p)
            .collect();
        let lrat: f64 = mine.iter().map(|r| num(r, "lrat_bytes")).sum();
        let big: Vec<_> = mine.iter().filter(|r| num(r, "lrat_bytes") > 1e6).collect();
        let raw_factor = big.iter().map(|r| num(r, "lrat_bytes")).sum::<f64>()
            / big
                .iter()
                .map(|r| num(r, "raw_lrat_bytes"))
                .sum::<f64>()
                .max(1.0);
        let (total, factor, pubd) = match p {
            "keller7" | "ptn" => {
                let (total, per) = if p == "keller7" {
                    published(&src.join("keller7/log"), 4, None)?
                } else {
                    published(&src.join("ptn/log"), 7, Some(8))?
                };
                let sv: Vec<_> = survey
                    .iter()
                    .filter(|r| {
                        r["problem"] == p
                            && r["verdict"] == "unsat"
                            && num(r, "lrat_bytes") > 1e6
                            && per.contains_key(&(num(r, "index") as u64))
                    })
                    .collect();
                let f = sv.iter().map(|r| num(r, "lrat_bytes")).sum::<f64>()
                    / sv.iter()
                        .map(|r| per[&(num(r, "index") as u64)])
                        .sum::<f64>();
                let what = if p == "ptn" { "DRAT" } else { "proof" };
                (total, f, format!("{} of {what} (logs)", fmt_bytes(total)))
            }
            "hexagon30" => (180e12, raw_factor, "180 TB of LRAT (paper)".to_string()),
            _ => (2e15, raw_factor, "2 PB of DRAT (paper)".to_string()),
        };
        let whole = total * factor;
        // Proofs under 10 KB take about as long as `base`, so they say
        // nothing about the rate.
        let acc: Vec<_> = mine
            .iter()
            .filter(|r| wall.contains_key(&r["label"]) && num(r, "lrat_bytes") >= 1e4)
            .collect();
        let secs: f64 = acc
            .iter()
            .map(|r| (wall[&r["label"]].1 - base).max(0.0))
            .sum();
        let rate = acc.iter().map(|r| num(r, "lrat_bytes")).sum::<f64>() / secs;
        println!(
            "| {title} | {cubes} | {} ({} of the cubes) | {} | {pubd} | {} ({factor:.2}) | {} | {} | {} |",
            mine.len(),
            sig2(mine.len() as f64 / cubes as f64),
            fmt_bytes(lrat),
            fmt_bytes(whole),
            sig2(lrat / whole),
            if acc.is_empty() {
                "none above 10 KB accepted".to_string()
            } else {
                format!("{}/s", fmt_bytes(rate))
            },
            if acc.is_empty() {
                "-".to_string()
            } else {
                fmt_time(whole / rate)
            }
        );
    }
    Ok(())
}

fn median(mut v: Vec<f64>) -> f64 {
    v.sort_by(f64::total_cmp);
    let n = v.len();
    if n == 0 {
        f64::NAN
    } else if n % 2 == 1 {
        v[n / 2]
    } else {
        (v[n / 2 - 1] + v[n / 2]) / 2.0
    }
}

/// The makespan of handing `times` out in order to the first free of `n`
/// threads, as `--check-threads` does.
fn makespan(times: &[f64], n: usize) -> f64 {
    let mut free = vec![0.0f64; n.max(1)];
    for t in times {
        let i = (0..free.len())
            .min_by(|&a, &b| free[a].total_cmp(&free[b]))
            .unwrap_or(0);
        free[i] += t;
    }
    free.into_iter().fold(0.0, f64::max)
}

/// Per memory budget and thread count: median wall, check time and peak
/// memory, speedup and efficiency against one thread, and the bound: the
/// one-thread time outside the declarations plus the makespan of the
/// one-thread declaration times handed out in export order. A measured time
/// well above the bound is lost to running the threads together (memory,
/// allocator, nitrolean's memory budget), not to the schedule or the serial
/// part.
pub fn scaling(parallel: &Path, decl_times: Option<&Path>) -> Res<()> {
    let rows: Vec<_> = tsv(parallel)?
        .into_iter()
        .filter(|r| r["run"] != "0" && r["verdict"] == "accepted")
        .collect();
    let decl: Vec<f64> = match decl_times {
        Some(p) => read(p)?
            .lines()
            .filter_map(|l| l.split('\t').nth(1)?.parse().ok())
            .collect(),
        None => Vec::new(),
    };
    let mut keys: Vec<(String, usize)> = rows
        .iter()
        .map(|r| (r["mem_budget_mib"].clone(), num(r, "jobs") as usize))
        .collect();
    keys.sort();
    keys.dedup();
    let sel = |b: &str, n: usize, k: &str| -> Vec<f64> {
        rows.iter()
            .filter(|r| r["mem_budget_mib"] == b && num(r, "jobs") as usize == n)
            .map(|r| num(r, k))
            .collect()
    };
    let serial_of = |one_wall: f64| (one_wall - decl.iter().sum::<f64>()).max(0.0);
    println!(
        "| memory budget | jobs | wall s | check s | speedup | efficiency | bound s | bound speedup | peak MiB |"
    );
    println!("| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |");
    for (b, n) in keys {
        let one_wall = median(sel(&b, 1, "wall_s"));
        if one_wall.is_nan() {
            return err(format!("no accepted one-thread run with memory budget {b}"));
        }
        let w = median(sel(&b, n, "wall_s"));
        let c = median(sel(&b, n, "check_s"));
        let m = median(sel(&b, n, "peak_rss_mib"));
        let bound = if decl.is_empty() {
            f64::NAN
        } else {
            serial_of(one_wall) + makespan(&decl, n)
        };
        println!(
            "| {b} | {n} | {w:.1} | {c:.1} | {:.2} | {:.0}% | {bound:.1} | {:.2} | {m:.0} |",
            one_wall / w,
            100.0 * one_wall / w / n as f64,
            one_wall / bound
        );
    }
    if !decl.is_empty() {
        let mut d = decl.clone();
        d.sort_by(|a, b| b.total_cmp(a));
        println!(
            "\n{} declarations, {:.1} s in all; the largest {:.2} s, the 48 largest {:.1} s",
            d.len(),
            d.iter().sum::<f64>(),
            d[0],
            d.iter().take(48).sum::<f64>()
        );
    }
    Ok(())
}
