//! `cargo xtask ab-summary BUILD.json OUT.md OUT.json ROWS.tsv...`: the
//! summary of an A/B benchmark (.github/workflows/ab-bench.yml).
//!
//! The rows come from bench/ab/run.sh on many machines; BUILD.json
//! describes the two builds (refs, commits, flags, binaries). For every
//! slice, architecture and thread count, each machine (job) gives one paired
//! ratio per metric: B over A, where A and B are the sums of the two A runs
//! and the two B runs of an A/B/B/A quadruple (the geometric mean over the
//! machine's quadruples, if more than one). The summary gives the median of
//! these per-machine ratios with a 95% interval from the sign test (order
//! statistics of the ratios; distribution-free; needs 6 machines or more),
//! and checks them against the bar:
//!
//!   instructions:u  median change at most +0.1% (on each CPU model with counters)
//!   wall, CPU time  not worse: the interval does not lie wholly above 1
//!   peak RSS        not higher: the interval does not lie wholly above 1
//!   output          the same for A and B in every run
//!
//! With fewer than 6 machines there is no interval, and the verdict is
//! INCONCLUSIVE unless something fails.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::fs;
use std::path::PathBuf;

use anyhow::{Context, Result, bail};
use serde_json::{Value, json};

/// The instruction bar: +0.1%.
const INSTR_BAR: f64 = 0.001;

const METRICS: [(&str, &str); 5] = [
    ("instr_u", "instructions:u"),
    ("instr_all", "instructions (user+kernel)"),
    ("wall_s", "wall"),
    ("cpu_s", "CPU time"),
    ("rss_kib", "peak RSS"),
];

#[derive(clap::Args)]
pub struct Args {
    /// The builds' description (JSON).
    build: PathBuf,
    /// The summary (Markdown) goes here.
    out_md: PathBuf,
    /// The results (JSON) go here.
    out_json: PathBuf,
    /// Rows of bench/ab/run.sh.
    #[arg(required = true)]
    rows: Vec<PathBuf>,
}

type Row = BTreeMap<String, String>;

fn read_rows(paths: &[PathBuf]) -> Result<Vec<Row>> {
    let mut rows = Vec::new();
    for p in paths {
        let text = fs::read_to_string(p).with_context(|| format!("{}", p.display()))?;
        let mut header: Option<Vec<String>> = None;
        for line in text.lines() {
            let cells: Vec<String> = line.split('\t').map(str::to_string).collect();
            if header.is_none() || cells[0] == "job" {
                header = Some(cells);
                continue;
            }
            let h = header.as_ref().unwrap();
            rows.push(h.iter().cloned().zip(cells).collect());
        }
    }
    Ok(rows)
}

fn get<'a>(r: &'a Row, k: &str) -> &'a str {
    r.get(k).map_or("", String::as_str)
}

fn num(s: &str) -> Option<f64> {
    s.parse::<f64>().ok().filter(|x| x.is_finite())
}

fn median(xs: &[f64]) -> Option<f64> {
    let mut v = xs.to_vec();
    v.sort_by(f64::total_cmp);
    let n = v.len();
    match n {
        0 => None,
        _ if n % 2 == 1 => Some(v[n / 2]),
        _ => Some((v[n / 2 - 1] + v[n / 2]) / 2.0),
    }
}

/// Distribution-free 95% interval for the median: (x_(k), x_(n+1-k)) for
/// the largest k with P(Bin(n, 1/2) < k) <= 0.025.
fn sign_ci(sorted: &[f64]) -> Option<(f64, f64)> {
    let n = sorted.len();
    let mut pmf = 0.5f64.powi(n as i32);
    let (mut cdf, mut k) = (0.0, 0usize);
    for j in 0..=n {
        cdf += pmf;
        if cdf > 0.025 {
            break;
        }
        k = j + 1;
        pmf *= (n - j) as f64 / (j + 1) as f64;
    }
    (k >= 1).then(|| (sorted[k - 1], sorted[n - k]))
}

fn gmean(xs: &[f64]) -> f64 {
    (xs.iter().map(|x| x.ln()).sum::<f64>() / xs.len() as f64).exp()
}

#[derive(Clone)]
struct Stat {
    n: usize,
    median: f64,
    ci: Option<(f64, f64)>,
    min: f64,
    max: f64,
    lower: usize,
    higher: usize,
}

fn stat(xs: &[f64]) -> Option<Stat> {
    if xs.is_empty() {
        return None;
    }
    let mut v = xs.to_vec();
    v.sort_by(f64::total_cmp);
    Some(Stat {
        n: v.len(),
        median: median(&v)?,
        ci: sign_ci(&v),
        min: v[0],
        max: v[v.len() - 1],
        lower: v.iter().filter(|&&x| x < 1.0).count(),
        higher: v.iter().filter(|&&x| x > 1.0).count(),
    })
}

fn stat_json(s: &Stat) -> Value {
    json!({"n": s.n, "median": s.median, "ci": s.ci.map(|(a, b)| vec![a, b]),
           "min": s.min, "max": s.max, "b_lower": s.lower, "b_higher": s.higher})
}

fn pct(r: f64, digits: usize) -> String {
    format!("{:+.digits$}%", (r - 1.0) * 100.0)
}

fn fmt_stat(s: &Stat, digits: usize) -> (String, String) {
    let ci = match s.ci {
        Some((lo, hi)) => format!("[{}, {}]", pct(lo, digits), pct(hi, digits)),
        None => format!(
            "range [{}, {}] (n<6)",
            pct(s.min, digits),
            pct(s.max, digits)
        ),
    };
    (pct(s.median, digits), ci)
}

/// The 95% interval lies wholly above 1.
fn worse(s: &Stat) -> bool {
    s.ci.is_some_and(|(lo, _)| lo > 1.0)
}

#[derive(Default)]
struct Machine {
    cpu: String,
    ratios: BTreeMap<&'static str, Vec<f64>>,
    a: BTreeMap<&'static str, Vec<f64>>,
    shas: BTreeSet<String>,
    statuses: BTreeSet<String>,
    complete: bool,
}

impl Machine {
    fn ratio(&self, m: &str) -> Option<f64> {
        self.ratios
            .get(m)
            .filter(|v| !v.is_empty())
            .map(|v| gmean(v))
    }
}

/// (slice, arch, threads) -> job -> that machine's facts.
type Groups = BTreeMap<(String, String, u32), BTreeMap<u32, Machine>>;

fn per_job(rows: &[Row]) -> Groups {
    let mut quads: BTreeMap<(String, String, u32, u32, u32), Vec<&Row>> = BTreeMap::new();
    for r in rows {
        let t = get(r, "threads").parse().unwrap_or(0);
        let job = get(r, "job").parse().unwrap_or(0);
        let rep = get(r, "rep").parse().unwrap_or(0);
        quads
            .entry((get(r, "slice").into(), get(r, "arch").into(), t, job, rep))
            .or_default()
            .push(r);
    }
    let mut out = Groups::new();
    for ((sl, arch, t, job, _), q) in quads {
        let m = out
            .entry((sl, arch, t))
            .or_default()
            .entry(job)
            .or_insert_with(|| Machine {
                cpu: get(q[0], "cpu").into(),
                complete: true,
                ..Machine::default()
            });
        for r in &q {
            m.shas.insert(get(r, "out_sha").into());
            m.statuses.insert(get(r, "status").into());
        }
        let a: Vec<&&Row> = q.iter().filter(|r| get(r, "side") == "A").collect();
        let b: Vec<&&Row> = q.iter().filter(|r| get(r, "side") == "B").collect();
        if a.len() != 2 || b.len() != 2 {
            m.complete = false;
            continue;
        }
        for (key, _) in METRICS {
            let av: Option<Vec<f64>> = a.iter().map(|r| num(get(r, key))).collect();
            let bv: Option<Vec<f64>> = b.iter().map(|r| num(get(r, key))).collect();
            let (Some(av), Some(bv)) = (av, bv) else {
                continue;
            };
            let sa: f64 = av.iter().sum();
            if sa <= 0.0 {
                continue;
            }
            m.ratios
                .entry(key)
                .or_default()
                .push(bv.iter().sum::<f64>() / sa);
            m.a.entry(key).or_default().extend(av);
        }
    }
    out
}

fn s(v: &Value, k: &str) -> String {
    match v.get(k) {
        Some(Value::String(x)) => x.clone(),
        Some(Value::Null) | None => String::new(),
        Some(x) => x.to_string(),
    }
}

pub fn summary(a: Args) -> Result<()> {
    let build: Value = serde_json::from_str(
        &fs::read_to_string(&a.build).with_context(|| format!("{}", a.build.display()))?,
    )
    .with_context(|| format!("{}: not JSON", a.build.display()))?;
    let rows = read_rows(&a.rows)?;
    if rows.is_empty() {
        bail!("ab-summary: no rows");
    }
    let groups = per_job(&rows);
    let mut md = String::new();
    macro_rules! w { ($($t:tt)*) => { let _ = writeln!(md, $($t)*); } }
    let short = |x: String| x.chars().take(12).collect::<String>();
    w!("## A/B benchmark\n");
    w!(
        "- A (base): `{}` = `{}`",
        s(&build, "base_ref"),
        short(s(&build, "base_sha"))
    );
    let flags = s(&build, "candidate_flags");
    w!(
        "- B (candidate): `{}` = `{}`{}",
        s(&build, "candidate_ref"),
        short(s(&build, "candidate_sha")),
        if flags.is_empty() {
            String::new()
        } else {
            format!(", flags `{flags}`")
        }
    );
    if let Some(Value::Object(bins)) = build.get("binaries") {
        for (k, v) in bins {
            w!("- binary {k}: SHA-256 `{}`", v.as_str().unwrap_or(""));
        }
    }
    w!("- builds: {}", s(&build, "build_note"));
    w!(
        "- slices: {}; threads: {}; A/B/B/A quadruples per machine and thread count: {}",
        s(&build, "slices"),
        s(&build, "threads"),
        s(&build, "reps")
    );
    let ttr = s(&build, "time_to_result");
    if !ttr.is_empty() {
        w!("- time to result: {ttr} (dispatch to this summary)");
    }
    let seen: BTreeSet<(&str, &str)> = rows
        .iter()
        .map(|r| (get(r, "arch"), get(r, "job")))
        .collect();
    w!(
        "- machines that reported rows: {} of {}\n",
        seen.len(),
        s(&build, "jobs_requested")
    );
    w!(
        "Each machine gives one paired ratio B/A per metric (sum of its two B runs over its two A runs). \
         Shown: the median change over machines, and a 95% interval for it from the sign test. \
         Bar: instructions:u at most +0.1%; wall, CPU time and peak RSS not worse \
         (the interval not wholly above 0); output identical. With fewer than 6 machines there is \
         no interval, and the verdict is INCONCLUSIVE unless something fails.\n"
    );

    // Machines by CPU model, per architecture.
    let mut cpus: BTreeMap<(&str, &str, &str), BTreeSet<&str>> = BTreeMap::new();
    for r in &rows {
        cpus.entry((get(r, "arch"), get(r, "cpu"), get(r, "counters")))
            .or_default()
            .insert(get(r, "job"));
    }
    w!("### Machines\n");
    w!("| arch | CPU | counters | jobs |");
    w!("|---|---|---|--:|");
    let mut cl: Vec<_> = cpus.iter().collect();
    cl.sort_by_key(|((arch, _, _), js)| (*arch, std::cmp::Reverse(js.len())));
    for ((arch, cpu, ctr), js) in cl {
        w!("| {arch} | {cpu} | {ctr} | {} |", js.len());
    }
    w!("");

    let mut keys: Vec<_> = groups.keys().cloned().collect();
    keys.sort_by_key(|k| (k.0 != "full", k.clone()));
    let mut results = serde_json::Map::new();
    // (slice, verdict, line)
    let mut verdicts: Vec<(String, String, String)> = Vec::new();
    // key -> (metric[@cpu] -> stat)
    let mut all_stats: BTreeMap<String, BTreeMap<String, Stat>> = BTreeMap::new();
    for k in &keys {
        let (sl, arch, t) = k;
        let jobs = &groups[k];
        let key = format!("{sl}/{arch}/j{t}");
        w!("### {sl}, {arch}, -j{t} ({} machines)\n", jobs.len());
        w!(
            "| metric | machines | median A | median change B/A | 95% interval | B lower / higher |"
        );
        w!("|---|--:|--:|--:|---|---|");
        let mut stats: BTreeMap<String, Stat> = BTreeMap::new();
        for (m, label) in METRICS {
            let mut by_cpu: BTreeMap<&str, Vec<&Machine>> = BTreeMap::new();
            for j in jobs.values() {
                if j.ratio(m).is_some() {
                    by_cpu.entry(j.cpu.as_str()).or_default().push(j);
                }
            }
            let mut models: Vec<_> = by_cpu.into_iter().collect();
            models.sort_by_key(|(_, js)| std::cmp::Reverse(js.len()));
            let a_med = |js: &[&Machine]| {
                median(
                    &js.iter()
                        .flat_map(|j| j.a[m].iter().copied())
                        .collect::<Vec<_>>(),
                )
                .unwrap_or(0.0)
            };
            if m.starts_with("instr") {
                // Per CPU model: counts are only comparable within one.
                for (cpu, js) in &models {
                    let st =
                        stat(&js.iter().filter_map(|j| j.ratio(m)).collect::<Vec<_>>()).unwrap();
                    let (med, ci) = fmt_stat(&st, 3);
                    w!(
                        "| {label} ({cpu}) | {} | {:.2} G | {med} | {ci} | {} / {} |",
                        st.n,
                        a_med(js) / 1e9,
                        st.lower,
                        st.higher
                    );
                    stats.insert(format!("{m}@{cpu}"), st);
                }
                continue;
            }
            let js: Vec<&Machine> = jobs.values().filter(|j| j.ratio(m).is_some()).collect();
            let Some(st) = stat(&js.iter().filter_map(|j| j.ratio(m)).collect::<Vec<_>>()) else {
                continue;
            };
            let am = a_med(&js);
            let a_txt = if m == "rss_kib" {
                format!("{:.0} MiB", am / 1024.0)
            } else {
                format!("{am:.2} s")
            };
            let (med, ci) = fmt_stat(&st, 2);
            w!(
                "| {label} | {} | {a_txt} | {med} | {ci} | {} / {} |",
                st.n,
                st.lower,
                st.higher
            );
            // Wall and CPU time by CPU model too, when there is more than one.
            if (m == "wall_s" || m == "cpu_s") && models.len() > 1 {
                for (cpu, js) in &models {
                    let s2 =
                        stat(&js.iter().filter_map(|j| j.ratio(m)).collect::<Vec<_>>()).unwrap();
                    let (med2, ci2) = fmt_stat(&s2, 2);
                    w!(
                        "| &nbsp;&nbsp;{label}, {cpu} | {} | | {med2} | {ci2} | {} / {} |",
                        s2.n,
                        s2.lower,
                        s2.higher
                    );
                }
            }
            stats.insert(m.to_string(), st);
        }
        w!("");
        // The bar.
        let mut problems: Vec<String> = Vec::new();
        let mut notes: Vec<String> = Vec::new();
        let mut few = false;
        let instr: Vec<(&str, &Stat)> = stats
            .iter()
            .filter_map(|(k, v)| k.strip_prefix("instr_u@").map(|c| (c, v)))
            .collect();
        if instr.is_empty() {
            notes.push("no instruction counts on this architecture".into());
        }
        for (cpu, st) in &instr {
            if st.median - 1.0 > INSTR_BAR {
                problems.push(format!(
                    "instructions:u {} on {cpu} (bar +0.100%)",
                    pct(st.median, 3)
                ));
            }
        }
        for (m, label) in [
            ("wall_s", "wall"),
            ("cpu_s", "CPU time"),
            ("rss_kib", "peak RSS"),
        ] {
            match stats.get(m) {
                None => problems.push(format!("no {label} pairs")),
                Some(st) if worse(st) => {
                    let (med, ci) = fmt_stat(st, 2);
                    problems.push(format!("{label} worse: {med} {ci}"));
                }
                Some(st) if st.ci.is_none() => few = true,
                Some(_) => {}
            }
        }
        let mism: Vec<String> = jobs
            .iter()
            .filter(|(_, j)| j.shas.len() != 1)
            .map(|(jb, _)| jb.to_string())
            .collect();
        let bad_status: BTreeSet<&str> = jobs
            .values()
            .flat_map(|j| j.statuses.iter().map(String::as_str))
            .filter(|s| *s != "0")
            .collect();
        if !mism.is_empty() {
            problems.push(format!(
                "output differs on {} machines (jobs {})",
                mism.len(),
                mism.iter().take(10).cloned().collect::<Vec<_>>().join(", ")
            ));
        }
        if !bad_status.is_empty() {
            problems.push(format!(
                "exit status {} seen",
                bad_status.iter().copied().collect::<Vec<_>>().join(", ")
            ));
        }
        let incomplete = jobs.values().filter(|j| !j.complete).count();
        if incomplete > 0 {
            notes.push(format!(
                "{incomplete} machines with an incomplete quadruple"
            ));
        }
        if few {
            notes.push("fewer than 6 machines: no interval for wall, CPU time or RSS".into());
        }
        let verdict = if !problems.is_empty() {
            "FAIL"
        } else if few {
            "INCONCLUSIVE"
        } else if !instr.is_empty() {
            "PASS"
        } else {
            "PASS (no instruction counts)"
        };
        let mut line = format!("**{verdict}** {key}");
        if !problems.is_empty() {
            line += &format!(": {}", problems.join("; "));
        }
        if !notes.is_empty() {
            line += &format!(" ({})", notes.join("; "));
        }
        w!("{line}\n");
        verdicts.push((sl.clone(), verdict.to_string(), line));
        results.insert(
            key.clone(),
            json!({
                "slice": sl, "arch": arch, "threads": t, "machines": jobs.len(),
                "verdict": verdict, "problems": problems, "notes": notes,
                "output_identical": mism.is_empty() && bad_status.is_empty(),
                "stats": stats.iter().map(|(k, v)| (k.clone(), stat_json(v))).collect::<serde_json::Map<_, _>>(),
            }),
        );
        all_stats.insert(key, stats);
    }

    // How well each smaller slice predicted all of Mathlib.
    let slices: BTreeSet<&str> = groups.keys().map(|k| k.0.as_str()).collect();
    if slices.contains("full") && slices.len() > 1 {
        w!("### Slices against all of Mathlib (screening)\n");
        w!("A slice is for screening only: all of Mathlib decides. \
             Here each slice's median change is set beside the full export's, from the same machines.\n");
        w!(
            "| slice | arch | threads | instructions:u slice / full | wall slice / full | CPU slice / full |"
        );
        w!("|---|---|--:|---|---|---|");
        for sl in slices.iter().filter(|s| **s != "full") {
            for (s2, arch, t) in groups.keys() {
                if s2 != sl {
                    continue;
                }
                let (Some(a), Some(f)) = (
                    all_stats.get(&format!("{sl}/{arch}/j{t}")),
                    all_stats.get(&format!("full/{arch}/j{t}")),
                ) else {
                    continue;
                };
                let mut ik: Vec<&String> = a
                    .keys()
                    .filter(|k| k.starts_with("instr_u@") && f.contains_key(*k))
                    .collect();
                ik.sort_by_key(|k| std::cmp::Reverse(a[*k].n));
                let ic = ik.first().map_or("–".to_string(), |k| {
                    format!("{} / {}", pct(a[*k].median, 3), pct(f[*k].median, 3))
                });
                let c = |m: &str| match (a.get(m), f.get(m)) {
                    (Some(x), Some(y)) => format!("{} / {}", pct(x.median, 2), pct(y.median, 2)),
                    _ => "–".into(),
                };
                w!(
                    "| {sl} | {arch} | {t} | {ic} | {} | {} |",
                    c("wall_s"),
                    c("cpu_s")
                );
            }
        }
        w!("");
    }

    w!("### Verdict\n");
    let has_full = verdicts.iter().any(|v| v.0 == "full");
    let decisive: Vec<_> = verdicts
        .iter()
        .filter(|v| !has_full || v.0 == "full")
        .collect();
    for v in &decisive {
        w!("- {}", v.2);
    }
    if !has_full {
        w!("- (a slice only: screening, not a decision; all of Mathlib decides)");
    }
    let overall = if !decisive.is_empty() && decisive.iter().all(|v| v.1.starts_with("PASS")) {
        "PASS"
    } else if decisive.iter().any(|v| v.1 == "FAIL") {
        "FAIL"
    } else {
        "INCONCLUSIVE"
    };
    w!(
        "\n**Overall: {overall}**{}",
        if has_full { "" } else { " (screening only)" }
    );
    fs::write(&a.out_md, &md)?;
    let out = json!({"build": build, "overall": overall, "results": results});
    fs::write(&a.out_json, serde_json::to_string_pretty(&out)? + "\n")?;
    print!("{md}");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sign_interval() {
        let xs: Vec<f64> = (1..=20).map(f64::from).collect();
        // n = 20: the interval is (x_6, x_15).
        assert_eq!(sign_ci(&xs), Some((6.0, 15.0)));
        let xs: Vec<f64> = (1..=6).map(f64::from).collect();
        assert_eq!(sign_ci(&xs), Some((1.0, 6.0)));
        assert_eq!(sign_ci(&[1.0, 2.0, 3.0, 4.0, 5.0]), None);
    }
}
