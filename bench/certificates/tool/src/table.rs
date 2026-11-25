//! `matcert table`: measure.sh's TSV as a Markdown table.

use std::collections::HashMap;
use std::fs;

const CHECKERS: [&str; 4] = ["nitrolean", "leanchecker", "gruszka", "nano-lean"];

fn tsv(path: &str) -> Result<Vec<HashMap<String, String>>, String> {
    let text = fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
    let mut lines = text.lines();
    let head: Vec<&str> = lines
        .next()
        .ok_or(format!("{path}: empty"))?
        .split('\t')
        .collect();
    Ok(lines
        .filter(|l| !l.is_empty())
        .map(|l| {
            head.iter()
                .map(|h| h.to_string())
                .zip(l.split('\t').map(str::to_string))
                .collect()
        })
        .collect())
}

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

/// A cell: `time, MiB` when the checker answered, else the verdict; a run with a longer
/// limit is added after the shortest one, as `timeout; 123 s, 456 at 600 s`.
fn cell(runs: &mut [&HashMap<String, String>]) -> String {
    runs.sort_by_key(|r| r["limit_s"].parse::<u64>().unwrap_or(0));
    let one = |r: &HashMap<String, String>| match r["verdict"].as_str() {
        "accepted" => format!("{}, {}", secs(&r["wall_s"]), grouped(&r["peak_rss_mib"])),
        v => v.to_string(),
    };
    let mut out = one(runs[0]);
    for r in &runs[1..] {
        out.push_str(&format!("; {} at {} s", one(r), r["limit_s"]));
    }
    out
}

pub fn table(args: &[String]) -> Result<(), String> {
    let [meas, manifest] = args else {
        return Err("usage: matcert table MEASUREMENTS.tsv MANIFEST.tsv".into());
    };
    let meas = tsv(meas)?;
    let manifest = tsv(manifest)?;
    println!(
        "| export | n | certificate bytes | {} |",
        CHECKERS.join(" | ")
    );
    println!("| --- | ---: | ---: |{}", " --- |".repeat(CHECKERS.len()));
    for m in &manifest {
        let label = &m["label"];
        let cells: Vec<String> = CHECKERS
            .iter()
            .map(|c| {
                let mut runs: Vec<_> = meas
                    .iter()
                    .filter(|r| &r["export"] == label && r["checker"] == *c)
                    .collect();
                if runs.is_empty() {
                    "-".into()
                } else {
                    cell(&mut runs)
                }
            })
            .collect();
        println!(
            "| {label} | {} | {} | {} |",
            m["n"],
            grouped(&m["cert_bytes"]),
            cells.join(" | ")
        );
    }
    Ok(())
}
