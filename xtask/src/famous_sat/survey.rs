//! `survey`: solve a sample of cubes and record the size of each trimmed,
//! core-restricted proof, to choose the cubes of `data/cubes.tsv` (fetch
//! does not run it). Rows: index, verdict, solve_s, core_clauses, lrat_bytes.

use std::path::Path;
use std::process::Command;
use std::time::{Duration, Instant};

use super::sat;
use super::util::{Res, err, mkdir, read, size, write};

/// `random:SEED:COUNT` (COUNT distinct indices from a splitmix64 stream
/// seeded with SEED) or a file with one cube index per line.
pub fn picks(spec: &str, cubes: &Path) -> Res<Vec<usize>> {
    if let Some(rest) = spec.strip_prefix("random:") {
        let (seed, count) = rest
            .split_once(':')
            .ok_or_else(|| anyhow::anyhow!("random:SEED:COUNT"))?;
        let mut s: u64 = seed.parse().map_err(|_| anyhow::anyhow!("bad seed"))?;
        let count: usize = count.parse().map_err(|_| anyhow::anyhow!("bad count"))?;
        let n = sat::count_cubes(cubes)?;
        if count > n {
            return err(format!("only {n} cubes"));
        }
        let mut set = std::collections::BTreeSet::new();
        while set.len() < count {
            s = s.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = s;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^= z >> 31;
            set.insert((z % n as u64) as usize + 1);
        }
        Ok(set.into_iter().collect())
    } else {
        read(Path::new(spec))?
            .split_whitespace()
            .map(|t| {
                t.parse()
                    .map_err(|_| anyhow::anyhow!("{spec}: bad index {t}"))
            })
            .collect()
    }
}

pub fn survey(
    cadical: &Path,
    formula: &Path,
    cubes: &Path,
    spec: &str,
    limit_s: u64,
    out: &Path,
    work: &Path,
) -> Res<()> {
    mkdir(work)?;
    let mut text = String::from("index\tverdict\tsolve_s\tcore_clauses\tlrat_bytes\n");
    let (cnf, lrat, trim, ccnf, clrat) = (
        work.join("c.cnf"),
        work.join("c.lrat"),
        work.join("c.trim.lrat"),
        work.join("c.core.cnf"),
        work.join("c.core.lrat"),
    );
    for i in picks(spec, cubes)? {
        sat::cube_cnf(formula, cubes, i, &cnf)?;
        let start = Instant::now();
        let mut child = Command::new(cadical)
            .args(["-q", "--lrat", "--no-binary", "-t"])
            .arg(limit_s.to_string())
            .arg(&cnf)
            .arg(&lrat)
            .stdout(std::process::Stdio::piped())
            .spawn()
            .map_err(|e| anyhow::anyhow!("cadical: {e}"))?;
        let deadline = Duration::from_secs(limit_s + 30);
        while child.try_wait()?.is_none() {
            if start.elapsed() > deadline {
                let _ = child.kill();
                break;
            }
            std::thread::sleep(Duration::from_millis(20));
        }
        let o = child.wait_with_output()?;
        let dt = start.elapsed().as_secs_f64();
        let status = String::from_utf8_lossy(&o.stdout);
        if !status.contains("s UNSATISFIABLE") {
            let v = if status.contains("s SATISFIABLE") {
                "sat"
            } else {
                "unknown"
            };
            text.push_str(&format!("{i}\t{v}\t{dt:.2}\t\t\n"));
            write(out, &text)?;
            continue;
        }
        sat::lrat_trim(&lrat, &trim)?;
        sat::lrat_core(&cnf, &trim, &ccnf, &clrat)?;
        let core = read(&ccnf)?
            .lines()
            .next()
            .and_then(|h| h.split_whitespace().nth(3).map(str::to_string))
            .unwrap_or_default();
        text.push_str(&format!("{i}\tunsat\t{dt:.2}\t{core}\t{}\n", size(&clrat)));
        write(out, &text)?;
    }
    Ok(())
}
