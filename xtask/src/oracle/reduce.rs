//! `cargo xtask oracle reduce`: shrinks a declaration on which Lean's checker
//! and nitrolean disagree to a small export.

use std::collections::HashSet;
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};

use anyhow::Result;
use regex::Regex;

use super::export::{Graph, norm_name};
use super::limited::run_limited;
use super::{Parsed, kind_of, parse_lean, parse_nitrolean, read_log, toolchain_bin};
use crate::util::{absolute, exit_with, root};

/// Reduce a declaration on which Lean's checker and nitrolean disagree to a
/// small export.
///
/// Starts from the closure of DECLARATION in EXPORT (the declaration and every
/// declaration it uses, transitively), checks that the two checkers still
/// disagree on it, then shrinks it: it turns the definitions and theorems of
/// the closure into axioms of the same type, as many as it can while the
/// disagreement stays (a delta-debugging search: all at once, then halves,
/// quarters, ... down to one at a time), and drops what the remaining values
/// no longer use.
///
/// "Disagree" means the same as for `oracle run`: one checker accepts
/// DECLARATION and the other rejects it, or both reject it with different
/// error kinds; a run that rejects another declaration of the reduced export
/// first does not count. The result is written to --out (default
/// reduced/<declaration>.ndjson) with a line for tests/kernel/cases.tsv on
/// stdout: id, rule, expected (Lean's verdict), lean, why.
#[derive(clap::Args)]
#[command(verbatim_doc_comment)]
pub struct Args {
    export: PathBuf,
    decl: String,
    #[arg(long)]
    out: Option<PathBuf>,
    #[arg(long)]
    leanchecker: Option<PathBuf>,
    #[arg(long, default_value = "leanprover/lean4:v4.36.0")]
    toolchain: String,
    /// default target/release/nitrolean
    #[arg(long)]
    nitrolean: Option<PathBuf>,
    #[arg(long, default_value_t = 600.0)]
    timeout: f64,
    #[arg(long, default_value_t = 300)]
    max_tests: usize,
}

/// 'accept', 'reject:<kind>', or None (another declaration rejected, or no verdict).
fn verdict(
    cmd: &[OsString],
    parse: fn(&str) -> Parsed,
    path: &Path,
    target: &str,
    timeout: f64,
) -> Result<Option<String>> {
    let log = crate::corpus::temp_path("reduce-", ".log");
    let mut argv = cmd.to_vec();
    argv.push(path.into());
    let st = run_limited(&argv, &log, timeout, 64 * 1024, None);
    let text = read_log(&log);
    let _ = fs::remove_file(&log);
    let st = st?;
    if st.status != "exited" {
        return Ok(None);
    }
    let (ok, decl, msg) = parse(&text);
    if ok && st.exit == "0" {
        return Ok(Some("accept".into()));
    }
    if let Some(d) = decl
        && norm_name(&d) == target
    {
        return Ok(Some(format!("reject:{}", kind_of(&msg))));
    }
    Ok(None)
}

fn show(v: &Option<String>) -> &str {
    v.as_deref().unwrap_or("None")
}

pub fn main(a: Args) -> Result<()> {
    let lc = match &a.leanchecker {
        Some(l) => l.clone(),
        None => toolchain_bin(&a.toolchain)?.join("leanchecker"),
    };
    let nitro = a
        .nitrolean
        .clone()
        .unwrap_or_else(|| root().join("target/release/nitrolean"));
    let target = norm_name(&a.decl);
    let out = a.out.clone().unwrap_or_else(|| {
        let safe = Regex::new(r"[^\w.-]").unwrap().replace_all(&target, "_");
        PathBuf::from("reduced").join(format!("{safe}.ndjson"))
    });
    if let Some(d) = absolute(&out).parent() {
        fs::create_dir_all(d)?;
    }

    eprintln!("reading {}", a.export.display());
    let g = Graph::new(&a.export)?;
    let Some(nid) = g.name_id(&target) else {
        return Err(exit_with(
            1,
            format!(
                "reduce: {} is not declared in {}",
                a.decl,
                a.export.display()
            ),
        ));
    };
    let start = g.decl_of[&nid];
    let mut tests = 0usize;
    let tmp = PathBuf::from(format!("{}.try.ndjson", out.display()));
    let lean_cmd = [lc.into_os_string(), "--from-export".into()];
    let nitro_cmd = [nitro.into_os_string(), "check".into()];

    let both = |vf: &HashSet<usize>,
                tests: &mut usize|
     -> Result<(Option<String>, Option<String>, usize)> {
        *tests += 1;
        let lines = g.closure(&[start], vf)?;
        g.write(&tmp, &lines, vf)?;
        let lv = verdict(&lean_cmd, parse_lean, &tmp, &target, a.timeout)?;
        let nv = verdict(&nitro_cmd, parse_nitrolean, &tmp, &target, a.timeout)?;
        Ok((lv, nv, lines.len()))
    };

    let (lv0, nv0, n0) = both(&HashSet::new(), &mut tests)?;
    eprintln!(
        "closure: {n0} records; Lean {}, nitrolean {}",
        show(&lv0),
        show(&nv0)
    );
    if lv0.is_none() || nv0.is_none() || lv0 == nv0 {
        let _ = fs::remove_file(&tmp);
        return Err(exit_with(
            1,
            format!(
                "reduce: the closure does not show the disagreement (Lean {}, nitrolean {}); the mismatch needs more than the closure",
                show(&lv0),
                show(&nv0)
            ),
        ));
    }

    let interesting = |vf: &HashSet<usize>, tests: &mut usize| -> Result<bool> {
        if *tests >= a.max_tests {
            return Ok(false);
        }
        let (lv, nv, _) = both(vf, tests)?;
        Ok(lv == lv0 && nv == nv0)
    };

    // Delta debugging over the records whose value can be dropped.
    let mut cands: Vec<usize> = g
        .closure(&[start], &HashSet::new())?
        .into_iter()
        .filter(|&no| no != start && matches!(g.decl_roots[&no].0, "def" | "thm" | "opaque"))
        .collect();
    cands.sort();
    let mut fixed: HashSet<usize> = HashSet::new();
    if !cands.is_empty() && interesting(&cands.iter().copied().collect(), &mut tests)? {
        fixed = cands.iter().copied().collect();
        cands.clear();
    }
    let mut chunk = (cands.len() / 2).max(1);
    while !cands.is_empty() && tests < a.max_tests {
        let mut kept = Vec::new();
        for part in cands.chunks(chunk) {
            let try_set: HashSet<usize> = fixed.iter().chain(part).copied().collect();
            if interesting(&try_set, &mut tests)? {
                fixed = try_set;
            } else {
                let mut p = part.to_vec();
                p.sort();
                kept.extend(p);
            }
        }
        let live = g.closure(&[start], &fixed)?;
        cands = kept.into_iter().filter(|c| live.contains(c)).collect();
        if chunk == 1 {
            break;
        }
        chunk = (chunk / 2).max(1);
    }
    let lines = g.closure(&[start], &fixed)?;
    g.write(&out, &lines, &fixed)?;
    let _ = fs::remove_file(&tmp);
    let (lv, nv) = (lv0.unwrap(), nv0.unwrap()); // every kept step reproduced these
    eprintln!(
        "reduced: {} records ({} made axioms), {tests} test runs; Lean {lv}, nitrolean {nv}; wrote {}",
        lines.len(),
        fixed.len(),
        out.display()
    );
    let expected = lv.split(':').next().unwrap_or("");
    let cid = format!(
        "oracle-{}",
        Regex::new(r"[^\w-]")
            .unwrap()
            .replace_all(&target, "-")
            .to_lowercase()
    );
    println!(
        "{cid}\toracle\t{expected}\t{expected}\tcorpus oracle: {target}: Lean {lv}, nitrolean {nv}"
    );
    Ok(())
}
