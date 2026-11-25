//! The conversions between DIMACS formulas, cube files and text LRAT proofs
//! that the exports are made with. Each writes exactly what the published
//! pins in `data/cubes.tsv` were made from.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::path::Path;

use super::util::{Res, err, read, write};

fn int(t: &str) -> Res<i64> {
    t.parse()
        .map_err(|_| anyhow::anyhow!("not a number: {t:?}"))
}

/// The literals of cube `index` (from 1) of a cube file: its `a lit ... 0`
/// lines; other lines are ignored, and so is a last line cut off before its
/// `0`.
pub fn cube(path: &Path, index: usize) -> Res<Vec<i64>> {
    let text = read(path)?;
    let mut n = 0;
    for raw in text.split_inclusive('\n') {
        if !raw.starts_with("a ") {
            continue;
        }
        let tok: Vec<&str> = raw.split_ascii_whitespace().collect();
        if tok.last() != Some(&"0") || !raw.ends_with('\n') {
            break;
        }
        n += 1;
        if n == index {
            return tok[1..tok.len() - 1].iter().map(|t| int(t)).collect();
        }
    }
    err(format!(
        "{} has {n} complete cubes, no cube {index}",
        path.display()
    ))
}

/// The number of complete cubes of a cube file.
pub fn count_cubes(path: &Path) -> Res<usize> {
    let text = read(path)?;
    Ok(text
        .split_inclusive('\n')
        .filter(|l| l.starts_with("a ") && l.ends_with(" 0\n"))
        .count())
}

/// The formula with the literals of cube `index` added as unit clauses.
pub fn cube_cnf(formula: &Path, cubes: &Path, index: usize, out: &Path) -> Res<()> {
    let lits = cube(cubes, index)?;
    let text = read(formula)?;
    let mut head: Option<Vec<&str>> = None;
    let mut body: Vec<String> = Vec::new();
    for raw in text.split_inclusive('\n') {
        if raw.starts_with('c') || raw.trim().is_empty() {
            continue;
        }
        if raw.starts_with("p ") {
            head = Some(raw.split_ascii_whitespace().collect());
            continue;
        }
        body.push(if raw.ends_with('\n') {
            raw.to_string()
        } else {
            format!("{raw}\n")
        });
    }
    let Some(head) = head else {
        return err(format!("{}: no header", formula.display()));
    };
    let declared = head.get(2).map_or(Ok(0), |t| int(t))?;
    let nvars = declared.max(lits.iter().map(|x| x.abs()).max().unwrap_or(0));
    let mut s = format!("p cnf {nvars} {}\n", body.len() + lits.len());
    for b in &body {
        s.push_str(b);
    }
    for x in &lits {
        let _ = writeln!(s, "{x} 0");
    }
    write(out, s)
}

/// Keep only the lemmas the final empty clause depends on and number them
/// consecutively after the formula's clauses: `cargo xtask kc lrat-trim`.
pub fn lrat_trim(input: &Path, out: &Path) -> Res<()> {
    crate::kc::lrat_trim(input, out)
}

fn zero(tok: &[&str]) -> Res<usize> {
    tok.iter()
        .position(|t| *t == "0")
        .ok_or_else(|| anyhow::anyhow!("LRAT line without 0: {}", tok.join(" ")))
}

fn clauses(text: &str) -> Vec<String> {
    text.split_inclusive('\n')
        .filter(|l| !(l.starts_with('c') || l.starts_with('p') || l.trim().is_empty()))
        .map(|l| {
            if l.ends_with('\n') {
                l.to_string()
            } else {
                format!("{l}\n")
            }
        })
        .collect()
}

/// Restrict a formula and its trimmed proof (`lrat_trim`'s output) to the
/// formula clauses the proof names: they keep their order and get ids 1, 2,
/// ...; the lemmas follow. A refutation of this core refutes the formula,
/// since the core is a subset of its clauses.
pub fn lrat_core(cnf_in: &Path, lrat_in: &Path, cnf_out: &Path, lrat_out: &Path) -> Res<()> {
    let cls = clauses(&read(cnf_in)?);
    let m = cls.len() as i64;
    let text = read(lrat_in)?;
    let lines: Vec<Vec<&str>> = text
        .lines()
        .map(|l| l.split_ascii_whitespace().collect::<Vec<_>>())
        .filter(|t| !t.is_empty())
        .collect();
    if let Some(t) = lines.first()
        && int(t[0])? != m + 1
    {
        return err(format!(
            "lrat_core: the first lemma is {}, expected {}",
            t[0],
            m + 1
        ));
    }
    let mut used = std::collections::BTreeSet::new();
    for tok in &lines {
        let z = zero(tok)?;
        for h in &tok[z + 1..tok.len() - 1] {
            let v = int(h)?.abs();
            if v <= m {
                used.insert(v);
            }
        }
    }
    let core: Vec<i64> = used.into_iter().collect();
    let new: HashMap<i64, i64> = core
        .iter()
        .enumerate()
        .map(|(i, c)| (*c, i as i64 + 1))
        .collect();
    let mut nvars = 0i64;
    let mut s = String::new();
    let body: Vec<&String> = core.iter().map(|c| &cls[*c as usize - 1]).collect();
    for cl in &body {
        let toks: Vec<&str> = cl.split_ascii_whitespace().collect();
        for t in &toks[..toks.len().saturating_sub(1)] {
            nvars = nvars.max(int(t)?.abs());
        }
    }
    let _ = writeln!(s, "p cnf {nvars} {}", body.len());
    for cl in body {
        s.push_str(cl);
    }
    write(cnf_out, s)?;
    let shift = m - core.len() as i64;
    let mut s = String::new();
    for tok in &lines {
        let z = zero(tok)?;
        let mut parts = vec![(int(tok[0])? - shift).to_string()];
        parts.extend(tok[1..=z].iter().map(|t| t.to_string()));
        for h in &tok[z + 1..tok.len() - 1] {
            let h = int(h)?;
            let v = h.abs();
            let v = if v <= m { new[&v] } else { v - shift };
            parts.push((if h > 0 { v } else { -v }).to_string());
        }
        parts.push("0".into());
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    write(lrat_out, s)
}

/// Rename the variables of a formula and its proof to 1, 2, ... in order of
/// first use (the formula first). The result is the same formula up to the
/// names of its variables, so a different theorem; it shows what the
/// variable numbering costs.
pub fn renumber(cnf_in: &Path, lrat_in: &Path, cnf_out: &Path, lrat_out: &Path) -> Res<()> {
    let mut new: HashMap<i64, i64> = HashMap::new();
    let mut ren = |t: &str| -> Res<String> {
        let v = int(t)?;
        if v == 0 {
            return Ok("0".into());
        }
        let n = new.len() as i64 + 1;
        let a = *new.entry(v.abs()).or_insert(n);
        Ok((if v > 0 { a } else { -a }).to_string())
    };
    let text = read(cnf_in)?;
    let mut cls = Vec::new();
    for raw in text.split_inclusive('\n') {
        if raw.trim().is_empty() || raw.starts_with('c') || raw.starts_with('p') {
            continue;
        }
        let r: Vec<String> = raw
            .split_ascii_whitespace()
            .map(&mut ren)
            .collect::<Res<_>>()?;
        cls.push(r.join(" "));
    }
    let text = read(lrat_in)?;
    let mut s = String::new();
    for raw in text.lines() {
        let tok: Vec<&str> = raw.split_ascii_whitespace().collect();
        if tok.is_empty() {
            continue;
        }
        let z = zero(&tok)?;
        let mut parts = vec![tok[0].to_string()];
        for t in &tok[1..=z] {
            parts.push(ren(t)?);
        }
        parts.extend(tok[z + 1..].iter().map(|t| t.to_string()));
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    write(lrat_out, s)?;
    let mut c = format!("p cnf {} {}\n", new.len(), cls.len());
    for cl in cls {
        c.push_str(&cl);
        c.push('\n');
    }
    write(cnf_out, c)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tmp(name: &str, s: &str) -> std::path::PathBuf {
        let p = std::env::temp_dir().join(format!("famous-sat-{}-{name}", std::process::id()));
        std::fs::write(&p, s).unwrap();
        p
    }

    /// Clauses `1`, `-1 2` and an unused `3`, and the cube `-2`: refuted by RUP.
    #[test]
    fn cube_trim_core_renumber() {
        let f = tmp("f.cnf", "c comment\np cnf 3 3\n1 0\n-1 2 0\n3 0\n");
        let c = tmp("c.icnf", "a -2 0\na 2 0\na 1");
        let out = tmp("s.cnf", "");
        cube_cnf(&f, &c, 1, &out).unwrap();
        assert_eq!(read(&out).unwrap(), "p cnf 3 4\n1 0\n-1 2 0\n3 0\n-2 0\n");
        assert!(cube(&c, 3).is_err(), "a cut-off last cube does not count");
        // A proof with a useless lemma 5 and a deletion; 6 is the empty clause.
        let l = tmp("p.lrat", "5 3 0 3 0\n5 d 3 0\n6 0 1 2 4 0\n");
        let t = tmp("t.lrat", "");
        lrat_trim(&l, &t).unwrap();
        assert_eq!(read(&t).unwrap(), "5 0 1 2 4 0\n");
        let (cc, cl) = (tmp("cc.cnf", ""), tmp("cc.lrat", ""));
        lrat_core(&out, &t, &cc, &cl).unwrap();
        assert_eq!(read(&cc).unwrap(), "p cnf 2 3\n1 0\n-1 2 0\n-2 0\n");
        assert_eq!(read(&cl).unwrap(), "4 0 1 2 3 0\n");
        let (rc, rl) = (tmp("r.cnf", ""), tmp("r.lrat", ""));
        renumber(&cc, &cl, &rc, &rl).unwrap();
        assert_eq!(read(&rc).unwrap(), "p cnf 2 3\n1 0\n-1 2 0\n-2 0\n");
        assert_eq!(read(&rl).unwrap(), "4 0 1 2 3 0\n");
    }
}
