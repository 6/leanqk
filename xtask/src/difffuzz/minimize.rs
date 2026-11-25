//! Shrink an export while the two checkers keep giving the same pair of verdicts.
//!
//! 1. the shortest prefix of declarations (binary search);
//! 2. only the declarations the last one depends on;
//! 3. chunks and then single declarations dropped, definitions and theorems
//!    turned into axioms (an axiom needs no value), repeated to a fixpoint;
//! 4. unreferenced name, level and expression records dropped, ids renumbered.

use std::collections::{HashMap, HashSet};

use serde_json::{Map, Value, json};

use super::export::{deps, dumps, infos, kind_of, u};

pub fn is_decl(line: &str) -> bool {
    ["axiom", "def", "thm", "opaque", "quot", "inductive"]
        .iter()
        .any(|k| line.starts_with(&format!("{{\"{k}\":")))
}

fn parse(line: &str) -> Map<String, Value> {
    serde_json::from_str::<Value>(line)
        .ok()
        .and_then(|v| v.as_object().cloned())
        .unwrap_or_default()
}

/// Keep the declarations the last one depends on through constants (the
/// quotient declarations as a block).
pub fn closure_prune(lines: &[String]) -> Vec<String> {
    let recs: Vec<Map<String, Value>> = lines.iter().map(|l| parse(l)).collect();
    let mut exprs: HashMap<u64, &Map<String, Value>> = HashMap::new();
    let mut defines: HashMap<u64, usize> = HashMap::new();
    let mut decls = Vec::new();
    for (i, r) in recs.iter().enumerate().skip(1) {
        if let Some(e) = r.get("ie") {
            exprs.insert(u(e), r);
        } else if is_decl(&lines[i]) {
            let k = kind_of(r);
            for x in infos(&k, &r[&k]) {
                defines.insert(u(&x["name"]), i);
            }
            decls.push(i);
        }
    }
    let Some(&root) = decls.last() else {
        return lines.to_vec();
    };
    let quot: Vec<usize> = decls
        .iter()
        .copied()
        .filter(|&i| recs[i].contains_key("quot"))
        .collect();
    let uses = |i: usize| -> HashSet<u64> {
        let r = &recs[i];
        let mut out = HashSet::new();
        let k = kind_of(r);
        if k == "inductive" {
            for x in infos(&k, &r[&k]) {
                out.insert(u(&x["name"]));
            }
        }
        let mut stack: Vec<u64> = deps(r)
            .into_iter()
            .filter(|d| d.0 == "ie")
            .map(|d| d.1)
            .collect();
        let mut seen = HashSet::new();
        while let Some(e) = stack.pop() {
            if !seen.insert(e) {
                continue;
            }
            let Some(x) = exprs.get(&e) else { continue };
            if let Some(c) = x.get("const") {
                out.insert(u(&c["name"]));
            }
            stack.extend(deps(x).into_iter().filter(|d| d.0 == "ie").map(|d| d.1));
        }
        out
    };
    let mut keep = HashSet::new();
    let mut todo = vec![root];
    while let Some(i) = todo.pop() {
        if !keep.insert(i) {
            continue;
        }
        if quot.contains(&i) {
            todo.extend(quot.iter().copied());
        }
        for n in uses(i) {
            if let Some(&j) = defines.get(&n)
                && !keep.contains(&j)
            {
                todo.push(j);
            }
        }
    }
    lines
        .iter()
        .enumerate()
        .filter(|(i, l)| *i == 0 || !is_decl(l) || keep.contains(i))
        .map(|(_, l)| l.clone())
        .collect()
}

/// Drop unreferenced primitive records and renumber ids densely, in order.
pub fn gc(lines: &[String]) -> Vec<String> {
    let recs: Vec<Map<String, Value>> = lines[1..].iter().map(|l| parse(l)).collect();
    let id_of = |r: &Map<String, Value>| -> Option<(&'static str, u64)> {
        ["in", "il", "ie"]
            .iter()
            .find_map(|sp| r.get(*sp).map(|v| (*sp, u(v))))
    };
    let mut by: HashMap<(&str, u64), &Map<String, Value>> = HashMap::new();
    for r in &recs {
        if let Some(k) = id_of(r) {
            by.insert(k, r);
        }
    }
    let mut live = HashSet::new();
    let mut stack: Vec<(&str, u64)> = recs
        .iter()
        .filter(|r| id_of(r).is_none())
        .flat_map(|r| deps(r))
        .collect();
    while let Some(d) = stack.pop() {
        if !by.contains_key(&d) || !live.insert(d) {
            continue;
        }
        stack.extend(deps(by[&d]));
    }
    let keep: Vec<&Map<String, Value>> = recs
        .iter()
        .filter(|r| id_of(r).is_none_or(|k| live.contains(&k)))
        .collect();
    let mut new: HashMap<(&str, u64), u64> = HashMap::from([(("in", 0), 0), (("il", 0), 0)]);
    let mut next: HashMap<&str, u64> = HashMap::from([("in", 1), ("il", 1), ("ie", 0)]);
    for r in &keep {
        if let Some((sp, i)) = id_of(r) {
            let n = next[sp];
            new.insert((sp, i), n);
            *next.get_mut(sp).unwrap() = n + 1;
        }
    }
    let mut out = vec![lines[0].clone()];
    for r in keep {
        out.push(dumps(&renumber(r, &new)));
    }
    out
}

fn renumber(r: &Map<String, Value>, new: &HashMap<(&str, u64), u64>) -> Value {
    let n = |v: &Value| json!(new.get(&("in", u(v))).copied().unwrap_or(u(v)));
    let l = |v: &Value| json!(new.get(&("il", u(v))).copied().unwrap_or(u(v)));
    let e = |v: &Value| json!(new.get(&("ie", u(v))).copied().unwrap_or(u(v)));
    let mut r = r.clone();
    let k = kind_of(&r);
    if r.contains_key("in") {
        r["in"] = n(&r["in"]);
        let pre = n(&r[&k]["pre"]);
        r[&k]["pre"] = pre;
    } else if r.contains_key("il") {
        r["il"] = l(&r["il"]);
        let p = r[&k].clone();
        r[&k] = match k.as_str() {
            "succ" => l(&p),
            "max" | "imax" => json!([l(&p[0]), l(&p[1])]),
            "param" => n(&p),
            _ => p,
        };
    } else if r.contains_key("ie") {
        r["ie"] = e(&r["ie"]);
        let mut p = r[&k].clone();
        match k.as_str() {
            "sort" => p = l(&p),
            "const" => {
                p["name"] = n(&p["name"]);
                p["us"] = Value::Array(p["us"].as_array().unwrap().iter().map(l).collect());
            }
            "proj" => {
                p["typeName"] = n(&p["typeName"]);
                p["struct"] = e(&p["struct"]);
            }
            "bvar" | "natVal" | "strVal" => {}
            _ => {
                if p.get("name").is_some() {
                    p["name"] = n(&p["name"]);
                }
                for c in super::export::children(&k) {
                    p[*c] = e(&p[*c]);
                }
            }
        }
        r[&k] = p;
    } else {
        let mut p = r[&k].clone();
        let fix = |x: &mut Value| {
            for f in ["name", "induct"] {
                if x.get(f).is_some() {
                    x[f] = n(&x[f]);
                }
            }
            for f in ["levelParams", "all", "ctors"] {
                if let Some(a) = x.get(f).and_then(|v| v.as_array()) {
                    x[f] = Value::Array(a.iter().map(n).collect());
                }
            }
            for f in ["type", "value"] {
                if x.get(f).is_some() {
                    x[f] = e(&x[f]);
                }
            }
            if let Some(rules) = x.get_mut("rules").and_then(|v| v.as_array_mut()) {
                for rule in rules {
                    rule["ctor"] = n(&rule["ctor"]);
                    rule["rhs"] = e(&rule["rhs"]);
                }
            }
        };
        if k == "inductive" {
            for g in ["types", "ctors", "recs"] {
                for x in p[g].as_array_mut().into_iter().flatten() {
                    fix(x);
                }
            }
        } else {
            fix(&mut p);
        }
        r[&k] = p;
    }
    Value::Object(r)
}

fn axiomatize(line: &str) -> Option<String> {
    let r = parse(line);
    let k = kind_of(&r);
    if !matches!(k.as_str(), "def" | "thm" | "opaque") {
        return None;
    }
    let p = &r[&k];
    let unsafe_ =
        p.get("safety") == Some(&json!("unsafe")) || p.get("isUnsafe") == Some(&json!(true));
    Some(dumps(
        &json!({"axiom": {"name": p["name"], "levelParams": p["levelParams"], "type": p["type"],
                                  "isUnsafe": unsafe_}}),
    ))
}

fn decl_lines(lines: &[String]) -> Vec<usize> {
    (1..lines.len()).filter(|&i| is_decl(&lines[i])).collect()
}

/// Minimise `lines`; `holds` says whether a candidate keeps the verdict pair.
pub fn minimize(
    mut lines: Vec<String>,
    holds: &mut dyn FnMut(&[String]) -> bool,
    log: &dyn Fn(&str),
) -> Vec<String> {
    let idx = decl_lines(&lines);
    if idx.is_empty() {
        return lines;
    }
    let (mut lo, mut hi) = (0, idx.len() - 1);
    while lo < hi {
        let mid = (lo + hi) / 2;
        if holds(&lines[..=idx[mid]]) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    lines.truncate(idx[lo] + 1);
    log(&format!("prefix: {} declarations", lo + 1));
    let c = closure_prune(&lines);
    if c.len() < lines.len() && holds(&c) {
        lines = c;
        log(&format!(
            "closure: {} declarations",
            decl_lines(&lines).len()
        ));
    }
    let mut changed = true;
    while changed {
        changed = false;
        let mut idx = decl_lines(&lines);
        let mut chunk = (idx.len() / 4).max(1);
        loop {
            // never drop the last declaration: it is the one that differs
            let mut pos = idx.len() as isize - 2;
            while pos >= 0 {
                let lo = (pos - chunk as isize + 1).max(0) as usize;
                let drop: HashSet<usize> = idx[lo..=pos as usize].iter().copied().collect();
                let cand: Vec<String> = lines
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| !drop.contains(i))
                    .map(|(_, l)| l.clone())
                    .collect();
                if holds(&cand) {
                    lines = cand;
                    idx = decl_lines(&lines);
                    changed = true;
                    pos = pos.min(idx.len() as isize - 2) - chunk as isize;
                    continue;
                }
                pos -= chunk as isize;
            }
            if chunk == 1 {
                break;
            }
            chunk /= 2;
        }
        for i in decl_lines(&lines).into_iter().rev() {
            if let Some(ax) = axiomatize(&lines[i]) {
                let mut cand = lines.clone();
                cand[i] = ax;
                if holds(&cand) {
                    lines = cand;
                    changed = true;
                    let p = closure_prune(&lines);
                    if p.len() < lines.len() && holds(&p) {
                        lines = p;
                        break;
                    }
                }
            }
        }
        log(&format!(
            "now {} declarations, {} lines",
            decl_lines(&lines).len(),
            lines.len()
        ));
    }
    let g = gc(&lines);
    if holds(&g) {
        lines = g;
    }
    lines
}
