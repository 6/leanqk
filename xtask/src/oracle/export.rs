//! Streaming helpers for lean4export NDJSON files (format 3.x), for the
//! oracle's runner and reducer.
//!
//! An export is a sequence of lines: the `meta` line, names (`in`), levels
//! (`il`), expressions (`ie`) and declaration records (`axiom`, `def`, `thm`,
//! `opaque`, `quot`, `inductive`; an `inductive` record carries a whole mutual
//! block). Every record refers only to ids bound on earlier lines, and ids
//! need not be dense, so dropping lines that nothing kept refers to leaves a
//! valid export.
//!
//! The passes read the file line by line and keep, per expression id, one
//! flag (and for `Graph`, the expression's children).

use std::collections::{HashMap, HashSet};
use std::fs;
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::Path;

use anyhow::{Context, Result, anyhow};
use serde_json::Value;

pub const DECL_KEYS: [&str; 6] = ["axiom", "def", "thm", "opaque", "quot", "inductive"];
/// Expression fields that hold expression ids.
const EXPR_CHILDREN: [(&str, &[&str]); 6] = [
    ("app", &["fn", "arg"]),
    ("lam", &["type", "body"]),
    ("forallE", &["type", "body"]),
    ("letE", &["type", "value", "body"]),
    ("proj", &["struct"]),
    ("mdata", &["expr"]),
];

/// A declaration name as both checkers print it, without Lean's «» escapes.
pub fn norm_name(s: &str) -> String {
    s.replace(['«', '»'], "")
}

/// Calls `f` with the number and bytes (newline included) of every line.
pub fn for_lines(path: &Path, mut f: impl FnMut(usize, &[u8]) -> Result<()>) -> Result<()> {
    let file = fs::File::open(path).with_context(|| format!("{}: cannot open", path.display()))?;
    let mut r = BufReader::with_capacity(1 << 20, file);
    let mut buf = Vec::new();
    let mut no = 0;
    loop {
        buf.clear();
        if r.read_until(b'\n', &mut buf)? == 0 {
            return Ok(());
        }
        f(no, &buf)?;
        no += 1;
    }
}

fn int(v: &Value, key: &str) -> Result<i64> {
    v.get(key)
        .and_then(Value::as_i64)
        .ok_or_else(|| anyhow!("export: record without an integer `{key}`: {v}"))
}

fn list<'a>(v: &'a Value, key: &str) -> &'a [Value] {
    v.get(key)
        .and_then(Value::as_array)
        .map(Vec::as_slice)
        .unwrap_or(&[])
}

/// What a line holds: "name", "level", "expr", "meta", a declaration key, or "".
fn classify(obj: &Value) -> &'static str {
    if obj.get("in").is_some() {
        "name"
    } else if obj.get("il").is_some() {
        "level"
    } else if obj.get("ie").is_some() {
        "expr"
    } else if obj.get("meta").is_some() {
        "meta"
    } else {
        decl_kind(obj).unwrap_or("")
    }
}

pub fn decl_kind(obj: &Value) -> Option<&'static str> {
    DECL_KEYS.iter().copied().find(|k| obj.get(*k).is_some())
}

/// The object on a line and what it holds; a line that is not a JSON object
/// is (null, ""), and is left for the checkers to report.
pub fn parse(raw: &[u8]) -> (Value, &'static str) {
    match serde_json::from_slice::<Value>(raw) {
        Ok(v) if v.is_object() => {
            let k = classify(&v);
            (v, k)
        }
        _ => (Value::Null, ""),
    }
}

/// Name ids of the constants a declaration record introduces.
pub fn decl_names(kind: &str, body: &Value) -> Result<Vec<i64>> {
    if kind == "inductive" {
        let mut out = Vec::new();
        for part in ["types", "ctors", "recs"] {
            for x in list(body, part) {
                out.push(int(x, "name")?);
            }
        }
        return Ok(out);
    }
    Ok(vec![int(body, "name")?])
}

/// Expression ids a declaration record refers to.
pub fn decl_roots(kind: &str, body: &Value) -> Result<Vec<i64>> {
    match kind {
        "axiom" | "quot" => Ok(vec![int(body, "type")?]),
        "def" | "thm" | "opaque" => Ok(vec![int(body, "type")?, int(body, "value")?]),
        _ => {
            let mut out = Vec::new();
            for x in list(body, "types").iter().chain(list(body, "ctors")) {
                out.push(int(x, "type")?);
            }
            for r in list(body, "recs") {
                out.push(int(r, "type")?);
                for rule in list(r, "rules") {
                    out.push(int(rule, "rhs")?);
                }
            }
            Ok(out)
        }
    }
}

/// (children expression ids, constant name id) of an `ie` record.
fn expr_children(obj: &Value) -> Result<(Vec<i64>, Option<i64>)> {
    for (k, fields) in EXPR_CHILDREN {
        if let Some(v) = obj.get(k) {
            return Ok((
                fields.iter().map(|f| int(v, f)).collect::<Result<_>>()?,
                None,
            ));
        }
    }
    if let Some(c) = obj.get("const") {
        return Ok((Vec::new(), Some(int(c, "name")?)));
    }
    Ok((Vec::new(), None))
}

/// Name ids to strings (only the names that are asked for are rendered).
#[derive(Default)]
pub struct Names {
    parts: HashMap<i64, (i64, String)>,
}

impl Names {
    pub fn add(&mut self, obj: &Value) -> Result<()> {
        let i = int(obj, "in")?;
        let part = if let Some(s) = obj.get("str") {
            let t = s
                .get("str")
                .and_then(Value::as_str)
                .ok_or_else(|| anyhow!("export: bad name record {obj}"))?;
            (int(s, "pre")?, t.to_string())
        } else {
            let n = obj
                .get("num")
                .ok_or_else(|| anyhow!("export: bad name record {obj}"))?;
            let i = n
                .get("i")
                .ok_or_else(|| anyhow!("export: bad name record {obj}"))?;
            (int(n, "pre")?, i.to_string())
        };
        self.parts.insert(i, part);
        Ok(())
    }

    pub fn render(&self, mut i: i64) -> String {
        let mut out = Vec::new();
        while i != 0 {
            let Some((pre, s)) = self.parts.get(&i) else {
                break;
            };
            out.push(s.as_str());
            i = *pre;
        }
        out.reverse();
        out.join(".")
    }
}

/// A declaration record: kind and constant names.
pub struct Decl {
    pub kind: &'static str,
    pub names: Vec<String>,
}

/// What one pass learns about an export: its declaration records, in file order.
pub struct Index {
    pub decls: Vec<Decl>,
    /// Normalized constant name to its record (the last one, if several).
    pub by_name: HashMap<String, usize>,
}

impl Index {
    pub fn new(path: &Path) -> Result<Index> {
        let mut names = Names::default();
        let mut decls = Vec::new();
        for_lines(path, |_no, raw| {
            let (obj, k) = parse(raw);
            if k == "name" {
                names.add(&obj)?;
            } else if DECL_KEYS.contains(&k) {
                let ids = decl_names(k, &obj[k])?;
                decls.push(Decl {
                    kind: k,
                    names: ids.iter().map(|&i| names.render(i)).collect(),
                });
            }
            Ok(())
        })?;
        let mut by_name = HashMap::new();
        for (i, d) in decls.iter().enumerate() {
            for n in &d.names {
                by_name.insert(norm_name(n), i);
            }
        }
        Ok(Index { decls, by_name })
    }

    pub fn constants(&self) -> impl Iterator<Item = &String> {
        self.decls.iter().flat_map(|d| d.names.iter())
    }
}

/// `{"axiom":{...}}` for a `thm`, `def` or `opaque` body, as Python's
/// `json.dumps(..., separators=(",", ":"))` writes it.
fn axiom_line(b: &Value) -> Result<Vec<u8>> {
    let field = |k: &str| {
        b.get(k)
            .map(|v| v.to_string())
            .ok_or_else(|| anyhow!("export: record without `{k}`: {b}"))
    };
    Ok(format!(
        "{{\"axiom\":{{\"name\":{},\"levelParams\":{},\"type\":{},\"isUnsafe\":false}}}}\n",
        field("name")?,
        field("levelParams")?,
        field("type")?
    )
    .into_bytes())
}

fn flag(bad: &[bool], i: i64) -> bool {
    i >= 0 && (i as usize) < bad.len() && bad[i as usize]
}

/// Copies `src` to `dst` without the declaration records that introduce one
/// of `drop_names` (normalized), and without every record that depends on a
/// dropped one, with the theorems named in `axiomatize` turned into axioms.
///
/// Repeats the pass until no new record is dropped (a constant can be used by
/// an expression that comes before its declaration). Returns the dropped
/// constant names (normalized).
pub fn rewrite(
    src: &Path,
    dst: &Path,
    drop_names: &HashSet<String>,
    axiomatize: &HashSet<String>,
) -> Result<HashSet<String>> {
    let mut drop: HashSet<String> = drop_names.iter().map(|n| norm_name(n)).collect();
    let axiomatize: HashSet<String> = axiomatize.iter().map(|n| norm_name(n)).collect();
    let (dropped, dropped_lines) = loop {
        let mut names = Names::default();
        let mut bad_names: HashSet<i64> = HashSet::new();
        let mut bad: Vec<bool> = Vec::new();
        let mut dropped: HashSet<String> = HashSet::new();
        let mut dropped_lines: HashSet<usize> = HashSet::new();
        for_lines(src, |no, raw| {
            let (obj, k) = parse(raw);
            if k == "name" {
                names.add(&obj)?;
                let i = int(&obj, "in")?;
                if drop.contains(&norm_name(&names.render(i))) {
                    bad_names.insert(i);
                }
            } else if DECL_KEYS.contains(&k) {
                let body = &obj[k];
                let ids = decl_names(k, body)?;
                let ns: Vec<String> = ids.iter().map(|&i| norm_name(&names.render(i))).collect();
                let mut roots = decl_roots(k, body)?;
                if k == "thm" && axiomatize.contains(&ns[0]) {
                    roots.truncate(1);
                }
                if ns.iter().any(|n| drop.contains(n)) || roots.iter().any(|&r| flag(&bad, r)) {
                    dropped.extend(ns);
                    dropped_lines.insert(no);
                    bad_names.extend(ids);
                }
            } else if k == "expr" {
                let ie = int(&obj, "ie")?;
                let (ch, c) = expr_children(&obj)?;
                let v =
                    c.is_some_and(|c| bad_names.contains(&c)) || ch.iter().any(|&x| flag(&bad, x));
                if v && ie >= 0 {
                    let ie = ie as usize;
                    if ie >= bad.len() {
                        bad.resize(ie + 1 + (1 << 16), false);
                    }
                    bad[ie] = true;
                }
            }
            Ok(())
        })?;
        if dropped.is_subset(&drop) {
            break (dropped, dropped_lines);
        }
        drop.extend(dropped);
    };
    let mut out = BufWriter::new(
        fs::File::create(dst).with_context(|| format!("{}: cannot create", dst.display()))?,
    );
    let mut names = Names::default();
    for_lines(src, |no, raw| {
        if dropped_lines.contains(&no) {
            return Ok(());
        }
        if axiomatize.is_empty() {
            out.write_all(raw)?;
            return Ok(());
        }
        let (obj, k) = parse(raw);
        if k == "name" {
            names.add(&obj)?;
        } else if k == "thm" {
            let name = int(&obj["thm"], "name")?;
            if axiomatize.contains(&norm_name(&names.render(name))) {
                out.write_all(&axiom_line(&obj["thm"])?)?;
                return Ok(());
            }
        }
        out.write_all(raw)?;
        Ok(())
    })?;
    out.flush()?;
    Ok(dropped)
}

/// The whole export in memory, compactly: for `closure`. Expression children
/// are kept in flat arrays, so a large export takes a few bytes per expression.
pub struct Graph {
    path: std::path::PathBuf,
    pub names: Names,
    kids_start: Vec<usize>,
    /// Children ids; a constant is -(name id) - 1.
    kids: Vec<i64>,
    expr_pos: HashMap<i64, usize>,
    /// Name id to the line number of its declaration record.
    pub decl_of: HashMap<i64, usize>,
    /// The name ids of `decl_of`, in the order they were first seen.
    decl_of_order: Vec<i64>,
    /// Line number to (kind, root expression ids).
    pub decl_roots: HashMap<usize, (&'static str, Vec<i64>)>,
    /// Per line: b'n', b'l', b'e', b'd' or b'm', and its id.
    line_kind: Vec<(u8, i64)>,
}

impl Graph {
    pub fn new(path: &Path) -> Result<Graph> {
        let mut g = Graph {
            path: path.to_path_buf(),
            names: Names::default(),
            kids_start: Vec::new(),
            kids: Vec::new(),
            expr_pos: HashMap::new(),
            decl_of: HashMap::new(),
            decl_of_order: Vec::new(),
            decl_roots: HashMap::new(),
            line_kind: Vec::new(),
        };
        for_lines(path, |no, raw| {
            let (obj, k) = parse(raw);
            if k == "name" {
                g.names.add(&obj)?;
                g.line_kind.push((b'n', int(&obj, "in")?));
            } else if DECL_KEYS.contains(&k) {
                let body = &obj[k];
                for i in decl_names(k, body)? {
                    if g.decl_of.insert(i, no).is_none() {
                        g.decl_of_order.push(i);
                    }
                }
                g.decl_roots.insert(no, (k, decl_roots(k, body)?));
                g.line_kind.push((b'd', no as i64));
            } else if k == "level" {
                g.line_kind.push((b'l', int(&obj, "il")?));
            } else if k == "expr" {
                let ie = int(&obj, "ie")?;
                let (ch, c) = expr_children(&obj)?;
                g.expr_pos.insert(ie, g.kids_start.len());
                g.kids_start.push(g.kids.len());
                g.kids.extend(ch);
                if let Some(c) = c {
                    g.kids.push(-c - 1);
                }
                g.line_kind.push((b'e', ie));
            } else {
                g.line_kind.push((b'm', 0));
            }
            Ok(())
        })?;
        g.kids_start.push(g.kids.len());
        Ok(g)
    }

    /// The name id of a declared constant, by its (normalized) name.
    pub fn name_id(&self, name: &str) -> Option<i64> {
        let want = norm_name(name);
        self.decl_of_order
            .iter()
            .copied()
            .find(|&i| norm_name(&self.names.render(i)) == want)
    }

    fn children(&self, e: i64) -> Result<&[i64]> {
        let p = *self
            .expr_pos
            .get(&e)
            .ok_or_else(|| anyhow!("export: undefined expression id {e}"))?;
        Ok(&self.kids[self.kids_start[p]..self.kids_start[p + 1]])
    }

    fn roots(&self, no: usize, value_free: &HashSet<usize>) -> &[i64] {
        let (k, roots) = &self.decl_roots[&no];
        if value_free.contains(&no) && matches!(*k, "def" | "thm" | "opaque") {
            &roots[..1]
        } else {
            roots
        }
    }

    /// Line numbers of the declaration records needed by `start` (themselves
    /// included). Records in `value_free` are taken as axioms: only their
    /// types count.
    pub fn closure(&self, start: &[usize], value_free: &HashSet<usize>) -> Result<HashSet<usize>> {
        let mut need = HashSet::new();
        let mut stack = start.to_vec();
        let mut seen = HashSet::new();
        while let Some(no) = stack.pop() {
            if !need.insert(no) {
                continue;
            }
            let mut work = self.roots(no, value_free).to_vec();
            while let Some(e) = work.pop() {
                if !seen.insert(e) {
                    continue;
                }
                for &x in self.children(e)? {
                    if x < 0 {
                        if let Some(&d) = self.decl_of.get(&(-x - 1))
                            && !need.contains(&d)
                        {
                            stack.push(d);
                        }
                    } else {
                        work.push(x);
                    }
                }
            }
        }
        Ok(need)
    }

    /// Writes the records on `decl_lines` (those in `value_free` made axioms)
    /// and every name and level line, with the expressions pruned to those
    /// reachable from them.
    pub fn write(
        &self,
        dst: &Path,
        decl_lines: &HashSet<usize>,
        value_free: &HashSet<usize>,
    ) -> Result<()> {
        let mut keep = HashSet::new();
        for &no in decl_lines {
            let mut work = self.roots(no, value_free).to_vec();
            while let Some(e) = work.pop() {
                if !keep.insert(e) {
                    continue;
                }
                work.extend(self.children(e)?.iter().copied().filter(|&x| x >= 0));
            }
        }
        let mut out = BufWriter::new(
            fs::File::create(dst).with_context(|| format!("{}: cannot create", dst.display()))?,
        );
        for_lines(&self.path, |no, raw| {
            let (kind, v) = self.line_kind[no];
            if kind == b'e' && !keep.contains(&v) {
                return Ok(());
            }
            if kind == b'd' {
                if !decl_lines.contains(&no) {
                    return Ok(());
                }
                if value_free.contains(&no) {
                    let obj: Value = serde_json::from_slice(raw)?;
                    if let Some(k) = decl_kind(&obj)
                        && matches!(k, "def" | "thm" | "opaque")
                    {
                        out.write_all(&axiom_line(&obj[k])?)?;
                        return Ok(());
                    }
                }
            }
            out.write_all(raw)?;
            Ok(())
        })?;
        out.flush()?;
        Ok(())
    }
}
