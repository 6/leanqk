//! A parsed lean4export (format 3.x) file, and mutants of it.
//!
//! A `Seed` indexes the records of an export. A `Mutant` is a seed with some
//! declaration lines replaced and new primitive records inserted right
//! before the mutated declaration. Existing records are never changed: a
//! changed subterm is rebuilt along its path to the root (path copying), so
//! other declarations that share hash-consed terms are untouched.

use std::collections::{BTreeMap, HashMap};
use std::sync::Mutex;

use serde_json::{Map, Value, json};

use super::rng::Rng;

/// The children of an expression kind, in order.
pub fn children(kind: &str) -> &'static [&'static str] {
    match kind {
        "app" => &["fn", "arg"],
        "lam" | "forallE" => &["type", "body"],
        "letE" => &["type", "value", "body"],
        "proj" => &["struct"],
        "mdata" => &["expr"],
        _ => &[],
    }
}

pub type Expr = (String, Value);

/// The kind (the key other than the id key) of a record.
pub fn kind_of(r: &Map<String, Value>) -> String {
    r.keys()
        .find(|k| !matches!(k.as_str(), "in" | "il" | "ie"))
        .cloned()
        .unwrap_or_default()
}

pub fn u(v: &Value) -> u64 {
    v.as_u64().unwrap_or(u64::MAX)
}

/// Where an expression field of a declaration record lives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Loc {
    /// The record itself (axiom, def, thm, opaque, quot).
    Top,
    /// `types[i]`, `ctors[i]` or `recs[i]` of an inductive block.
    Part(&'static str, usize),
    /// `recs[r].rules[i]`.
    Rule(usize, usize),
}

/// An expression root of a declaration: label, location, field, expression id.
#[derive(Clone, Debug)]
pub struct Root {
    pub label: &'static str,
    pub loc: Loc,
    pub field: &'static str,
    pub expr: u64,
}

pub fn at_loc(p: &Value, loc: Loc) -> &Value {
    match loc {
        Loc::Top => p,
        Loc::Part(g, i) => &p[g][i],
        Loc::Rule(r, i) => &p["recs"][r]["rules"][i],
    }
}

pub fn at_loc_mut(p: &mut Value, loc: Loc) -> &mut Value {
    match loc {
        Loc::Top => p,
        Loc::Part(g, i) => &mut p[g][i],
        Loc::Rule(r, i) => &mut p["recs"][r]["rules"][i],
    }
}

pub fn decl_roots(kind: &str, p: &Value) -> Vec<Root> {
    let mut out = Vec::new();
    if kind == "inductive" {
        for (g, label) in [("types", "type"), ("ctors", "ctor"), ("recs", "rec")] {
            for (i, x) in p[g].as_array().into_iter().flatten().enumerate() {
                out.push(Root {
                    label,
                    loc: Loc::Part(g, i),
                    field: "type",
                    expr: u(&x["type"]),
                });
            }
        }
        for (r, x) in p["recs"].as_array().into_iter().flatten().enumerate() {
            for (i, rule) in x["rules"].as_array().into_iter().flatten().enumerate() {
                out.push(Root {
                    label: "rule",
                    loc: Loc::Rule(r, i),
                    field: "rhs",
                    expr: u(&rule["rhs"]),
                });
            }
        }
    } else {
        for (f, label) in [("type", "type"), ("value", "value")] {
            if p.get(f).is_some() {
                out.push(Root {
                    label,
                    loc: Loc::Top,
                    field: f,
                    expr: u(&p[f]),
                });
            }
        }
    }
    out
}

/// The sub-records of a declaration that carry a name (for inductives: every
/// type, constructor and recursor).
pub fn infos(kind: &str, p: &Value) -> Vec<Value> {
    if kind == "inductive" {
        let mut v = Vec::new();
        for g in ["types", "ctors", "recs"] {
            v.extend(p[g].as_array().cloned().unwrap_or_default());
        }
        v
    } else {
        vec![p.clone()]
    }
}

pub struct Decl {
    pub line: usize,
    pub kind: String,
    pub payload: Value,
}

pub struct Seed {
    pub lines: Vec<String>,
    pub names: HashMap<u64, String>,
    pub name_ids: HashMap<String, u64>,
    pub ndef: HashMap<u64, usize>,
    pub levels: HashMap<u64, Expr>,
    pub exprs: HashMap<u64, Expr>,
    pub decls: Vec<Decl>,
    /// constant name -> (line, kind, info record)
    pub consts: HashMap<String, (usize, String, Value)>,
    pub max: [u64; 3],
    lbr: Mutex<HashMap<u64, u64>>,
}

impl Seed {
    pub fn parse(path: &str, text: &str) -> Result<Seed, String> {
        let lines: Vec<String> = text
            .lines()
            .filter(|l| !l.trim().is_empty())
            .map(String::from)
            .collect();
        let mut s = Seed {
            lines: Vec::new(),
            names: HashMap::from([(0, String::new())]),
            name_ids: HashMap::from([(String::new(), 0)]),
            ndef: HashMap::from([(0, 0)]),
            levels: HashMap::from([(0, ("zero".to_string(), Value::Null))]),
            exprs: HashMap::new(),
            decls: Vec::new(),
            consts: HashMap::new(),
            max: [0, 0, 0],
            lbr: Mutex::new(HashMap::new()),
        };
        for (i, ln) in lines.iter().enumerate().skip(1) {
            let r: Value =
                serde_json::from_str(ln).map_err(|e| format!("{path}:{}: {e}", i + 1))?;
            let r = r.as_object().ok_or("record is not an object")?;
            let k = kind_of(r);
            if let Some(id) = r.get("in") {
                let id = u(id);
                let p = &r[&k];
                let pre = s.names.get(&u(&p["pre"])).cloned().unwrap_or_default();
                let part = if k == "str" {
                    p["str"].as_str().unwrap_or("").to_string()
                } else {
                    p["i"].to_string()
                };
                let n = if pre.is_empty() {
                    part
                } else {
                    format!("{pre}.{part}")
                };
                s.name_ids.entry(n.clone()).or_insert(id);
                s.names.insert(id, n);
                s.ndef.insert(id, i);
                s.max[0] = s.max[0].max(id);
            } else if let Some(id) = r.get("il") {
                let id = u(id);
                s.levels.insert(id, (k.clone(), r[&k].clone()));
                s.max[1] = s.max[1].max(id);
            } else if let Some(id) = r.get("ie") {
                let id = u(id);
                s.exprs.insert(id, (k.clone(), r[&k].clone()));
                s.max[2] = s.max[2].max(id + 1);
            } else {
                let p = r[&k].clone();
                for x in infos(&k, &p) {
                    let n = s.name_str(u(&x["name"]));
                    s.consts.entry(n).or_insert((i, k.clone(), x));
                }
                s.decls.push(Decl {
                    line: i,
                    kind: k,
                    payload: p,
                });
            }
        }
        s.lines = lines;
        Ok(s)
    }

    pub fn name_str(&self, i: u64) -> String {
        self.names.get(&i).cloned().unwrap_or_else(|| "?".into())
    }

    pub fn decl_names(&self, d: &Decl) -> Vec<String> {
        infos(&d.kind, &d.payload)
            .iter()
            .map(|x| self.name_str(u(&x["name"])))
            .collect()
    }

    pub fn expr(&self, e: u64) -> &Expr {
        &self.exprs[&e]
    }

    pub fn ekind(&self, e: u64) -> &str {
        self.exprs.get(&e).map(|x| x.0.as_str()).unwrap_or("")
    }

    /// Loose bound variable range of `e` (memoised, iterative).
    pub fn lbr(&self, e: u64) -> u64 {
        let mut memo = self.lbr.lock().unwrap();
        if let Some(&v) = memo.get(&e) {
            return v;
        }
        let mut stack = vec![(e, false)];
        while let Some((x, ready)) = stack.pop() {
            if memo.contains_key(&x) {
                continue;
            }
            let Some((k, p)) = self.exprs.get(&x) else {
                memo.insert(x, 0);
                continue;
            };
            if k == "bvar" {
                memo.insert(x, u(p) + 1);
                continue;
            }
            let kids = children(k);
            if !ready {
                stack.push((x, true));
                for c in kids {
                    let y = u(&p[*c]);
                    if !memo.contains_key(&y) {
                        stack.push((y, false));
                    }
                }
                continue;
            }
            let mut r = 0;
            for c in kids {
                let mut v = memo.get(&u(&p[*c])).copied().unwrap_or(0);
                if *c == "body" {
                    v = v.saturating_sub(1);
                }
                r = r.max(v);
            }
            memo.insert(x, r);
        }
        memo[&e]
    }

    /// The name id of a dotted name if it is bound before `line`.
    pub fn name_before(&self, dotted: &str, line: usize) -> Option<u64> {
        let id = *self.name_ids.get(dotted)?;
        (self.ndef.get(&id).copied().unwrap_or(usize::MAX) < line).then_some(id)
    }

    pub fn const_before(&self, c: &str, line: usize) -> bool {
        self.consts.get(c).is_some_and(|x| x.0 < line)
    }
}

/// A tree position: the path of (expression, field) from the root, the
/// expression there, and its binder depth.
pub type Pos = (Vec<(u64, &'static str)>, u64, u64);

/// Up to `limit` tree positions of `root`, in a randomised depth-first order.
pub fn positions(seed: &Seed, root: u64, limit: usize, rng: Option<&mut Rng>) -> Vec<Pos> {
    let mut out = Vec::new();
    let mut stack: Vec<Pos> = vec![(Vec::new(), root, 0)];
    let mut rng = rng;
    while out.len() < limit {
        if let Some(r) = rng.as_deref_mut()
            && stack.len() > 1
            && r.chance(0.5)
        {
            let i = r.below(stack.len());
            let n = stack.len() - 1;
            stack.swap(i, n);
        }
        let Some((path, e, d)) = stack.pop() else {
            break;
        };
        if let Some((k, p)) = seed.exprs.get(&e) {
            for c in children(k) {
                let mut np = path.clone();
                np.push((e, *c));
                stack.push((np, u(&p[*c]), if *c == "body" { d + 1 } else { d }));
            }
        }
        out.push((path, e, d));
    }
    out
}

pub fn dumps(v: &Value) -> String {
    // serde_json's maps are ordered by key, as the exporter writes them.
    v.to_string()
}

pub struct Mutant<'s> {
    pub seed: &'s Seed,
    pub line: usize,
    pub replace: BTreeMap<usize, Option<String>>,
    pub insert: Vec<Value>,
    next: [u64; 3],
    keys: HashMap<String, u64>,
    new_exprs: HashMap<u64, Expr>,
    pub op: String,
    pub decl: String,
    pub note: String,
    pub truncate: bool,
    pub expect: &'static str,
}

impl<'s> Mutant<'s> {
    pub fn new(seed: &'s Seed, line: usize) -> Mutant<'s> {
        Mutant {
            seed,
            line,
            replace: BTreeMap::new(),
            insert: Vec::new(),
            next: [seed.max[0] + 1, seed.max[1] + 1, seed.max[2]],
            keys: HashMap::new(),
            new_exprs: HashMap::new(),
            op: String::new(),
            decl: String::new(),
            note: String::new(),
            truncate: false,
            expect: "reject",
        }
    }

    fn fresh(&mut self, space: usize, sp: &str, kind: &str, payload: Value) -> u64 {
        let key = format!("{sp}:{kind}:{payload}");
        if let Some(&i) = self.keys.get(&key) {
            return i;
        }
        let i = self.next[space];
        self.next[space] += 1;
        let mut r = Map::new();
        r.insert(sp.to_string(), json!(i));
        r.insert(kind.to_string(), payload.clone());
        self.insert.push(Value::Object(r));
        self.keys.insert(key, i);
        if sp == "ie" {
            self.new_exprs.insert(i, (kind.to_string(), payload));
        }
        i
    }

    pub fn expr(&mut self, kind: &str, payload: Value) -> u64 {
        self.fresh(2, "ie", kind, payload)
    }

    pub fn level(&mut self, kind: &str, payload: Value) -> u64 {
        if kind == "zero" {
            return 0;
        }
        self.fresh(1, "il", kind, payload)
    }

    /// The id of a dotted name made of string parts, created if not bound before the line.
    pub fn name(&mut self, dotted: &str) -> u64 {
        if let Some(i) = self.seed.name_before(dotted, self.line) {
            return i;
        }
        let mut pre = 0;
        let mut sofar = String::new();
        for part in dotted.split('.') {
            if !sofar.is_empty() {
                sofar.push('.');
            }
            sofar.push_str(part);
            pre = match self.seed.name_before(&sofar, self.line) {
                Some(i) => i,
                None => self.fresh(0, "in", "str", json!({"pre": pre, "str": part})),
            };
        }
        pre
    }

    /// (kind, payload) of an existing or new expression.
    pub fn get(&self, e: u64) -> Option<&Expr> {
        self.seed.exprs.get(&e).or_else(|| self.new_exprs.get(&e))
    }

    /// Replace the subterm at `path` with `new`; the new root.
    pub fn rebuild(&mut self, path: &[(u64, &'static str)], mut new: u64) -> u64 {
        for (e, field) in path.iter().rev() {
            let (k, p) = self.get(*e).cloned().expect("path expression");
            let mut q = p;
            q[*field] = json!(new);
            new = self.expr(&k, q);
        }
        new
    }

    /// Shift the loose bound variables >= cutoff of `e` by n.
    pub fn lift(&mut self, e: u64, n: u64, cutoff: u64) -> u64 {
        let mut memo = HashMap::new();
        self.lift_go(e, n, cutoff, &mut memo)
    }

    fn lift_go(&mut self, x: u64, n: u64, c: u64, memo: &mut HashMap<(u64, u64), u64>) -> u64 {
        if self.seed.exprs.contains_key(&x) && self.seed.lbr(x) <= c {
            return x;
        }
        if let Some(&r) = memo.get(&(x, c)) {
            return r;
        }
        let Some((k, p)) = self.get(x).cloned() else {
            return x;
        };
        let r = if k == "bvar" {
            let i = u(&p);
            if i >= c {
                self.expr("bvar", json!(i + n))
            } else {
                x
            }
        } else if !children(&k).is_empty() {
            let mut q = p.clone();
            for f in children(&k) {
                let y = self.lift_go(u(&p[*f]), n, if *f == "body" { c + 1 } else { c }, memo);
                q[*f] = json!(y);
            }
            self.expr(&k, q)
        } else {
            x
        };
        memo.insert((x, c), r);
        r
    }

    /// The declaration record being built (the replaced one, else a copy of the seed's).
    pub fn current(&self, kind: &str, payload: &Value) -> Value {
        match self.replace.get(&self.line) {
            Some(Some(s)) => {
                let v: Value = serde_json::from_str(s).expect("own record");
                v[kind].clone()
            }
            _ => payload.clone(),
        }
    }

    pub fn set_decl(&mut self, kind: &str, p: Value) {
        let mut r = Map::new();
        r.insert(kind.to_string(), p);
        self.replace
            .insert(self.line, Some(dumps(&Value::Object(r))));
    }

    /// Replace one expression field of the declaration.
    pub fn set_root(&mut self, kind: &str, payload: &Value, root: &Root, new: u64) {
        let mut p = self.current(kind, payload);
        at_loc_mut(&mut p, root.loc)[root.field] = json!(new);
        self.set_decl(kind, p);
    }

    pub fn text(&self) -> String {
        let mut out = String::new();
        for (i, ln) in self.seed.lines.iter().enumerate() {
            if i == self.line {
                for r in &self.insert {
                    out.push_str(&dumps(r));
                    out.push('\n');
                }
            }
            match self.replace.get(&i) {
                Some(Some(s)) => {
                    out.push_str(s);
                    out.push('\n');
                }
                Some(None) => {}
                None => {
                    out.push_str(ln);
                    out.push('\n');
                }
            }
            if self.truncate && i == self.line {
                break;
            }
        }
        out
    }
}

/// The (space, id) pairs a record refers to.
pub fn deps(r: &Map<String, Value>) -> Vec<(&'static str, u64)> {
    let mut out = Vec::new();
    let k = kind_of(r);
    let p = &r[&k];
    if r.contains_key("in") {
        out.push(("in", u(&p["pre"])));
    } else if r.contains_key("il") {
        match k.as_str() {
            "succ" => out.push(("il", u(p))),
            "max" | "imax" => {
                out.push(("il", u(&p[0])));
                out.push(("il", u(&p[1])));
            }
            "param" => out.push(("in", u(p))),
            _ => {}
        }
    } else if r.contains_key("ie") {
        match k.as_str() {
            "sort" => out.push(("il", u(p))),
            "const" => {
                out.push(("in", u(&p["name"])));
                for l in p["us"].as_array().into_iter().flatten() {
                    out.push(("il", u(l)));
                }
            }
            "proj" => {
                out.push(("in", u(&p["typeName"])));
                out.push(("ie", u(&p["struct"])));
            }
            "bvar" | "natVal" | "strVal" => {}
            _ => {
                if let Some(n) = p.get("name") {
                    out.push(("in", u(n)));
                }
                for c in children(&k) {
                    out.push(("ie", u(&p[*c])));
                }
            }
        }
    } else {
        for x in infos(&k, p) {
            for f in ["name", "induct"] {
                if let Some(n) = x.get(f) {
                    out.push(("in", u(n)));
                }
            }
            for f in ["levelParams", "all", "ctors"] {
                for n in x.get(f).and_then(|v| v.as_array()).into_iter().flatten() {
                    out.push(("in", u(n)));
                }
            }
            for f in ["type", "value"] {
                if let Some(e) = x.get(f) {
                    out.push(("ie", u(e)));
                }
            }
            for rule in x
                .get("rules")
                .and_then(|v| v.as_array())
                .into_iter()
                .flatten()
            {
                out.push(("in", u(&rule["ctor"])));
                out.push(("ie", u(&rule["rhs"])));
            }
        }
    }
    out
}
