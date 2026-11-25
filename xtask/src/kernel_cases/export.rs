//! Reading, building and mutating lean4export (format 3.x) files.
//!
//! An export is a list of JSON records. Names (`in`), levels (`il`) and
//! expressions (`ie`) have their own id spaces; declarations refer to them by
//! id. `Export` keeps the records in order, hash-conses new terms against
//! existing ones, and inserts the new primitive records right before the
//! declaration that first needs them, so the output stays in dependency
//! order. Ids are given out in the order the terms are made, so the order of
//! the calls that make them decides the output.

use std::collections::HashMap;

use serde_json::{Map, Value, json};

pub const EXPR_CHILDREN: [&str; 7] = ["fn", "arg", "type", "body", "value", "struct", "expr"];

/// A record as one compact line with sorted keys (`serde_json`'s maps are
/// sorted): the same bytes as Python's
/// `json.dumps(rec, ensure_ascii=False, separators=(",", ":"), sort_keys=True)`.
pub fn dumps(v: &Value) -> String {
    serde_json::to_string(v).expect("JSON values serialise")
}

/// The kind of a record: its key other than `in`, `il` and `ie`.
pub fn kind_of(r: &Value) -> &str {
    r.as_object()
        .and_then(|m| m.keys().find(|k| !matches!(k.as_str(), "in" | "il" | "ie")))
        .map(String::as_str)
        .unwrap_or_else(|| panic!("record without a kind: {r}"))
}

/// A component of a name.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Part {
    Str(String),
    Num(u64),
}

pub type Id = u64;

fn id(v: &Value) -> Id {
    v.as_u64().unwrap_or_else(|| panic!("not an id: {v}"))
}

/// A binder: name id, type id, binder info.
pub type Binder = (Id, Id, String);

pub struct Export {
    pub meta: Value,
    pub recs: Vec<Value>,
    pending: Vec<Value>,
    pub names: HashMap<Id, Vec<Part>>,
    name_ids: HashMap<Vec<Part>, Id>,
    /// Kind and payload (as canonical JSON) of each level; level 0 is zero.
    pub levels: HashMap<Id, (String, String)>,
    level_ids: HashMap<(String, String), Id>,
    pub exprs: HashMap<Id, (String, Value)>,
    expr_ids: HashMap<(String, String), Id>,
    max_name: Option<Id>,
    max_level: Option<Id>,
    max_expr: Option<Id>,
}

/// What an expression callback of `rebuild` gets: id, kind, payload, depth.
pub type ExprFn<'a> = dyn FnMut(&mut Export, Id, &str, &Value, u64) -> Option<Id> + 'a;
pub type LevelFn<'a> = dyn FnMut(&mut Export, Id) -> Id + 'a;

impl Export {
    pub fn new(text: &str) -> Export {
        let mut lines = text.split('\n').filter(|l| !l.trim().is_empty());
        let meta = serde_json::from_str(lines.next().expect("an export has a meta line"))
            .expect("the meta line is JSON");
        let recs: Vec<Value> = lines
            .map(|l| serde_json::from_str(l).expect("export records are JSON"))
            .collect();
        let mut e = Export {
            meta,
            recs: Vec::new(),
            pending: Vec::new(),
            names: HashMap::new(),
            name_ids: HashMap::new(),
            levels: HashMap::new(),
            level_ids: HashMap::new(),
            exprs: HashMap::new(),
            expr_ids: HashMap::new(),
            max_name: None,
            max_level: None,
            max_expr: None,
        };
        e.names.insert(0, Vec::new());
        e.name_ids.insert(Vec::new(), 0);
        e.max_name = Some(0);
        let zero = ("zero".to_string(), String::new());
        e.levels.insert(0, zero.clone());
        e.level_ids.insert(zero, 0);
        e.max_level = Some(0);
        for r in &recs {
            e.learn(r);
        }
        e.recs = recs;
        e
    }

    /// An export with only the given meta record.
    pub fn empty(meta: &Value) -> Export {
        Export::new(&(dumps(meta) + "\n"))
    }

    fn learn(&mut self, r: &Value) {
        let m = r.as_object().unwrap();
        if let Some(i) = m.get("in") {
            let i = id(i);
            let n = if let Some(s) = m.get("str") {
                let mut n = self.names[&id(&s["pre"])].clone();
                n.push(Part::Str(s["str"].as_str().unwrap().to_string()));
                n
            } else {
                let s = &m["num"];
                let mut n = self.names[&id(&s["pre"])].clone();
                n.push(Part::Num(id(&s["i"])));
                n
            };
            self.names.insert(i, n.clone());
            self.name_ids.entry(n).or_insert(i);
            self.max_name = self.max_name.max(Some(i));
        } else if let Some(i) = m.get("il") {
            let i = id(i);
            let k = kind_of(r).to_string();
            let key = (k.clone(), dumps(&m[&k]));
            self.levels.insert(i, key.clone());
            self.level_ids.entry(key).or_insert(i);
            self.max_level = self.max_level.max(Some(i));
        } else if let Some(i) = m.get("ie") {
            let i = id(i);
            let k = kind_of(r).to_string();
            let key = (k.clone(), dumps(&m[&k]));
            self.exprs.insert(i, (k, m[&key.0].clone()));
            self.expr_ids.entry(key).or_insert(i);
            self.max_expr = self.max_expr.max(Some(i));
        }
    }

    /// Serialise, pulling every primitive record in front of its first user.
    pub fn text(&mut self) -> String {
        let pending = std::mem::take(&mut self.pending);
        self.recs.extend(pending);
        let mut place: HashMap<(&'static str, Id), usize> = HashMap::new();
        for (i, r) in self.recs.iter().enumerate() {
            for sp in ["in", "il", "ie"] {
                if let Some(x) = r.get(sp) {
                    place.insert((sp, id(x)), i);
                }
            }
        }
        let mut done = vec![false; self.recs.len()];
        let mut order = Vec::with_capacity(self.recs.len());
        for start in 0..self.recs.len() {
            let mut stack = vec![(start, false)];
            while let Some((x, ready)) = stack.pop() {
                if done[x] {
                    continue;
                }
                if ready {
                    done[x] = true;
                    order.push(x);
                    continue;
                }
                stack.push((x, true));
                for d in deps(&self.recs[x]).into_iter().rev() {
                    if let Some(&y) = place.get(&d)
                        && !done[y]
                    {
                        stack.push((y, false));
                    }
                }
            }
        }
        let mut old: Vec<Option<Value>> = std::mem::take(&mut self.recs)
            .into_iter()
            .map(Some)
            .collect();
        self.recs = order.iter().map(|&i| old[i].take().unwrap()).collect();
        let mut out = dumps(&self.meta);
        for r in &self.recs {
            out.push('\n');
            out.push_str(&dumps(r));
        }
        out.push('\n');
        out
    }

    fn new_prim(&mut self, space: &str, kind: &str, payload: Value) -> Id {
        let key = (kind.to_string(), dumps(&payload));
        let ids = match space {
            "il" => &self.level_ids,
            _ => &self.expr_ids,
        };
        if let Some(&i) = ids.get(&key) {
            return i;
        }
        let fresh = match space {
            "il" => self.max_level,
            _ => self.max_expr,
        }
        .map_or(0, |m| m + 1);
        let mut m = Map::new();
        m.insert(space.to_string(), json!(fresh));
        m.insert(kind.to_string(), payload);
        let r = Value::Object(m);
        self.learn(&r);
        self.pending.push(r);
        fresh
    }

    // ----- names -----------------------------------------------------------

    /// Id of a dotted name, created if missing (numeric parts not supported).
    pub fn name(&mut self, s: &str) -> Id {
        let parts: Vec<Part> = if s.is_empty() {
            Vec::new()
        } else {
            s.split('.').map(|p| Part::Str(p.to_string())).collect()
        };
        self.name_parts(&parts)
    }

    fn name_parts(&mut self, parts: &[Part]) -> Id {
        if let Some(&i) = self.name_ids.get(parts) {
            return i;
        }
        let pre = self.name_parts(&parts[..parts.len() - 1]);
        let Part::Str(last) = &parts[parts.len() - 1] else {
            unreachable!()
        };
        let fresh = self.max_name.map_or(0, |m| m + 1);
        let r = json!({"in": fresh, "str": {"pre": pre, "str": last}});
        self.learn(&r);
        self.pending.push(r);
        fresh
    }

    /// The id of an existing dotted name.
    pub fn name_id(&self, s: &str) -> Option<Id> {
        let parts: Vec<Part> = s.split('.').map(|p| Part::Str(p.to_string())).collect();
        self.name_ids.get(&parts).copied()
    }

    pub fn name_str(&self, i: Id) -> String {
        self.names[&i]
            .iter()
            .map(|p| match p {
                Part::Str(s) => s.clone(),
                Part::Num(n) => n.to_string(),
            })
            .collect::<Vec<_>>()
            .join(".")
    }

    // ----- levels ----------------------------------------------------------

    pub fn lsucc(&mut self, l: Id) -> Id {
        self.new_prim("il", "succ", json!(l))
    }

    pub fn lmax(&mut self, a: Id, b: Id) -> Id {
        self.new_prim("il", "max", json!([a, b]))
    }

    pub fn limax(&mut self, a: Id, b: Id) -> Id {
        self.new_prim("il", "imax", json!([a, b]))
    }

    pub fn lparam(&mut self, s: &str) -> Id {
        let n = self.name(s);
        self.new_prim("il", "param", json!(n))
    }

    pub fn lnum(&mut self, n: usize) -> Id {
        let mut l = 0;
        for _ in 0..n {
            l = self.lsucc(l);
        }
        l
    }

    // ----- expressions -----------------------------------------------------

    pub fn expr(&mut self, kind: &str, payload: Value) -> Id {
        self.new_prim("ie", kind, payload)
    }

    pub fn bvar(&mut self, i: u64) -> Id {
        self.expr("bvar", json!(i))
    }

    pub fn sort(&mut self, l: Id) -> Id {
        self.expr("sort", json!(l))
    }

    pub fn konst(&mut self, s: &str, us: &[Id]) -> Id {
        let n = self.name(s);
        self.expr("const", json!({"name": n, "us": us}))
    }

    pub fn c(&mut self, s: &str) -> Id {
        self.konst(s, &[])
    }

    pub fn app(&mut self, mut f: Id, args: &[Id]) -> Id {
        for &a in args {
            f = self.expr("app", json!({"fn": f, "arg": a}));
        }
        f
    }

    pub fn pi(&mut self, n: &str, ty: Id, body: Id) -> Id {
        let n = self.name(n);
        self.expr(
            "forallE",
            json!({"binderInfo": "default", "body": body, "name": n, "type": ty}),
        )
    }

    pub fn lam(&mut self, n: &str, ty: Id, body: Id) -> Id {
        let n = self.name(n);
        self.expr(
            "lam",
            json!({"binderInfo": "default", "body": body, "name": n, "type": ty}),
        )
    }

    pub fn nat(&mut self, v: &str) -> Id {
        self.expr("natVal", json!(v))
    }

    pub fn str_(&mut self, s: &str) -> Id {
        self.expr("strVal", json!(s))
    }

    pub fn proj(&mut self, type_name: &str, idx: u64, strukt: Id) -> Id {
        let n = self.name(type_name);
        self.expr("proj", json!({"idx": idx, "struct": strukt, "typeName": n}))
    }

    // ----- expression transforms -------------------------------------------

    /// Rebuild expression `e` bottom-up. `fe(export, id, kind, payload, depth)`
    /// may return a replacement id; `fl(export, level)` maps the levels of
    /// sorts and constants.
    pub fn rebuild(&mut self, e: Id, fe: Option<&mut ExprFn>, fl: Option<&mut LevelFn>) -> Id {
        let mut memo = HashMap::new();
        self.rebuild_at(e, fe, fl, 0, &mut memo)
    }

    fn rebuild_at(
        &mut self,
        e: Id,
        mut fe: Option<&mut ExprFn>,
        mut fl: Option<&mut LevelFn>,
        depth: u64,
        memo: &mut HashMap<(Id, u64), Id>,
    ) -> Id {
        if let Some(&r) = memo.get(&(e, depth)) {
            return r;
        }
        let (k, p) = self.exprs[&e].clone();
        if let Some(f) = fe.as_deref_mut()
            && let Some(r) = f(self, e, &k, &p, depth)
        {
            memo.insert((e, depth), r);
            return r;
        }
        let out = match k.as_str() {
            "sort" => match fl.as_deref_mut() {
                Some(f) => {
                    let l = f(self, id(&p));
                    self.sort(l)
                }
                None => e,
            },
            "const" => match fl.as_deref_mut() {
                Some(f) => {
                    let us: Vec<Id> = p["us"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|u| f(self, id(u)))
                        .collect();
                    self.expr("const", json!({"name": p["name"], "us": us}))
                }
                None => e,
            },
            "bvar" | "natVal" | "strVal" => e,
            _ => {
                let mut q = p.as_object().unwrap().clone();
                for c in EXPR_CHILDREN {
                    if let Some(x) = q.get(c) {
                        let x = id(x);
                        let d = if c == "body" { depth + 1 } else { depth };
                        let y = self.rebuild_at(x, fe.as_deref_mut(), fl.as_deref_mut(), d, memo);
                        q.insert(c.to_string(), json!(y));
                    }
                }
                self.expr(&k, Value::Object(q))
            }
        };
        memo.insert((e, depth), out);
        out
    }

    pub fn map_levels(&mut self, e: Id, fl: &mut LevelFn) -> Id {
        self.rebuild(e, None, Some(fl))
    }

    /// Split `e` into its leading binders of `kind` and the body.
    pub fn binders(&self, mut e: Id, kind: &str) -> (Vec<Binder>, Id) {
        let mut bs = Vec::new();
        while self.exprs[&e].0 == kind {
            let p = &self.exprs[&e].1;
            bs.push((
                id(&p["name"]),
                id(&p["type"]),
                p["binderInfo"].as_str().unwrap().to_string(),
            ));
            e = id(&p["body"]);
        }
        (bs, e)
    }

    pub fn close(&mut self, bs: &[Binder], mut body: Id, kind: &str) -> Id {
        for (n, t, bi) in bs.iter().rev() {
            body = self.expr(
                kind,
                json!({"binderInfo": bi, "body": body, "name": n, "type": t}),
            );
        }
        body
    }

    pub fn app_args(&self, mut e: Id) -> (Id, Vec<Id>) {
        let mut args = Vec::new();
        while self.exprs[&e].0 == "app" {
            let p = &self.exprs[&e].1;
            args.push(id(&p["arg"]));
            e = id(&p["fn"]);
        }
        args.reverse();
        (e, args)
    }

    /// For `ty = ∀ xs, @Eq.{u} T a b` build `fun xs => @Eq.refl.{u} T a`.
    pub fn rfl_proof(&mut self, ty: Id) -> Id {
        let (bs, body) = self.binders(ty, "forallE");
        let (f, args) = self.app_args(body);
        let (fk, fp) = self.exprs[&f].clone();
        assert!(
            fk == "const" && self.name_str(id(&fp["name"])) == "Eq",
            "not an Eq statement"
        );
        let (t, a) = (args[0], args[1]);
        assert_eq!(args.len(), 3, "not an Eq statement");
        let n = self.name("Eq.refl");
        let refl = self.expr("const", json!({"name": n, "us": fp["us"]}));
        let body = self.app(refl, &[t, a]);
        self.close(&bs, body, "lam")
    }

    // ----- declarations ----------------------------------------------------

    /// The index of the record declaring `name`, if any.
    pub fn decl_index(&self, name: &str) -> Option<usize> {
        let n = json!(self.name_id(name)?);
        for (i, r) in self.recs.iter().enumerate() {
            let k = kind_of(r);
            let p = &r[k];
            if matches!(k, "axiom" | "def" | "thm" | "opaque" | "quot") && p["name"] == n {
                return Some(i);
            }
            if k == "inductive" {
                for part in ["types", "ctors", "recs"] {
                    if p[part].as_array().unwrap().iter().any(|x| x["name"] == n) {
                        return Some(i);
                    }
                }
            }
        }
        None
    }

    /// The info of a declaration (a type, ctor or rec for inductives).
    pub fn decl(&mut self, name: &str) -> &mut Map<String, Value> {
        let i = self
            .decl_index(name)
            .unwrap_or_else(|| panic!("no declaration {name}"));
        let n = json!(self.name_id(name).unwrap());
        let r = &mut self.recs[i];
        let k = kind_of(r).to_string();
        let p = r.get_mut(&k).unwrap();
        if k != "inductive" {
            return p.as_object_mut().unwrap();
        }
        for part in ["types", "ctors", "recs"] {
            let has = p[part]
                .as_array()
                .unwrap()
                .iter()
                .position(|x| x["name"] == n);
            if let Some(j) = has {
                return p[part][j].as_object_mut().unwrap();
            }
        }
        unreachable!()
    }

    /// An id field of a declaration's info.
    pub fn decl_id(&mut self, name: &str, field: &str) -> Id {
        id(&self.decl(name)[field])
    }

    pub fn set(&mut self, name: &str, field: &str, v: Value) {
        self.decl(name).insert(field.to_string(), v);
    }

    pub fn add_decl(&mut self, kind: &str, info: Value) {
        let mut m = Map::new();
        m.insert(kind.to_string(), info);
        self.recs.push(Value::Object(m));
    }

    fn names_of(&mut self, lps: &[&str]) -> Vec<Id> {
        lps.iter().map(|u| self.name(u)).collect()
    }

    pub fn add_thm(&mut self, name: &str, ty: Id, value: Id, lps: &[&str]) {
        let all = self.name(name);
        let lps = self.names_of(lps);
        let n = self.name(name);
        self.add_decl(
            "thm",
            json!({"all": [all], "levelParams": lps, "name": n, "type": ty, "value": value}),
        );
    }

    pub fn add_def(&mut self, name: &str, ty: Id, value: Id, lps: &[&str], safety: &str) {
        let all = self.name(name);
        let lps = self.names_of(lps);
        let n = self.name(name);
        self.add_decl(
            "def",
            json!({"all": [all], "hints": "opaque", "levelParams": lps, "name": n,
                   "safety": safety, "type": ty, "value": value}),
        );
    }

    pub fn add_axiom(&mut self, name: &str, ty: Id, lps: &[&str], unsafe_: bool) {
        let lps = self.names_of(lps);
        let n = self.name(name);
        self.add_decl(
            "axiom",
            json!({"isUnsafe": unsafe_, "levelParams": lps, "name": n, "type": ty}),
        );
    }

    /// Removes the declaration `name`; false if there is none.
    pub fn remove_decl(&mut self, name: &str) -> bool {
        match self.decl_index(name) {
            Some(i) => {
                self.recs.remove(i);
                true
            }
            None => false,
        }
    }
}

/// The (space, id) pairs a record refers to.
pub fn deps(r: &Value) -> Vec<(&'static str, Id)> {
    let mut out = Vec::new();
    let k = kind_of(r);
    let p = &r[k];
    let m = r.as_object().unwrap();
    if m.contains_key("in") {
        out.push(("in", id(&p["pre"])));
    } else if m.contains_key("il") {
        match k {
            "succ" => out.push(("il", id(p))),
            "max" | "imax" => {
                out.push(("il", id(&p[0])));
                out.push(("il", id(&p[1])));
            }
            "param" => out.push(("in", id(p))),
            _ => {}
        }
    } else if m.contains_key("ie") {
        match k {
            "sort" => out.push(("il", id(p))),
            "const" => {
                out.push(("in", id(&p["name"])));
                for u in p["us"].as_array().unwrap() {
                    out.push(("il", id(u)));
                }
            }
            "proj" => {
                out.push(("in", id(&p["typeName"])));
                out.push(("ie", id(&p["struct"])));
            }
            "bvar" | "natVal" | "strVal" => {}
            _ => {
                if let Some(n) = p.get("name") {
                    out.push(("in", id(n)));
                }
                for c in EXPR_CHILDREN {
                    if let Some(x) = p.get(c) {
                        out.push(("ie", id(x)));
                    }
                }
            }
        }
    } else {
        let infos: Vec<&Value> = if k != "inductive" {
            vec![p]
        } else {
            ["types", "ctors", "recs"]
                .iter()
                .flat_map(|part| p[*part].as_array().unwrap().iter())
                .collect()
        };
        for x in infos {
            for f in ["name", "induct"] {
                if let Some(n) = x.get(f) {
                    out.push(("in", id(n)));
                }
            }
            for f in ["levelParams", "all", "ctors"] {
                if let Some(ns) = x.get(f).and_then(Value::as_array) {
                    for n in ns {
                        out.push(("in", id(n)));
                    }
                }
            }
            for f in ["type", "value"] {
                if let Some(e) = x.get(f) {
                    out.push(("ie", id(e)));
                }
            }
            if let Some(rules) = x.get("rules").and_then(Value::as_array) {
                for rule in rules {
                    out.push(("in", id(&rule["ctor"])));
                    out.push(("ie", id(&rule["rhs"])));
                }
            }
        }
    }
    out
}
