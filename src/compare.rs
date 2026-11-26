//! Comparing two environments declaration by declaration, for example the
//! one read from an NDJSON export with the one loaded from `.olean` files.
//!
//! Terms are compared structurally by translating each term of the first
//! environment into the second one's arenas: both are hash-consed, so two
//! terms are equal exactly when the translation of one is the id of the
//! other. Like the arenas themselves, the comparison ignores binder names
//! and binder annotations (kernel-irrelevant, and not part of a term's
//! identity in either arena) and `mdata` (which neither reader keeps).

use num_bigint::BigUint;

use crate::env::{Decl, DeclKind, Env, NameList, TermSink, is_lazy};
use crate::expr::{ExprId, ExprNode, LetBinder};
use crate::level::{LevelId, LevelList, LevelNode};
use crate::name::{NameId, NameNode};

/// Builds a lazily read value of `b` in `a`'s arenas by lookup only: a
/// term node `a` does not have makes the result [`IntoEnv::missing`] (the
/// value is then not one of `a`'s terms).
pub(crate) struct IntoEnv<'e, 't> {
    pub a: &'e Env,
    pub b: &'e Env,
    pub missing: bool,
    /// Translates `b`'s terms into `a` (for the shared subterms that
    /// `b`'s lazy values come with).
    pub back: &'t mut Tr<'e>,
}

/// An id no arena has.
const NONE: u32 = u32::MAX - 2;

impl IntoEnv<'_, '_> {
    fn got<T>(&mut self, x: Option<T>, none: T) -> T {
        x.unwrap_or_else(|| {
            self.missing = true;
            none
        })
    }
}

impl TermSink for IntoEnv<'_, '_> {
    fn keeps_shared(&self) -> bool {
        false
    }

    fn shared_name(&mut self, n: NameId) -> NameId {
        self.back.name(n).unwrap_or(NameId(NONE))
    }

    fn shared_expr(&mut self, e: ExprId) -> ExprId {
        let r = self.back.expr(e);
        self.got(r, ExprId(NONE))
    }

    fn name(&mut self, node: NameNode) -> NameId {
        let node = match node {
            NameNode::Str(p, s) => self
                .a
                .names
                .strings
                .find(self.b.names.strings.get(s))
                .map(|s| NameNode::Str(p, s)),
            n => Some(n),
        };
        // Not a failure by itself: binder names are not part of a term's
        // identity. A node that needs the name will not be found.
        node.and_then(|n| self.a.names.find(n))
            .unwrap_or(NameId(NONE))
    }

    fn level(&mut self, node: LevelNode) -> LevelId {
        let r = self.a.levels.find(&node);
        self.got(r, LevelId(NONE))
    }

    fn list(&mut self, levels: &[LevelId]) -> LevelList {
        let r = self.a.levels.find_list(levels);
        self.got(r, LevelList(NONE))
    }

    fn expr(&mut self, node: ExprNode) -> ExprId {
        let node = match node {
            ExprNode::Str(s) => self
                .a
                .names
                .strings
                .find(self.b.names.strings.get(s))
                .map(ExprNode::Str),
            n => Some(n),
        };
        let r = node.and_then(|n| self.a.exprs.find(&n));
        self.got(r, ExprId(NONE))
    }

    fn let_in(&mut self, binder: LetBinder, body: ExprId) -> ExprId {
        let r = self
            .a
            .exprs
            .find_let(&binder)
            .and_then(|h| self.a.exprs.find(&ExprNode::Let(h, body)));
        self.got(r, ExprId(NONE))
    }

    fn nat_big(&mut self, n: BigUint) -> ExprId {
        let r = self
            .a
            .exprs
            .find_big(&n)
            .and_then(|b| self.a.exprs.find(&ExprNode::NatBig(b)));
        self.got(r, ExprId(NONE))
    }
}

const UNKNOWN: u32 = u32::MAX;
const MISSING: u32 = u32::MAX - 1;

/// Translation of ids from environment `a` into environment `b`.
pub(crate) struct Tr<'e> {
    a: &'e Env,
    b: &'e Env,
    names: Vec<u32>,
    levels: Vec<u32>,
    exprs: Vec<u32>,
    stack: Vec<(ExprId, bool)>,
    /// From `b` into `a`, made when first needed.
    back: Option<Box<Tr<'e>>>,
}

impl<'e> Tr<'e> {
    pub(crate) fn new(a: &'e Env, b: &'e Env) -> Self {
        Tr {
            a,
            b,
            names: vec![UNKNOWN; a.names.len()],
            levels: vec![UNKNOWN; a.levels.len()],
            exprs: vec![UNKNOWN; a.exprs.len()],
            stack: Vec::new(),
            back: None,
        }
    }

    fn name(&mut self, n: NameId) -> Option<NameId> {
        let mut chain = Vec::new();
        let mut cur = n;
        let mut base = loop {
            match self.names[cur.index()] {
                MISSING => return None,
                UNKNOWN => {}
                id => break NameId(id),
            }
            match self.a.names.get(cur) {
                NameNode::Anon => break NameId::ANON,
                NameNode::Str(p, _) | NameNode::Num(p, _) => {
                    chain.push(cur);
                    cur = p;
                }
            }
        };
        while let Some(c) = chain.pop() {
            let node = match self.a.names.get(c) {
                NameNode::Str(_, s) => self
                    .b
                    .names
                    .strings
                    .find(self.a.names.strings.get(s))
                    .map(|s| NameNode::Str(base, s)),
                NameNode::Num(_, k) => Some(NameNode::Num(base, k)),
                NameNode::Anon => Some(NameNode::Anon),
            };
            match node.and_then(|n| self.b.names.find(n)) {
                Some(id) => {
                    self.names[c.index()] = id.0;
                    base = id;
                }
                None => {
                    self.names[c.index()] = MISSING;
                    return None;
                }
            }
        }
        Some(base)
    }

    fn level(&mut self, l: LevelId) -> Option<LevelId> {
        match self.levels[l.index()] {
            MISSING => return None,
            UNKNOWN => {}
            id => return Some(LevelId(id)),
        }
        // Levels are shallow: plain recursion is fine.
        let node = match self.a.levels.get(l) {
            LevelNode::Zero => Some(LevelNode::Zero),
            LevelNode::Succ(x) => self.level(x).map(LevelNode::Succ),
            LevelNode::Max(x, y) => self
                .level(x)
                .and_then(|x| Some(LevelNode::Max(x, self.level(y)?))),
            LevelNode::IMax(x, y) => self
                .level(x)
                .and_then(|x| Some(LevelNode::IMax(x, self.level(y)?))),
            LevelNode::Param(n) => self.name(n).map(LevelNode::Param),
        };
        let r = node.and_then(|n| self.b.levels.find(&n));
        self.levels[l.index()] = r.map_or(MISSING, |r| r.0);
        r
    }

    fn done(&self, e: ExprId) -> Option<Option<ExprId>> {
        match self.exprs[e.index()] {
            UNKNOWN => None,
            MISSING => Some(None),
            id => Some(Some(ExprId(id))),
        }
    }

    /// The id in `b` of the term `e` of `a`, if `b` has it.
    fn expr(&mut self, e: ExprId) -> Option<ExprId> {
        self.stack.clear();
        self.stack.push((e, false));
        while let Some(&(x, expanded)) = self.stack.last() {
            if self.done(x).is_some() {
                self.stack.pop();
                continue;
            }
            let node = self.a.exprs.get(x);
            let kids: Vec<ExprId> = match node {
                ExprNode::App(f, a) => vec![f, a],
                ExprNode::Lam(_, _, t, b) | ExprNode::Pi(_, _, t, b) => vec![t, b],
                ExprNode::Let(l, b) => {
                    let l = self.a.exprs.let_binder(l);
                    vec![l.ty, l.value, b]
                }
                ExprNode::Proj(_, _, s) => vec![s],
                _ => vec![],
            };
            if !expanded && kids.iter().any(|&k| self.done(k).is_none()) {
                self.stack.last_mut().expect("nonempty").1 = true;
                for &k in kids.iter().rev() {
                    if self.done(k).is_none() {
                        self.stack.push((k, false));
                    }
                }
                continue;
            }
            self.stack.pop();
            let k = |t: &Self, i: usize| t.done(kids[i]).flatten();
            let tr = match node {
                ExprNode::BVar(i) => Some(ExprNode::BVar(i)),
                ExprNode::FVar(i) => Some(ExprNode::FVar(i)),
                ExprNode::Sort(l) => self.level(l).map(ExprNode::Sort),
                ExprNode::Const(n, ls) => (|| {
                    let n = self.name(n)?;
                    let mut v = Vec::new();
                    for &l in self.a.levels.list(ls) {
                        v.push(self.level(l)?);
                    }
                    Some(ExprNode::Const(n, self.b.levels.find_list(&v)?))
                })(),
                ExprNode::App(..) => (|| Some(ExprNode::App(k(self, 0)?, k(self, 1)?)))(),
                ExprNode::Lam(bi, _, _, _) => {
                    (|| Some(ExprNode::Lam(bi, NameId::ANON, k(self, 0)?, k(self, 1)?)))()
                }
                ExprNode::Pi(bi, _, _, _) => {
                    (|| Some(ExprNode::Pi(bi, NameId::ANON, k(self, 0)?, k(self, 1)?)))()
                }
                ExprNode::Let(l, _) => (|| {
                    let l = self.a.exprs.let_binder(l);
                    let lb = LetBinder {
                        name: NameId::ANON,
                        ty: k(self, 0)?,
                        value: k(self, 1)?,
                        nondep: l.nondep,
                    };
                    Some(ExprNode::Let(self.b.exprs.find_let(&lb)?, k(self, 2)?))
                })(),
                ExprNode::NatSmall(lo, hi) => Some(ExprNode::NatSmall(lo, hi)),
                ExprNode::NatBig(i) => self
                    .b
                    .exprs
                    .find_big(self.a.exprs.big(i))
                    .map(ExprNode::NatBig),
                ExprNode::Str(s) => self
                    .b
                    .names
                    .strings
                    .find(self.a.names.strings.get(s))
                    .map(ExprNode::Str),
                ExprNode::Proj(n, i, _) => {
                    (|| Some(ExprNode::Proj(self.name(n)?, i, k(self, 0)?)))()
                }
            };
            let r = tr.and_then(|n| self.b.exprs.find(&n));
            self.exprs[x.index()] = r.map_or(MISSING, |r| r.0);
        }
        self.done(e).flatten()
    }

    fn names_eq(&mut self, x: NameList, y: NameList) -> bool {
        let (xs, ys) = (self.a.name_list(x), self.b.name_list(y));
        xs.len() == ys.len() && xs.iter().zip(ys).all(|(&p, &q)| self.name(p) == Some(q))
    }

    fn expr_eq(&mut self, x: ExprId, y: ExprId) -> bool {
        self.expr(x) == Some(y)
    }

    /// The first field in which the declarations differ, if any.
    fn decl_diff(&mut self, x: &Decl, y: &Decl) -> Option<&'static str> {
        if !self.names_eq(x.level_params, y.level_params) {
            return Some("level parameters");
        }
        if !self.expr_eq(x.ty, y.ty) {
            return Some("type");
        }
        use DeclKind as K;
        match (x.kind, y.kind) {
            (K::Axiom { is_unsafe: u }, K::Axiom { is_unsafe: v }) => {
                (u != v).then_some("isUnsafe")
            }
            (
                K::Definition {
                    value: value_a,
                    hints: hints_a,
                    safety: safety_a,
                    all: all_a,
                },
                K::Definition {
                    value: value_b,
                    hints: hints_b,
                    safety: safety_b,
                    all: all_b,
                },
            ) => {
                if hints_a != hints_b {
                    Some("hints")
                } else if safety_a != safety_b {
                    Some("safety")
                } else if !self.names_eq(all_a, all_b) {
                    Some("all")
                } else if !self.expr_eq(value_a, value_b) {
                    Some("value")
                } else {
                    None
                }
            }
            (
                K::Theorem {
                    value: value_a,
                    all: all_a,
                },
                K::Theorem {
                    value: value_b,
                    all: all_b,
                },
            ) => {
                if !self.names_eq(all_a, all_b) {
                    Some("all")
                } else if is_lazy(value_b) {
                    let (a, b) = (self.a, self.b);
                    let back = self.back.get_or_insert_with(|| Box::new(Tr::new(b, a)));
                    let mut sink = IntoEnv {
                        a,
                        b,
                        missing: false,
                        back,
                    };
                    match self.b.value_into(y, &mut sink) {
                        Ok(Some(v)) if !sink.missing && v == value_a => None,
                        _ => Some("value"),
                    }
                } else if !self.expr_eq(value_a, value_b) {
                    Some("value")
                } else {
                    None
                }
            }
            (
                K::Opaque {
                    value: value_a,
                    all: all_a,
                    is_unsafe: is_unsafe_a,
                },
                K::Opaque {
                    value: value_b,
                    all: all_b,
                    is_unsafe: is_unsafe_b,
                },
            ) => {
                if is_unsafe_a != is_unsafe_b {
                    Some("isUnsafe")
                } else if !self.names_eq(all_a, all_b) {
                    Some("all")
                } else if !self.expr_eq(value_a, value_b) {
                    Some("value")
                } else {
                    None
                }
            }
            (K::Quot { kind: kind_a }, K::Quot { kind: kind_b }) => {
                (kind_a != kind_b).then_some("kind")
            }
            (
                K::Inductive {
                    num_params: num_params_a,
                    num_indices: num_indices_a,
                    all: all_a,
                    ctors: ctors_a,
                    num_nested: num_nested_a,
                    is_rec: is_rec_a,
                    is_reflexive: is_reflexive_a,
                    is_unsafe: is_unsafe_a,
                },
                K::Inductive {
                    num_params: num_params_b,
                    num_indices: num_indices_b,
                    all: all_b,
                    ctors: ctors_b,
                    num_nested: num_nested_b,
                    is_rec: is_rec_b,
                    is_reflexive: is_reflexive_b,
                    is_unsafe: is_unsafe_b,
                },
            ) => {
                if (
                    num_params_a,
                    num_indices_a,
                    num_nested_a,
                    is_rec_a,
                    is_reflexive_a,
                    is_unsafe_a,
                ) != (
                    num_params_b,
                    num_indices_b,
                    num_nested_b,
                    is_rec_b,
                    is_reflexive_b,
                    is_unsafe_b,
                ) {
                    Some("inductive flags or counts")
                } else if !self.names_eq(all_a, all_b) {
                    Some("all")
                } else if !self.names_eq(ctors_a, ctors_b) {
                    Some("ctors")
                } else {
                    None
                }
            }
            (
                K::Constructor {
                    induct: induct_a,
                    cidx: cidx_a,
                    num_params: num_params_a,
                    num_fields: num_fields_a,
                    is_unsafe: is_unsafe_a,
                },
                K::Constructor {
                    induct: induct_b,
                    cidx: cidx_b,
                    num_params: num_params_b,
                    num_fields: num_fields_b,
                    is_unsafe: is_unsafe_b,
                },
            ) => {
                if (cidx_a, num_params_a, num_fields_a, is_unsafe_a)
                    != (cidx_b, num_params_b, num_fields_b, is_unsafe_b)
                {
                    Some("constructor flags or counts")
                } else if self.name(induct_a) != Some(induct_b) {
                    Some("induct")
                } else {
                    None
                }
            }
            (
                K::Recursor {
                    all: all_a,
                    num_params: num_params_a,
                    num_indices: num_indices_a,
                    num_motives: num_motives_a,
                    num_minors: num_minors_a,
                    rules: rules_a,
                    k: k_a,
                    is_unsafe: is_unsafe_a,
                },
                K::Recursor {
                    all: all_b,
                    num_params: num_params_b,
                    num_indices: num_indices_b,
                    num_motives: num_motives_b,
                    num_minors: num_minors_b,
                    rules: rules_b,
                    k: k_b,
                    is_unsafe: is_unsafe_b,
                },
            ) => {
                if (
                    num_params_a,
                    num_indices_a,
                    num_motives_a,
                    num_minors_a,
                    k_a,
                    is_unsafe_a,
                ) != (
                    num_params_b,
                    num_indices_b,
                    num_motives_b,
                    num_minors_b,
                    k_b,
                    is_unsafe_b,
                ) {
                    return Some("recursor flags or counts");
                }
                if !self.names_eq(all_a, all_b) {
                    return Some("all");
                }
                let (x, y) = (self.a.rec_rules(rules_a), self.b.rec_rules(rules_b));
                if x.len() != y.len() {
                    return Some("rules");
                }
                for (p, q) in x.iter().zip(y) {
                    if p.nfields != q.nfields || self.name(p.ctor) != Some(q.ctor) {
                        return Some("rules");
                    }
                    if !self.expr_eq(p.rhs, q.rhs) {
                        return Some("rule right-hand side");
                    }
                }
                None
            }
            _ => Some("kind"),
        }
    }
}

/// The result of [`compare`].
#[derive(Debug, Default)]
pub struct Diff {
    /// Declarations in both environments.
    pub common: usize,
    /// Names of declarations only in the first environment.
    pub only_a: Vec<String>,
    /// Declarations only in the second, with a category: `unsafe`,
    /// `partial`, `internal` (a name component starting with `_`) or
    /// `other`.
    pub only_b: Vec<(String, &'static str)>,
    /// Declarations in both that differ, with the first differing field.
    pub differ: Vec<(String, &'static str)>,
    /// Theorems that several modules of `b` declare with different proofs,
    /// where `a` has a later copy than the one `b` finds by name (`b`
    /// holds and checks every copy).
    pub later_copy: Vec<String>,
}

impl Diff {
    /// Whether every declaration of the first environment is in the second
    /// and identical there.
    pub fn a_matches(&self) -> bool {
        self.only_a.is_empty() && self.differ.is_empty()
    }
}

fn category(env: &Env, d: &Decl) -> &'static str {
    use crate::env::Safety;
    let is_unsafe = match d.kind {
        DeclKind::Axiom { is_unsafe }
        | DeclKind::Opaque { is_unsafe, .. }
        | DeclKind::Inductive { is_unsafe, .. }
        | DeclKind::Constructor { is_unsafe, .. }
        | DeclKind::Recursor { is_unsafe, .. } => is_unsafe,
        DeclKind::Definition { safety, .. } => safety == Safety::Unsafe,
        _ => false,
    };
    if is_unsafe {
        return "unsafe";
    }
    if let DeclKind::Definition {
        safety: Safety::Partial,
        ..
    } = d.kind
    {
        return "partial";
    }
    let mut n = d.name;
    loop {
        match env.names.get(n) {
            NameNode::Anon => break,
            NameNode::Str(p, s) => {
                if env.names.strings.get(s).starts_with('_') {
                    return "internal";
                }
                n = p;
            }
            NameNode::Num(p, _) => n = p,
        }
    }
    "other"
}

/// Compare the declarations of `a` with those of `b`, by name.
pub fn compare(a: &Env, b: &Env) -> Diff {
    let mut tr = Tr::new(a, b);
    let mut diff = Diff::default();
    let mut found = vec![false; b.decls.len()];
    // Later copies of a theorem that `b` holds besides the one found by
    // name (see `olean::build`), by name.
    let mut shadows: hashbrown::HashMap<NameId, Vec<usize>> = hashbrown::HashMap::new();
    for (j, d) in b.decls.iter().enumerate() {
        if b.by_name.get(&d.name) != Some(j as u32) {
            shadows.entry(d.name).or_default().push(j);
            found[j] = true;
        }
    }
    for d in &a.decls {
        let Some((n, j)) = tr.name(d.name).and_then(|n| Some((n, b.by_name.get(&n)?))) else {
            diff.only_a.push(a.names.display(d.name).to_string());
            continue;
        };
        found[j as usize] = true;
        diff.common += 1;
        if let Some(f) = tr.decl_diff(d, &b.decls[j as usize]) {
            let copies = shadows.get(&n).map_or(&[][..], |v| v.as_slice());
            if copies
                .iter()
                .any(|&k| tr.decl_diff(d, &b.decls[k]).is_none())
            {
                diff.later_copy.push(a.names.display(d.name).to_string());
            } else {
                diff.differ.push((a.names.display(d.name).to_string(), f));
            }
        }
    }
    for (j, d) in b.decls.iter().enumerate() {
        if !found[j] {
            diff.only_b
                .push((b.names.display(d.name).to_string(), category(b, d)));
        }
    }
    diff
}
