//! Structural fingerprints of declarations, used to decide whether the
//! environment's `Nat.add` (and the other operations with built-in
//! arithmetic) are the prelude's.
//!
//! The fingerprint of a declaration is a SHA-256 digest of its kind, name,
//! universe parameters, type and (for definitions) value and of the
//! structural fields of inductive types, constructors and recursors.
//! Binder names and binder annotations are left out: they do not change
//! what a term means. Constants are referred to by name, so a fingerprint
//! covers one declaration; [`Checker::matches`] then requires every
//! declaration that an operation depends on to match the table taken from
//! the prelude of one Lean version (`fingerprint_table.rs`, written by
//! `examples/fingerprints.rs` from the preludes of the versions it lists). Theorems contribute their statement only,
//! and their proofs are not followed: by proof irrelevance any proof of
//! the same statement does as well.

use std::cell::RefCell;

use sha2::{Digest, Sha256};

use crate::env::{Decl, DeclKind, Env, Hints, QuotKind, Safety};
use crate::expr::{BinderInfo, ExprId, ExprNode};
use crate::level::{LevelId, LevelNode};
use crate::name::{NameId, NameNode};

use super::fingerprint_table::{TABLE, VERSIONS};
use super::store::IdMap;

pub type Digest32 = [u8; 32];

pub struct Checker<'e> {
    env: &'e Env,
    declarations: &'e [Decl],
    exprs: RefCell<IdMap<ExprId, Digest32>>,
    decls: RefCell<IdMap<NameId, Result<u32, String>>>,
}

fn h(parts: &[&[u8]]) -> Digest32 {
    let mut s = Sha256::new();
    for p in parts {
        s.update((p.len() as u64).to_le_bytes());
        s.update(p);
    }
    s.finalize().into()
}

impl<'e> Checker<'e> {
    pub fn new(env: &'e Env) -> Self {
        Self::with_decls(env, &env.decls)
    }

    pub(super) fn with_decls(env: &'e Env, declarations: &'e [Decl]) -> Self {
        Checker {
            env,
            declarations,
            exprs: RefCell::new(IdMap::default()),
            decls: RefCell::new(IdMap::default()),
        }
    }

    pub fn name_str(&self, n: NameId) -> String {
        let mut parts: Vec<String> = Vec::new();
        let mut cur = n;
        loop {
            match self.env.names.get(cur) {
                NameNode::Anon => break,
                NameNode::Str(p, s) => {
                    parts.push(format!("s{}", self.env.names.strings.get(s)));
                    cur = p;
                }
                NameNode::Num(p, k) => {
                    parts.push(format!("n{k}"));
                    cur = p;
                }
            }
        }
        parts.reverse();
        parts.join("\u{0}")
    }

    fn level(&self, l: LevelId, out: &mut Vec<u8>) {
        match self.env.levels.get(l) {
            LevelNode::Zero => out.push(0),
            LevelNode::Succ(a) => {
                out.push(1);
                self.level(a, out)
            }
            LevelNode::Max(a, b) => {
                out.push(2);
                self.level(a, out);
                self.level(b, out)
            }
            LevelNode::IMax(a, b) => {
                out.push(3);
                self.level(a, out);
                self.level(b, out)
            }
            LevelNode::Param(n) => {
                out.push(4);
                let s = self.name_str(n);
                out.extend_from_slice(&(s.len() as u64).to_le_bytes());
                out.extend_from_slice(s.as_bytes());
            }
        }
    }

    pub fn expr(&self, e: ExprId) -> Digest32 {
        if let Some(d) = self.exprs.borrow().get(&e) {
            return *d;
        }
        let d = match self.env.exprs.get(e) {
            ExprNode::BVar(i) => h(&[b"bvar", &i.to_le_bytes()]),
            ExprNode::FVar(i) => h(&[b"fvar", &i.to_le_bytes()]),
            ExprNode::Sort(l) => {
                let mut v = Vec::new();
                self.level(l, &mut v);
                h(&[b"sort", &v])
            }
            ExprNode::Const(n, ls) => {
                let mut v = Vec::new();
                for &l in self.env.levels.list(ls) {
                    self.level(l, &mut v);
                    v.push(0xff);
                }
                h(&[b"const", self.name_str(n).as_bytes(), &v])
            }
            ExprNode::App(f, a) => h(&[b"app", &self.expr(f), &self.expr(a)]),
            ExprNode::Lam(_, _, t, b) => h(&[b"lam", &self.expr(t), &self.expr(b)]),
            ExprNode::Pi(_, _, t, b) => h(&[b"pi", &self.expr(t), &self.expr(b)]),
            ExprNode::Let(l, b) => {
                let lb = self.env.exprs.let_binder(l);
                h(&[
                    b"let",
                    &self.expr(lb.ty),
                    &self.expr(lb.value),
                    &self.expr(b),
                ])
            }
            ExprNode::NatSmall(lo, hi) => {
                h(&[b"nat", &((hi as u64) << 32 | lo as u64).to_le_bytes()])
            }
            ExprNode::NatBig(b) => h(&[b"nat", &self.env.exprs.big(b).to_bytes_le()]),
            ExprNode::Str(s) => h(&[b"str", self.env.names.strings.get(s).as_bytes()]),
            ExprNode::Proj(s, i, x) => h(&[
                b"proj",
                self.name_str(s).as_bytes(),
                &i.to_le_bytes(),
                &self.expr(x),
            ]),
        };
        let _ = BinderInfo::Default;
        self.exprs.borrow_mut().insert(e, d);
        d
    }

    fn names(&self, ns: &[NameId]) -> Vec<u8> {
        let mut v = Vec::new();
        for &n in ns {
            let s = self.name_str(n);
            v.extend_from_slice(&(s.len() as u64).to_le_bytes());
            v.extend_from_slice(s.as_bytes());
        }
        v
    }

    /// The fingerprint of `d`.
    pub fn decl(&self, d: &Decl) -> Digest32 {
        let name = self.name_str(d.name);
        let lps = self.names(self.env.name_list(d.level_params));
        let ty = self.expr(d.ty);
        let u = |x: u32| x.to_le_bytes();
        let b = |x: bool| [x as u8];
        match d.kind {
            DeclKind::Axiom { is_unsafe } => {
                h(&[b"axiom", name.as_bytes(), &lps, &ty, &b(is_unsafe)])
            }
            DeclKind::Definition {
                value,
                hints,
                safety,
                ..
            } => {
                let hs = match hints {
                    Hints::Opaque => [0, 0, 0, 0, 0],
                    Hints::Abbrev => [1, 0, 0, 0, 0],
                    Hints::Regular(k) => {
                        let k = k.to_le_bytes();
                        [2, k[0], k[1], k[2], k[3]]
                    }
                };
                let sf = [match safety {
                    Safety::Unsafe => 0,
                    Safety::Safe => 1,
                    Safety::Partial => 2,
                }];
                h(&[
                    b"def",
                    name.as_bytes(),
                    &lps,
                    &ty,
                    &self.expr(value),
                    &hs,
                    &sf,
                ])
            }
            DeclKind::Theorem { .. } => h(&[b"thm", name.as_bytes(), &lps, &ty]),
            DeclKind::Opaque { is_unsafe, .. } => {
                h(&[b"opaque", name.as_bytes(), &lps, &ty, &b(is_unsafe)])
            }
            DeclKind::Quot { kind } => {
                let k = [match kind {
                    QuotKind::Type => 0,
                    QuotKind::Ctor => 1,
                    QuotKind::Lift => 2,
                    QuotKind::Ind => 3,
                }];
                h(&[b"quot", name.as_bytes(), &lps, &ty, &k])
            }
            DeclKind::Inductive {
                num_params,
                num_indices,
                all,
                ctors,
                num_nested,
                is_rec,
                is_reflexive,
                is_unsafe,
            } => h(&[
                b"ind",
                name.as_bytes(),
                &lps,
                &ty,
                &u(num_params),
                &u(num_indices),
                &self.names(self.env.name_list(all)),
                &self.names(self.env.name_list(ctors)),
                &u(num_nested),
                &b(is_rec),
                &b(is_reflexive),
                &b(is_unsafe),
            ]),
            DeclKind::Constructor {
                induct,
                cidx,
                num_params,
                num_fields,
                is_unsafe,
            } => h(&[
                b"ctor",
                name.as_bytes(),
                &lps,
                &ty,
                self.name_str(induct).as_bytes(),
                &u(cidx),
                &u(num_params),
                &u(num_fields),
                &b(is_unsafe),
            ]),
            DeclKind::Recursor {
                all,
                num_params,
                num_indices,
                num_motives,
                num_minors,
                rules,
                k,
                is_unsafe,
            } => {
                let mut rs = Vec::new();
                for r in self.env.rec_rules(rules) {
                    rs.extend_from_slice(self.name_str(r.ctor).as_bytes());
                    rs.push(0);
                    rs.extend_from_slice(&r.nfields.to_le_bytes());
                    rs.extend_from_slice(&self.expr(r.rhs));
                }
                h(&[
                    b"rec",
                    name.as_bytes(),
                    &lps,
                    &ty,
                    &self.names(self.env.name_list(all)),
                    &u(num_params),
                    &u(num_indices),
                    &u(num_motives),
                    &u(num_minors),
                    &rs,
                    &b(k),
                    &b(is_unsafe),
                ])
            }
        }
    }

    /// The declarations `d` refers to, as the cone walk follows them.
    pub fn deps(&self, d: &Decl, out: &mut Vec<NameId>) {
        let mut roots = vec![d.ty];
        match d.kind {
            DeclKind::Definition { value, .. } => roots.push(value),
            DeclKind::Inductive { ctors, .. } => out.extend_from_slice(self.env.name_list(ctors)),
            DeclKind::Constructor { induct, .. } => out.push(induct),
            DeclKind::Recursor { all, rules, .. } => {
                out.extend_from_slice(self.env.name_list(all));
                roots.extend(self.env.rec_rules(rules).iter().map(|r| r.rhs));
            }
            _ => {}
        }
        let mut seen = IdMap::<ExprId, ()>::default();
        while let Some(e) = roots.pop() {
            if seen.insert(e, ()).is_some() {
                continue;
            }
            match self.env.exprs.get(e) {
                ExprNode::Const(n, _) => out.push(n),
                ExprNode::App(f, a) => roots.extend([f, a]),
                ExprNode::Lam(_, _, t, b) | ExprNode::Pi(_, _, t, b) => roots.extend([t, b]),
                ExprNode::Let(l, b) => {
                    let lb = self.env.exprs.let_binder(l);
                    roots.extend([lb.ty, lb.value, b]);
                }
                ExprNode::Proj(s, _, x) => {
                    out.push(s);
                    roots.push(x);
                }
                _ => {}
            }
        }
    }

    /// Ok if `n` and everything it depends on match the table, all for the
    /// same Lean version: the versions they all match, as a mask over
    /// `VERSIONS`.
    pub fn matches(&self, n: NameId) -> Result<u32, String> {
        let mut stack = vec![n];
        let mut seen = IdMap::<NameId, ()>::default();
        let mut deps = Vec::new();
        let mut common = u32::MAX;
        while let Some(m) = stack.pop() {
            if seen.insert(m, ()).is_some() {
                continue;
            }
            let cached = self.decls.borrow().get(&m).cloned();
            let r = match cached {
                Some(r) => r,
                None => {
                    let r = self.match_decl(m);
                    self.decls.borrow_mut().insert(m, r.clone());
                    r
                }
            };
            let mask = r?;
            common &= mask;
            if common == 0 {
                return Err(format!(
                    "its declarations are not all from one Lean version (`{}` is from {})",
                    display(&key(self, m)),
                    versions(mask)
                ));
            }
            let d = self
                .env
                .by_name
                .get(&m)
                .map(|i| &self.declarations[i as usize])
                .expect("matched");
            deps.clear();
            self.deps(d, &mut deps);
            stack.extend_from_slice(&deps);
        }
        Ok(common)
    }

    /// The versions whose table has `m` as it is declared here.
    fn match_decl(&self, m: NameId) -> Result<u32, String> {
        let shown = key(self, m);
        let Some(d) = self
            .env
            .by_name
            .get(&m)
            .map(|i| &self.declarations[i as usize])
        else {
            return Err(format!(
                "depends on `{}`, which is not declared",
                display(&shown)
            ));
        };
        let lo = TABLE.partition_point(|(k, _, _)| *k < shown.as_str());
        let rows = TABLE[lo..]
            .iter()
            .take_while(|(k, _, _)| *k == shown.as_str());
        let mut known = false;
        let mut mask = 0;
        let digest = hex(&self.decl(d));
        for (_, v, vs) in rows {
            known = true;
            if *v == digest {
                mask |= vs;
            }
        }
        match (known, mask) {
            (false, _) => Err(format!(
                "depends on `{}`, which the prelude's does not",
                display(&shown)
            )),
            (true, 0) => Err(format!(
                "`{}` is not the expected declaration",
                display(&shown)
            )),
            (true, m) => Ok(m),
        }
    }
}

/// The mask over `VERSIONS` of the versions named in `vs`.
pub fn version_mask(vs: &[&str]) -> u32 {
    VERSIONS
        .iter()
        .enumerate()
        .filter(|(_, v)| vs.contains(v))
        .fold(0, |m, (i, _)| m | 1 << i)
}

fn versions(mask: u32) -> String {
    VERSIONS
        .iter()
        .enumerate()
        .filter(|(i, _)| mask & (1 << i) != 0)
        .map(|(_, v)| *v)
        .collect::<Vec<_>>()
        .join(", ")
}

/// The key a name has in the table.
pub fn key(c: &Checker<'_>, n: NameId) -> String {
    c.name_str(n).replace('\u{0}', ".")
}

fn display(key: &str) -> String {
    key.split('.')
        .map(|c| c.get(1..).unwrap_or(""))
        .collect::<Vec<_>>()
        .join(".")
}

pub fn hex(d: &Digest32) -> String {
    d.iter().map(|b| format!("{b:02x}")).collect()
}
