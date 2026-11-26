//! The type checker: type inference, weak head normalization and
//! definitional equality. This follows `type_checker.cpp` of Lean's kernel
//! (v4.36.0) closely, function by function, so the two can be read side by
//! side; departures are marked. The arrangement of the caches and the
//! lazy delta loop also matches nanoda_lib's `tc.rs` and lean4lean's
//! `TypeChecker.lean`, which follow the same C++ code.
//!
//! Free variables are indices into `lctx`, which only grows while a
//! declaration is checked: an fvar is never reused, so cached results that
//! mention one stay valid for the whole declaration.

use num_bigint::BigUint;

use crate::env::{Decl, DeclKind, Hints, Safety};
use crate::expr::{BinderInfo, ExprId, ExprNode};
use crate::level::{LevelId, LevelList};
use crate::name::NameId;

use super::ext::{Ext, NatOp, SMALL_NAT, SmallNat};
use super::store::{IdMap, IdSet, Store};
use super::univ;

/// A kernel error: the declaration being checked is rejected.
#[derive(Debug, Clone)]
pub struct KErr(pub Box<String>);

impl KErr {
    /// Boxed, so that a result of the checker fits in two registers.
    pub fn new(msg: String) -> Self {
        KErr(Box::new(msg))
    }
}

pub type R<T> = Result<T, KErr>;

pub fn err<T>(msg: impl Into<String>) -> R<T> {
    Err(KErr::new(msg.into()))
}

#[derive(Clone, Copy, Debug)]
pub struct LocalDecl {
    pub name: NameId,
    pub ty: ExprId,
    pub val: Option<ExprId>,
    pub bi: BinderInfo,
}

/// Lean's `definition_safety`, for the declaration being checked.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Mode {
    Safe,
    Unsafe,
    Partial,
}

/// Bound on the byte size of `Nat` literals the kernel computes or accepts
/// (Lean's `LEAN_NAT_MAX_SIZE` default).
pub const NAT_MAX_BYTES: u64 = 128 * 1024 * 1024;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Step {
    Continue,
    Unknown,
    Equal,
    Diff,
}

pub struct Tc<'e> {
    pub st: Store<'e>,
    pub ext: &'e Ext,
    pub lctx: Vec<LocalDecl>,
    /// Universe parameters in scope; `None` skips the check.
    pub lparams: Option<Vec<NameId>>,
    pub mode: Mode,
    eager: bool,
    /// Only declarations before this index of `env.decls` are visible ...
    pub limit: u32,
    /// ... and these (an unsafe or partial mutual group) ...
    pub extra: Vec<NameId>,
    /// ... and these, declared by the inductive block being checked.
    pub pending: IdMap<NameId, Decl>,
    infer_cache: [IdMap<ExprId, ExprId>; 2],
    whnf_core_cache: IdMap<ExprId, ExprId>,
    whnf_cache: IdMap<ExprId, ExprId>,
    unfold_cache: IdMap<ExprId, ExprId>,
    /// Values read lazily from `.olean` files, built in the store.
    values: IdMap<ExprId, ExprId>,
    eq_ok: IdSet<(ExprId, ExprId)>,
    eq_fail: IdSet<(ExprId, ExprId)>,
    level_eq: IdMap<(LevelId, LevelId), bool>,
    major_induct: IdMap<NameId, NameId>,
    /// The closed-term evaluator's state (`eval/`); `None` while it runs.
    pub(super) eval: Option<Box<super::eval::State>>,
}

fn pair(a: ExprId, b: ExprId) -> (ExprId, ExprId) {
    if a <= b { (a, b) } else { (b, a) }
}

impl<'e> Tc<'e> {
    pub fn new(st: Store<'e>, ext: &'e Ext, limit: u32) -> Self {
        Tc {
            st,
            ext,
            lctx: Vec::new(),
            lparams: None,
            mode: Mode::Safe,
            eager: false,
            limit,
            extra: Vec::new(),
            pending: IdMap::default(),
            infer_cache: [IdMap::default(), IdMap::default()],
            whnf_core_cache: IdMap::default(),
            whnf_cache: IdMap::default(),
            unfold_cache: IdMap::default(),
            values: IdMap::default(),
            eq_ok: IdSet::default(),
            eq_fail: IdSet::default(),
            level_eq: IdMap::default(),
            major_induct: IdMap::default(),
            eval: Some(Box::default()),
        }
    }

    /// Forget everything about the previous declaration.
    pub fn reset(&mut self, limit: u32) {
        self.st.clear();
        self.lctx.clear();
        self.lparams = None;
        self.mode = Mode::Safe;
        self.eager = false;
        self.limit = limit;
        self.extra.clear();
        self.pending.clear();
        for c in &mut self.infer_cache {
            *c = IdMap::default();
        }
        self.whnf_core_cache = IdMap::default();
        self.whnf_cache = IdMap::default();
        self.unfold_cache = IdMap::default();
        self.values = IdMap::default();
        self.eq_ok = IdSet::default();
        self.eq_fail = IdSet::default();
        self.level_eq = IdMap::default();
        self.major_induct = IdMap::default();
        self.eval = Some(Box::default());
    }

    /// Drop the caches (but not the store or the context), as after the
    /// environment changed under them.
    pub fn clear_caches(&mut self) {
        for c in &mut self.infer_cache {
            c.clear();
        }
        self.whnf_core_cache.clear();
        self.whnf_cache.clear();
        self.unfold_cache.clear();
        self.eq_ok.clear();
        self.eq_fail.clear();
        self.eval = Some(Box::default());
    }

    // ---- environment ----

    /// The declaration named `n`, if it is visible from the one being checked.
    pub fn find(&self, n: NameId) -> Option<Decl> {
        if !self.pending.is_empty()
            && let Some(d) = self.pending.get(&n)
        {
            return Some(*d);
        }
        let env = self.st.env;
        let &i = env.by_name.get(&n)?;
        if i < self.limit || self.extra.contains(&n) {
            Some(self.st.decls[i as usize])
        } else {
            None
        }
    }

    pub fn get(&self, n: NameId) -> R<Decl> {
        match self.find(n) {
            Some(d) => Ok(d),
            None => err(format!("unknown constant '{}'", self.st.show(n))),
        }
    }

    pub fn show(&self, n: NameId) -> String {
        self.st.show(n)
    }

    pub fn pp(&self, e: ExprId) -> String {
        super::pp::pp(&self.st, &self.lctx, e)
    }

    // ---- local context ----

    pub fn push_local(
        &mut self,
        name: NameId,
        ty: ExprId,
        val: Option<ExprId>,
        bi: BinderInfo,
    ) -> ExprId {
        let i = self.lctx.len() as u32;
        self.lctx.push(LocalDecl { name, ty, val, bi });
        self.st.fvar(i)
    }

    pub fn fvar_decl(&self, e: ExprId) -> Option<LocalDecl> {
        match self.st.node(e) {
            ExprNode::FVar(i) => self.lctx.get(i as usize).copied(),
            _ => None,
        }
    }

    /// Bind `fvars` (in order) around `body`: `Π` for assumptions, `let` for
    /// definitions that `body` uses (dead ones are dropped, as Lean does
    /// for `infer_let`).
    pub fn mk_binding(&mut self, lam: bool, fvars: &[ExprId], body: ExprId) -> ExprId {
        let mut r = self.st.abstract_fvars(body, fvars);
        for i in (0..fvars.len()).rev() {
            let d = self.fvar_decl(fvars[i]).expect("fvar");
            let ty = self.st.abstract_fvars(d.ty, &fvars[..i]);
            r = match d.val {
                Some(v) => {
                    if self.st.has_loose_bvar(r, 0) {
                        let v = self.st.abstract_fvars(v, &fvars[..i]);
                        self.st.mk_let(d.name, ty, v, r)
                    } else {
                        self.st.lower_loose(r, 0, 1)
                    }
                }
                None if lam => self.st.lam(d.bi, d.name, ty, r),
                None => self.st.pi(d.bi, d.name, ty, r),
            };
        }
        r
    }

    pub fn mk_pi(&mut self, fvars: &[ExprId], body: ExprId) -> ExprId {
        self.mk_binding(false, fvars, body)
    }

    pub fn mk_lambda(&mut self, fvars: &[ExprId], body: ExprId) -> ExprId {
        self.mk_binding(true, fvars, body)
    }

    // ---- small helpers ----

    fn decl_value(d: &Decl) -> Option<ExprId> {
        match d.kind {
            DeclKind::Definition { value, .. } | DeclKind::Theorem { value, .. } => Some(value),
            _ => None,
        }
    }

    /// The value of a definition, theorem or opaque `d` (`None` for other
    /// kinds), as a term of the store: a value left in its `.olean` file
    /// is built in the store on first use (see [`Env::value_into`]).
    pub fn value(&mut self, d: &Decl) -> Result<Option<ExprId>, String> {
        let v = match d.kind {
            DeclKind::Definition { value, .. }
            | DeclKind::Theorem { value, .. }
            | DeclKind::Opaque { value, .. } => value,
            _ => return Ok(None),
        };
        if !crate::env::is_lazy(v) {
            return Ok(Some(v));
        }
        if let Some(&e) = self.values.get(&v) {
            return Ok(Some(e));
        }
        let env = self.st.env;
        let e = env.value_into_store(d, &mut self.st)?;
        if let Some(e) = e {
            self.values.insert(v, e);
        }
        Ok(e)
    }

    /// [`Tc::value`] where a malformed file is a bug of the loader.
    fn unfold_value(&mut self, d: &Decl) -> Option<ExprId> {
        Self::decl_value(d)?;
        self.value(d).unwrap_or_else(|e| panic!("{e}"))
    }

    fn decl_hints(d: &Decl) -> Hints {
        match d.kind {
            DeclKind::Definition { hints, .. } => hints,
            _ => Hints::Opaque,
        }
    }

    pub fn decl_is_unsafe(d: &Decl) -> bool {
        match d.kind {
            DeclKind::Axiom { is_unsafe }
            | DeclKind::Opaque { is_unsafe, .. }
            | DeclKind::Inductive { is_unsafe, .. }
            | DeclKind::Constructor { is_unsafe, .. }
            | DeclKind::Recursor { is_unsafe, .. } => is_unsafe,
            DeclKind::Definition { safety, .. } => safety == Safety::Unsafe,
            DeclKind::Theorem { .. } | DeclKind::Quot { .. } => false,
        }
    }

    /// `d`'s type with its universe parameters replaced by `ls`.
    pub fn instantiate_type(&mut self, d: &Decl, ls: LevelList) -> ExprId {
        let ps: Vec<NameId> = self.st.lparams(d).to_vec();
        let ls: Vec<LevelId> = self.st.list(ls).to_vec();
        self.st.instantiate_lparams(d.ty, &ps, &ls)
    }

    pub fn sort_level(&self, e: ExprId) -> Option<LevelId> {
        match self.st.node(e) {
            ExprNode::Sort(l) => Some(l),
            _ => None,
        }
    }

    fn check_level(&self, l: LevelId) -> R<()> {
        if let Some(ps) = &self.lparams
            && let Some(p) = univ::undefined_param(&self.st, l, ps)
        {
            return err(format!(
                "invalid reference to undefined universe level parameter '{}'",
                self.show(p)
            ));
        }
        Ok(())
    }

    // ---- inference ----

    pub fn ensure_sort(&mut self, e: ExprId) -> R<ExprId> {
        if self.sort_level(e).is_some() {
            return Ok(e);
        }
        let w = self.whnf(e)?;
        if self.sort_level(w).is_some() {
            Ok(w)
        } else {
            err(format!("type expected, got {}", self.pp(e)))
        }
    }

    pub fn ensure_pi(&mut self, e: ExprId) -> R<ExprId> {
        if matches!(self.st.node(e), ExprNode::Pi(..)) {
            return Ok(e);
        }
        let w = self.whnf(e)?;
        if matches!(self.st.node(w), ExprNode::Pi(..)) {
            Ok(w)
        } else {
            err(format!("function expected, got {}", self.pp(e)))
        }
    }

    /// The sort of the type `e`, checking that it is a type.
    pub fn ensure_type(&mut self, e: ExprId) -> R<LevelId> {
        let t = self.infer(e)?;
        let s = self.ensure_sort(t)?;
        Ok(self.sort_level(s).unwrap())
    }

    /// Infer the type of `e` without checking it.
    pub fn infer(&mut self, e: ExprId) -> R<ExprId> {
        self.infer_core(e, true)
    }

    /// Infer the type of `e`, checking it, with universe parameters `ps`.
    pub fn check(&mut self, e: ExprId, ps: &[NameId]) -> R<ExprId> {
        let saved = self.lparams.replace(ps.to_vec());
        let r = self.infer_core(e, false);
        self.lparams = saved;
        r
    }

    pub fn infer_core(&mut self, e: ExprId, infer_only: bool) -> R<ExprId> {
        if self.st.has_loose_bvars(e) {
            return err("type checker does not support loose bound variables");
        }
        if let Some(&r) = self.infer_cache[infer_only as usize].get(&e) {
            return Ok(r);
        }
        let r = match self.st.node(e) {
            ExprNode::BVar(_) => unreachable!(),
            ExprNode::FVar(i) => match self.lctx.get(i as usize) {
                Some(d) => d.ty,
                None => return err("unknown free variable"),
            },
            ExprNode::Sort(l) => {
                if !infer_only {
                    self.check_level(l)?;
                }
                let l = self.st.succ(l);
                self.st.sort(l)
            }
            ExprNode::Const(n, ls) => self.infer_constant(n, ls, infer_only)?,
            ExprNode::Lam(..) => self.infer_lambda(e, infer_only)?,
            ExprNode::Pi(..) => self.infer_pi(e, infer_only)?,
            ExprNode::App(..) => self.infer_app(e, infer_only)?,
            ExprNode::Let(..) => self.infer_let(e, infer_only)?,
            ExprNode::NatSmall(..) => self.nat_type()?,
            ExprNode::NatBig(b) => {
                if self.st.big(b).bits().div_ceil(8) > NAT_MAX_BYTES {
                    return err(
                        "the kernel refused a `Nat` numeral because its size exceeds the maximum",
                    );
                }
                self.nat_type()?
            }
            ExprNode::Str(_) => self.string_type()?,
            ExprNode::Proj(s, i, x) => self.infer_proj(e, s, i, x, infer_only)?,
        };
        self.infer_cache[infer_only as usize].insert(e, r);
        Ok(r)
    }

    /// `Nat`, if literals are available (see `ext.rs`).
    fn nat_type(&mut self) -> R<ExprId> {
        match self.ext.nat {
            Some(n) if self.find(n).is_some() => Ok(self.st.cnst(n, LevelList::EMPTY)),
            _ => err(
                "a `Nat` literal needs the prelude's `Nat` (absent or not the expected inductive type)",
            ),
        }
    }

    fn string_type(&mut self) -> R<ExprId> {
        match self.ext.string() {
            Some(s) if self.find(s.string).is_some() && self.find(s.of_list).is_some() => {
                Ok(self.st.cnst(s.string, LevelList::EMPTY))
            }
            _ => err(
                "a `String` literal needs the prelude's `String`, `String.ofList`, `Char.ofNat` and `List` (absent or not the expected declarations)",
            ),
        }
    }

    fn infer_constant(&mut self, n: NameId, ls: LevelList, infer_only: bool) -> R<ExprId> {
        let d = self.get(n)?;
        let nps = d.level_params.len();
        let nls = self.st.list(ls).len();
        if nps != nls {
            return err(format!(
                "incorrect number of universe levels parameters for '{}', #{nps} expected, #{nls} provided",
                self.show(n)
            ));
        }
        if !infer_only {
            if Self::decl_is_unsafe(&d) && self.mode != Mode::Unsafe {
                return err(format!(
                    "invalid declaration, it uses unsafe declaration '{}'",
                    self.show(n)
                ));
            }
            if let DeclKind::Definition {
                safety: Safety::Partial,
                ..
            } = d.kind
                && self.mode == Mode::Safe
            {
                return err(format!(
                    "invalid declaration, safe declaration must not contain partial declaration '{}'",
                    self.show(n)
                ));
            }
            for i in 0..nls {
                let l = self.st.list(ls)[i];
                self.check_level(l)?;
            }
        }
        Ok(self.instantiate_type(&d, ls))
    }

    fn infer_lambda(&mut self, mut e: ExprId, infer_only: bool) -> R<ExprId> {
        let mut fvars = Vec::new();
        while let ExprNode::Lam(bi, n, t, b) = self.st.node(e) {
            let d = self.st.instantiate_rev(t, &fvars);
            if !infer_only {
                let s = self.infer_core(d, infer_only)?;
                self.ensure_sort(s)?;
            }
            let fv = self.push_local(n, d, None, bi);
            fvars.push(fv);
            e = b;
        }
        let body = self.st.instantiate_rev(e, &fvars);
        let r = self.infer_core(body, infer_only)?;
        let r = self.cheap_beta_reduce(r);
        Ok(self.mk_pi(&fvars, r))
    }

    fn infer_pi(&mut self, mut e: ExprId, infer_only: bool) -> R<ExprId> {
        let mut fvars = Vec::new();
        let mut us = Vec::new();
        while let ExprNode::Pi(bi, n, t, b) = self.st.node(e) {
            let d = self.st.instantiate_rev(t, &fvars);
            let s = self.infer_core(d, infer_only)?;
            let s = self.ensure_sort(s)?;
            us.push(self.sort_level(s).unwrap());
            let fv = self.push_local(n, d, None, bi);
            fvars.push(fv);
            e = b;
        }
        let body = self.st.instantiate_rev(e, &fvars);
        let s = self.infer_core(body, infer_only)?;
        let s = self.ensure_sort(s)?;
        let mut r = self.sort_level(s).unwrap();
        for &u in us.iter().rev() {
            r = univ::mk_imax(&mut self.st, u, r);
        }
        Ok(self.st.sort(r))
    }

    fn is_eager_reduce(&self, e: ExprId) -> bool {
        match self.ext.eager_reduce {
            Some(n) => {
                self.st.nargs(e) == 2
                    && matches!(self.st.node(self.st.head(e)), ExprNode::Const(m, _) if m == n)
            }
            None => false,
        }
    }

    fn infer_app(&mut self, e: ExprId, infer_only: bool) -> R<ExprId> {
        if !infer_only {
            let ExprNode::App(f, a) = self.st.node(e) else {
                unreachable!()
            };
            let ft = self.infer_core(f, false)?;
            let ft = self.ensure_pi(ft)?;
            let at = self.infer_core(a, false)?;
            let ExprNode::Pi(_, _, dom, body) = self.st.node(ft) else {
                unreachable!()
            };
            let ok = if self.is_eager_reduce(a) {
                let saved = std::mem::replace(&mut self.eager, true);
                let r = self.is_def_eq(at, dom);
                self.eager = saved;
                r?
            } else {
                self.is_def_eq(at, dom)?
            };
            if !ok {
                return err(format!(
                    "application type mismatch: argument {} has type {} but is expected to have type {}",
                    self.pp(a),
                    self.pp(at),
                    self.pp(dom)
                ));
            }
            Ok(self.st.instantiate1(body, a))
        } else {
            let mut args = Vec::new();
            let f = self.st.spine(e, &mut args);
            let mut ft = self.infer_core(f, true)?;
            let mut j = 0;
            for i in 0..args.len() {
                match self.st.node(ft) {
                    ExprNode::Pi(_, _, _, b) => ft = b,
                    _ => {
                        ft = self.st.instantiate_rev(ft, &args[j..i]);
                        ft = self.ensure_pi(ft)?;
                        let ExprNode::Pi(_, _, _, b) = self.st.node(ft) else {
                            unreachable!()
                        };
                        ft = b;
                        j = i;
                    }
                }
            }
            Ok(self.st.instantiate_rev(ft, &args[j..]))
        }
    }

    fn infer_let(&mut self, mut e: ExprId, infer_only: bool) -> R<ExprId> {
        let mut fvars = Vec::new();
        while let ExprNode::Let(h, b) = self.st.node(e) {
            let lb = self.st.let_binder(h);
            let ty = self.st.instantiate_rev(lb.ty, &fvars);
            let val = self.st.instantiate_rev(lb.value, &fvars);
            if !infer_only {
                let s = self.infer_core(ty, false)?;
                self.ensure_sort(s)?;
                let vt = self.infer_core(val, false)?;
                if !self.is_def_eq(vt, ty)? {
                    return err(format!(
                        "type mismatch at let '{}': value has type {} but is expected to have type {}",
                        self.show(lb.name),
                        self.pp(vt),
                        self.pp(ty)
                    ));
                }
            }
            let fv = self.push_local(lb.name, ty, Some(val), BinderInfo::Default);
            fvars.push(fv);
            e = b;
        }
        let body = self.st.instantiate_rev(e, &fvars);
        let r = self.infer_core(body, infer_only)?;
        let r = self.cheap_beta_reduce(r);
        Ok(self.mk_pi(&fvars, r))
    }

    fn cheap_beta_reduce(&mut self, e: ExprId) -> ExprId {
        if !matches!(self.st.node(e), ExprNode::App(..)) {
            return e;
        }
        let mut args = Vec::new();
        let mut f = self.st.spine(e, &mut args);
        if !matches!(self.st.node(f), ExprNode::Lam(..)) {
            return e;
        }
        let mut i = 0;
        while i < args.len()
            && let ExprNode::Lam(_, _, _, b) = self.st.node(f)
        {
            i += 1;
            f = b;
        }
        if !self.st.has_loose_bvars(f) {
            self.st.apps(f, &args[i..])
        } else if let ExprNode::BVar(k) = self.st.node(f) {
            let h = args[i - k as usize - 1];
            self.st.apps(h, &args[i..])
        } else {
            e
        }
    }

    fn proj_error(&self, e: ExprId) -> KErr {
        KErr::new(format!("invalid projection {}", self.pp(e)))
    }

    fn infer_proj(
        &mut self,
        e: ExprId,
        sname: NameId,
        idx: u32,
        x: ExprId,
        infer_only: bool,
    ) -> R<ExprId> {
        let xt = self.infer_core(x, infer_only)?;
        let ty = self.whnf(xt)?;
        let mut args = Vec::new();
        let i_head = self.st.spine(ty, &mut args);
        let ExprNode::Const(i_name, i_lvls) = self.st.node(i_head) else {
            return Err(self.proj_error(e));
        };
        if i_name != sname {
            return Err(self.proj_error(e));
        }
        let i_decl = self.get(i_name)?;
        let DeclKind::Inductive {
            num_params,
            num_indices,
            ctors,
            ..
        } = i_decl.kind
        else {
            return Err(self.proj_error(e));
        };
        if ctors.len() != 1 || args.len() != (num_params + num_indices) as usize {
            return Err(self.proj_error(e));
        }
        let ctor = self.st.name_list(ctors)[0];
        let c_decl = self.get(ctor)?;
        let mut r = self.instantiate_type(&c_decl, i_lvls);
        for &a in args.iter().take(num_params as usize) {
            r = self.whnf(r)?;
            let ExprNode::Pi(_, _, _, b) = self.st.node(r) else {
                return Err(self.proj_error(e));
            };
            r = self.st.instantiate1(b, a);
        }
        let is_prop_type = self.is_prop(ty)?;
        for i in 0..idx {
            r = self.whnf(r)?;
            let ExprNode::Pi(_, _, d, b) = self.st.node(r) else {
                return Err(self.proj_error(e));
            };
            if self.st.has_loose_bvars(b) {
                if is_prop_type && !self.is_prop(d)? {
                    return Err(self.proj_error(e));
                }
                let p = self.st.proj(i_name, i, x);
                r = self.st.instantiate1(b, p);
            } else {
                r = b;
            }
        }
        r = self.whnf(r)?;
        let ExprNode::Pi(_, _, d, _) = self.st.node(r) else {
            return Err(self.proj_error(e));
        };
        if is_prop_type && !self.is_prop(d)? {
            return Err(self.proj_error(e));
        }
        Ok(d)
    }

    /// Whether `e` is a proposition (its type is `Prop` up to level equivalence).
    pub fn is_prop(&mut self, e: ExprId) -> R<bool> {
        let t = self.infer(e)?;
        let s = self.ensure_sort(t)?;
        let l = self.sort_level(s).unwrap();
        Ok(univ::normalizes_to_zero(&self.st, l))
    }

    // ---- weak head normal form ----

    fn is_let_fvar(&self, e: ExprId) -> Option<ExprId> {
        self.fvar_decl(e).and_then(|d| d.val)
    }

    pub fn whnf_core(&mut self, e: ExprId) -> R<ExprId> {
        self.whnf_core_with(e, false, false)
    }

    pub fn whnf_core_with(&mut self, e: ExprId, cheap_rec: bool, cheap_proj: bool) -> R<ExprId> {
        match self.st.node(e) {
            ExprNode::BVar(_)
            | ExprNode::Sort(_)
            | ExprNode::Pi(..)
            | ExprNode::Const(..)
            | ExprNode::Lam(..)
            | ExprNode::NatSmall(..)
            | ExprNode::NatBig(_)
            | ExprNode::Str(_) => return Ok(e),
            ExprNode::FVar(_) => {
                return match self.is_let_fvar(e) {
                    Some(v) => self.whnf_core_with(v, cheap_rec, cheap_proj),
                    None => Ok(e),
                };
            }
            ExprNode::App(..) | ExprNode::Let(..) | ExprNode::Proj(..) => {}
        }
        if let Some(&r) = self.whnf_core_cache.get(&e) {
            return Ok(r);
        }
        let r = match self.st.node(e) {
            ExprNode::Proj(s, i, x) => match self.reduce_proj(s, i, x, cheap_rec, cheap_proj)? {
                Some(m) => self.whnf_core_with(m, cheap_rec, cheap_proj)?,
                None => e,
            },
            ExprNode::App(..) => {
                let mut args = Vec::new();
                let f0 = self.st.spine(e, &mut args);
                let f = self.whnf_core_with(f0, cheap_rec, cheap_proj)?;
                if let ExprNode::Lam(..) = self.st.node(f) {
                    let mut m = 0;
                    let mut b = f;
                    while m < args.len()
                        && let ExprNode::Lam(_, _, _, body) = self.st.node(b)
                    {
                        b = body;
                        m += 1;
                    }
                    let b = self.st.instantiate_rev(b, &args[..m]);
                    let r = self.st.apps(b, &args[m..]);
                    self.whnf_core_with(r, cheap_rec, cheap_proj)?
                } else if f == f0 {
                    return match self.reduce_recursor(e, cheap_rec, cheap_proj)? {
                        Some(r) => self.whnf_core_with(r, cheap_rec, cheap_proj),
                        None => Ok(e),
                    };
                } else {
                    let r = self.st.apps(f, &args);
                    self.whnf_core_with(r, cheap_rec, cheap_proj)?
                }
            }
            ExprNode::Let(h, b) => {
                let v = self.st.let_binder(h).value;
                let r = self.st.instantiate1(b, v);
                self.whnf_core_with(r, cheap_rec, cheap_proj)?
            }
            _ => unreachable!(),
        };
        if !cheap_rec && !cheap_proj {
            self.whnf_core_cache.insert(e, r);
        }
        Ok(r)
    }

    fn reduce_proj(
        &mut self,
        s: NameId,
        i: u32,
        x: ExprId,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> R<Option<ExprId>> {
        let c = if cheap_proj {
            self.whnf_core_with(x, cheap_rec, cheap_proj)?
        } else {
            self.whnf(x)?
        };
        self.reduce_proj_core(c, s, i)
    }

    fn reduce_proj_core(&mut self, mut c: ExprId, sname: NameId, idx: u32) -> R<Option<ExprId>> {
        if let ExprNode::Str(_) = self.st.node(c) {
            let x = self.string_lit_to_constructor(c)?;
            c = self.whnf(x)?;
        }
        let mut args = Vec::new();
        let mk = self.st.spine(c, &mut args);
        let ExprNode::Const(mk_name, _) = self.st.node(mk) else {
            return Ok(None);
        };
        let Some(d) = self.find(mk_name) else {
            return Ok(None);
        };
        let DeclKind::Constructor {
            induct, num_params, ..
        } = d.kind
        else {
            return Ok(None);
        };
        if induct != sname {
            return Ok(None);
        }
        let k = num_params as usize + idx as usize;
        Ok(args.get(k).copied())
    }

    fn major_induct(&mut self, rec: NameId, d: &Decl) -> Option<NameId> {
        if let Some(&n) = self.major_induct.get(&rec) {
            return Some(n);
        }
        let DeclKind::Recursor {
            num_params,
            num_indices,
            num_motives,
            num_minors,
            ..
        } = d.kind
        else {
            return None;
        };
        let k = num_params + num_motives + num_minors + num_indices;
        let mut t = d.ty;
        for _ in 0..k {
            match self.st.node(t) {
                ExprNode::Pi(_, _, _, b) => t = b,
                _ => return None,
            }
        }
        let ExprNode::Pi(_, _, dom, _) = self.st.node(t) else {
            return None;
        };
        let (n, _) = self.st.head_const(dom)?;
        self.major_induct.insert(rec, n);
        Some(n)
    }

    fn reduce_recursor(
        &mut self,
        e: ExprId,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> R<Option<ExprId>> {
        if let Some(r) = self.quot_reduce_rec(e)? {
            return Ok(Some(r));
        }
        self.inductive_reduce_rec(e, cheap_rec, cheap_proj)
    }

    fn quot_reduce_rec(&mut self, e: ExprId) -> R<Option<ExprId>> {
        let Some(q) = self.ext.quot.as_ref() else {
            return Ok(None);
        };
        let Some((f, _)) = self.st.head_const(e) else {
            return Ok(None);
        };
        let (mk_pos, arg_pos) = if f == q.lift {
            (5, 3)
        } else if f == q.ind {
            (4, 3)
        } else {
            return Ok(None);
        };
        // Only once the quotient declarations are in scope.
        if self.find(f).is_none() || !matches!(self.find(f).unwrap().kind, DeclKind::Quot { .. }) {
            return Ok(None);
        }
        let mut args = Vec::new();
        self.st.spine(e, &mut args);
        if args.len() <= mk_pos {
            return Ok(None);
        }
        let mk = self.whnf(args[mk_pos])?;
        let mut mk_args = Vec::new();
        let mk_fn = self.st.spine(mk, &mut mk_args);
        match self.st.node(mk_fn) {
            ExprNode::Const(n, _) if n == q.mk && mk_args.len() == 3 => {}
            _ => return Ok(None),
        }
        let mut r = self.st.app(args[arg_pos], mk_args[2]);
        r = self.st.apps(r, &args[mk_pos + 1..]);
        Ok(Some(r))
    }

    fn rec_whnf(&mut self, e: ExprId, cheap_rec: bool, cheap_proj: bool) -> R<ExprId> {
        if cheap_rec {
            self.whnf_core_with(e, cheap_rec, cheap_proj)
        } else {
            self.whnf(e)
        }
    }

    pub fn is_non_rec_structure(&self, n: NameId) -> bool {
        match self.find(n) {
            Some(Decl {
                kind:
                    DeclKind::Inductive {
                        ctors,
                        num_indices,
                        is_rec,
                        ..
                    },
                ..
            }) => ctors.len() == 1 && num_indices == 0 && !is_rec,
            _ => false,
        }
    }

    fn is_constructor_app(&self, e: ExprId) -> bool {
        match self.st.head_const(e) {
            Some((n, _)) => matches!(
                self.find(n),
                Some(Decl {
                    kind: DeclKind::Constructor { .. },
                    ..
                })
            ),
            None => false,
        }
    }

    fn first_ctor(&self, i: NameId) -> Option<NameId> {
        match self.find(i)?.kind {
            DeclKind::Inductive { ctors, .. } => self.st.name_list(ctors).first().copied(),
            _ => None,
        }
    }

    /// For the evaluator (`eval/`).
    pub(super) fn ctor_when_k_pub(&mut self, induct: NameId, nparams: u32, e: ExprId) -> R<ExprId> {
        self.ctor_when_k(induct, nparams, e)
    }

    pub(super) fn major_induct_of(&mut self, rec: NameId, d: &Decl) -> Option<NameId> {
        self.major_induct(rec, d)
    }

    fn ctor_when_k(&mut self, induct: NameId, nparams: u32, e: ExprId) -> R<ExprId> {
        let t = self.infer(e)?;
        let app_type = self.whnf(t)?;
        let mut args = Vec::new();
        let i = self.st.spine(app_type, &mut args);
        let ExprNode::Const(i_name, i_lvls) = self.st.node(i) else {
            return Ok(e);
        };
        if i_name != induct {
            return Ok(e);
        }
        let Some(c) = self.first_ctor(i_name) else {
            return Ok(e);
        };
        if args.len() < nparams as usize {
            return Ok(e);
        }
        let c = self.st.cnst(c, i_lvls);
        let new_c = self.st.apps(c, &args[..nparams as usize]);
        let new_t = self.infer(new_c)?;
        if !self.is_def_eq(app_type, new_t)? {
            return Ok(e);
        }
        Ok(new_c)
    }

    fn expand_eta_struct(&mut self, e_type: ExprId, e: ExprId) -> R<ExprId> {
        let mut args = Vec::new();
        let i = self.st.spine(e_type, &mut args);
        let ExprNode::Const(i_name, i_lvls) = self.st.node(i) else {
            return Ok(e);
        };
        let Some(c) = self.first_ctor(i_name) else {
            return Ok(e);
        };
        let DeclKind::Constructor {
            num_params,
            num_fields,
            ..
        } = self.get(c)?.kind
        else {
            return Ok(e);
        };
        let np = (num_params as usize).min(args.len());
        let c = self.st.cnst(c, i_lvls);
        let mut r = self.st.apps(c, &args[..np]);
        for k in 0..num_fields {
            let p = self.st.proj(i_name, k, e);
            r = self.st.app(r, p);
        }
        Ok(r)
    }

    /// Whether the recursor `d` eliminates into any universe: it has one
    /// universe parameter more than the first type of its block (as
    /// leanprover/lean4#15371 tests it; the major's own type can be an
    /// auxiliary nested one).
    fn is_large_elim(&self, d: &Decl) -> bool {
        let DeclKind::Recursor { all, .. } = d.kind else {
            return false;
        };
        let Some(&first) = self.st.name_list(all).first() else {
            return false;
        };
        match self.find(first) {
            Some(i) => d.level_params.len() != i.level_params.len(),
            None => false,
        }
    }

    fn ctor_when_structure(&mut self, rec: &Decl, induct: NameId, e: ExprId) -> R<ExprId> {
        if !self.is_non_rec_structure(induct)
            || self.is_constructor_app(e)
            || matches!(self.st.node(e), ExprNode::Str(_))
        {
            return Ok(e);
        }
        let t = self.infer(e)?;
        let e_type = self.whnf(t)?;
        match self.st.head_const(e_type) {
            Some((n, _)) if n == induct => {}
            _ => return Ok(e),
        }
        // Divergence (corpus/divergences.md), after leanprover/lean4#15371:
        // Lean v4.36.0 never expands a structure in `Prop`; here one whose
        // recursor eliminates into any universe (such as `And`, whose
        // fields are all proofs) is expanded too.
        if !self.is_large_elim(rec) {
            return Ok(e);
        }
        self.expand_eta_struct(e_type, e)
    }

    fn inductive_reduce_rec(
        &mut self,
        e: ExprId,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> R<Option<ExprId>> {
        let Some((rec_name, rec_lvls)) = self.st.head_const(e) else {
            return Ok(None);
        };
        let Some(d) = self.find(rec_name) else {
            return Ok(None);
        };
        let DeclKind::Recursor {
            num_params,
            num_indices,
            num_motives,
            num_minors,
            rules,
            k,
            ..
        } = d.kind
        else {
            return Ok(None);
        };
        let mut args = Vec::new();
        self.st.spine(e, &mut args);
        let major_idx = (num_params + num_motives + num_minors + num_indices) as usize;
        if major_idx >= args.len() {
            return Ok(None);
        }
        let Some(induct) = self.major_induct(rec_name, &d) else {
            return Ok(None);
        };
        let mut major = args[major_idx];
        if k {
            major = self.ctor_when_k(induct, num_params, major)?;
        }
        // Divergence (corpus/divergences.md): structure eta comes before
        // `whnf` of the major premise, as leanprover/lean4#15351 proposes,
        // so a major premise without a normal form does not stop the
        // reduction. Both orders agree whenever Lean's terminates.
        major = self.ctor_when_structure(&d, induct, major)?;
        major = self.rec_whnf(major, cheap_rec, cheap_proj)?;
        match self.st.node(major) {
            ExprNode::NatSmall(..) | ExprNode::NatBig(_) => {
                major = self.nat_lit_to_constructor(major)?;
            }
            ExprNode::Str(_) => {
                let x = self.string_lit_to_constructor(major)?;
                major = self.whnf(x)?;
            }
            _ => {}
        }
        let mut margs = Vec::new();
        let mhead = self.st.spine(major, &mut margs);
        let ExprNode::Const(ctor, _) = self.st.node(mhead) else {
            return Ok(None);
        };
        let Some(rule) = self
            .st
            .rec_rules(rules)
            .iter()
            .find(|r| r.ctor == ctor)
            .copied()
        else {
            return Ok(None);
        };
        let nfields = rule.nfields as usize;
        if nfields > margs.len() {
            return Ok(None);
        }
        let ps: Vec<NameId> = self.st.lparams(&d).to_vec();
        let ls: Vec<LevelId> = self.st.list(rec_lvls).to_vec();
        if ps.len() != ls.len() {
            return Ok(None);
        }
        let mut rhs = self.st.instantiate_lparams(rule.rhs, &ps, &ls);
        let pmm = (num_params + num_motives + num_minors) as usize;
        rhs = self.st.apps(rhs, &args[..pmm]);
        rhs = self.st.apps(rhs, &margs[margs.len() - nfields..]);
        rhs = self.st.apps(rhs, &args[major_idx + 1..]);
        Ok(Some(rhs))
    }

    /// `n` as `Nat.zero` or `Nat.succ (n - 1)`.
    pub fn nat_lit_to_constructor(&mut self, e: ExprId) -> R<ExprId> {
        if SMALL_NAT
            && let ExprNode::NatSmall(lo, hi) = self.st.node(e)
            && let (Some(zero), Some(succ)) = (self.ext.nat_zero, self.ext.nat_succ)
        {
            let v = (hi as u64) << 32 | lo as u64;
            if v == 0 {
                return Ok(self.st.cnst(zero, LevelList::EMPTY));
            }
            self.st
                .charge_nat_unfold(u64::from(u64::BITS - v.leading_zeros()));
            let p = self.st.nat_u64(v - 1);
            let s = self.st.cnst(succ, LevelList::EMPTY);
            return Ok(self.st.app(s, p));
        }
        let Some(v) = self.nat_value(e) else {
            unreachable!()
        };
        let (Some(zero), Some(succ)) = (self.ext.nat_zero, self.ext.nat_succ) else {
            return err("a `Nat` literal needs the prelude's `Nat`");
        };
        if v == BigUint::ZERO {
            return Ok(self.st.cnst(zero, LevelList::EMPTY));
        }
        self.st.charge_nat_unfold(v.bits());
        let p = self.st.nat(v - 1u32);
        let s = self.st.cnst(succ, LevelList::EMPTY);
        Ok(self.st.app(s, p))
    }

    /// `String.ofList [Char.ofNat c₁, …]` for a string literal.
    pub fn string_lit_to_constructor(&mut self, e: ExprId) -> R<ExprId> {
        let ExprNode::Str(s) = self.st.node(e) else {
            unreachable!()
        };
        let Some(x) = self.ext.string() else {
            return err("a `String` literal needs the prelude's `String`");
        };
        let chars: Vec<u32> = self.st.str(s).chars().map(|c| c as u32).collect();
        let zero = LevelList::EMPTY;
        let char_ty = self.st.cnst(x.char, zero);
        let l0 = self.st.mk_list(&[LevelId::ZERO]);
        let nil = self.st.cnst(x.list_nil, l0);
        let cons = self.st.cnst(x.list_cons, l0);
        let nil = self.st.app(nil, char_ty);
        let cons = self.st.app(cons, char_ty);
        let of_nat = self.st.cnst(x.char_of_nat, zero);
        let mut r = nil;
        for &c in chars.iter().rev() {
            let n = self.st.nat_u64(c as u64);
            let ch = self.st.app(of_nat, n);
            let a = self.st.app(cons, ch);
            r = self.st.app(a, r);
        }
        let of_list = self.st.cnst(x.of_list, zero);
        Ok(self.st.app(of_list, r))
    }

    fn is_delta(&self, e: ExprId) -> Option<Decl> {
        let (n, ls) = self.st.head_const(e)?;
        let d = self.find(n)?;
        Self::decl_value(&d)?;
        (self.st.list(ls).len() == d.level_params.len()).then_some(d)
    }

    fn unfold_definition_core(&mut self, e: ExprId) -> Option<ExprId> {
        let ExprNode::Const(_, ls) = self.st.node(e) else {
            return None;
        };
        let d = self.is_delta(e)?;
        let v = self.unfold_value(&d)?;
        if self.st.list(ls).is_empty() {
            return Some(v);
        }
        if let Some(&r) = self.unfold_cache.get(&e) {
            return Some(r);
        }
        let ps: Vec<NameId> = self.st.lparams(&d).to_vec();
        let lv: Vec<LevelId> = self.st.list(ls).to_vec();
        let r = self.st.instantiate_lparams(v, &ps, &lv);
        self.unfold_cache.insert(e, r);
        Some(r)
    }

    fn unfold_definition(&mut self, e: ExprId) -> Option<ExprId> {
        if let ExprNode::App(..) = self.st.node(e) {
            let mut args = Vec::new();
            let f0 = self.st.spine(e, &mut args);
            let f = self.unfold_definition_core(f0)?;
            Some(self.st.apps(f, &args))
        } else {
            self.unfold_definition_core(e)
        }
    }

    pub fn nat_value(&self, e: ExprId) -> Option<BigUint> {
        match self.st.node(e) {
            ExprNode::NatSmall(lo, hi) => Some(BigUint::from((hi as u64) << 32 | lo as u64)),
            ExprNode::NatBig(b) => Some(self.st.big(b).clone()),
            _ => None,
        }
    }

    /// The value of a literal below 2^64 or of `Nat.zero`.
    fn nat_small_ext(&self, e: ExprId) -> Option<u64> {
        match self.st.node(e) {
            ExprNode::NatSmall(lo, hi) => Some((hi as u64) << 32 | lo as u64),
            ExprNode::Const(n, ls) if Some(n) == self.ext.nat_zero && ls == LevelList::EMPTY => {
                Some(0)
            }
            _ => None,
        }
    }

    /// Whether `e` is a literal or `Nat.zero`.
    fn is_nat_lit_ext(&self, e: ExprId) -> bool {
        match self.st.node(e) {
            ExprNode::NatSmall(..) | ExprNode::NatBig(_) => true,
            ExprNode::Const(n, ls) => Some(n) == self.ext.nat_zero && ls == LevelList::EMPTY,
            _ => false,
        }
    }

    /// `op x y` on literals below 2^64, if the result is one (`NatOp::small`).
    fn nat_op_small(&mut self, op: NatOp, x: ExprId, y: ExprId) -> Option<R<ExprId>> {
        let r = op.small(self.nat_small_ext(x)?, self.nat_small_ext(y)?)?;
        Some(match r {
            SmallNat::Nat(n) => Ok(self.st.nat_u64(n)),
            SmallNat::Bool(b) => self.mk_bool(b),
        })
    }

    /// The value of a literal or of `Nat.zero`.
    fn nat_lit_ext(&self, e: ExprId) -> Option<BigUint> {
        match self.st.node(e) {
            ExprNode::Const(n, ls) if Some(n) == self.ext.nat_zero && ls == LevelList::EMPTY => {
                Some(BigUint::ZERO)
            }
            _ => self.nat_value(e),
        }
    }

    fn nat_size_ok(v: &BigUint) -> R<()> {
        if v.bits().div_ceil(8) > NAT_MAX_BYTES {
            return err("the kernel refused a `Nat` numeral because its size exceeds the maximum");
        }
        Ok(())
    }

    fn mk_bool(&mut self, b: bool) -> R<ExprId> {
        let n = if b {
            self.ext.bool_true
        } else {
            self.ext.bool_false
        };
        match n {
            Some(n) => Ok(self.st.cnst(n, LevelList::EMPTY)),
            None => err("`Bool` is missing"),
        }
    }

    fn reduce_nat(&mut self, e: ExprId) -> R<Option<ExprId>> {
        if self.ext.nat.is_none() {
            return Ok(None);
        }
        let ExprNode::App(f, a2) = self.st.node(e) else {
            return Ok(None);
        };
        match self.st.node(f) {
            ExprNode::Const(n, ls) if ls == LevelList::EMPTY && Some(n) == self.ext.nat_succ => {
                let a = self.whnf(a2)?;
                if SMALL_NAT
                    && let Some(x) = self.nat_small_ext(a)
                    && let Some(r) = x.checked_add(1)
                {
                    return Ok(Some(self.st.nat_u64(r)));
                }
                let Some(v) = self.nat_lit_ext(a) else {
                    return Ok(None);
                };
                let v = v + 1u32;
                Self::nat_size_ok(&v)?;
                Ok(Some(self.st.nat(v)))
            }
            ExprNode::App(g, a1) => {
                let ExprNode::Const(n, ls) = self.st.node(g) else {
                    return Ok(None);
                };
                if ls != LevelList::EMPTY {
                    return Ok(None);
                }
                let Some(op) = self.ext.nat_op(n) else {
                    return Ok(None);
                };
                let x = self.whnf(a1)?;
                if !self.is_nat_lit_ext(x) {
                    return Ok(None);
                }
                let y = self.whnf(a2)?;
                if SMALL_NAT && let Some(r) = self.nat_op_small(op, x, y) {
                    return r.map(Some);
                }
                let Some(x) = self.nat_lit_ext(x) else {
                    return Ok(None);
                };
                let Some(y) = self.nat_lit_ext(y) else {
                    return Ok(None);
                };
                self.nat_op(op, x, y).map(Some)
            }
            _ => Ok(None),
        }
    }

    fn nat_op(&mut self, op: NatOp, x: BigUint, y: BigUint) -> R<ExprId> {
        let r = match op {
            NatOp::Add => x + y,
            NatOp::Sub => {
                if x >= y {
                    x - y
                } else {
                    BigUint::ZERO
                }
            }
            NatOp::Mul => x * y,
            NatOp::Div => {
                if y == BigUint::ZERO {
                    BigUint::ZERO
                } else {
                    x / y
                }
            }
            NatOp::Mod => {
                if y == BigUint::ZERO {
                    x
                } else {
                    x % y
                }
            }
            NatOp::Gcd => num_integer_gcd(x, y),
            NatOp::Beq => return self.mk_bool(x == y),
            NatOp::Ble => return self.mk_bool(x <= y),
            NatOp::Land => x & y,
            NatOp::Lor => x | y,
            NatOp::Xor => x ^ y,
            NatOp::Pow => {
                let Ok(k) = u32::try_from(&y) else {
                    return err(
                        "the kernel refused to evaluate `Nat.pow` because its second argument does not fit in a 32-bit unsigned integer",
                    );
                };
                if x > BigUint::from(1u32)
                    && k != 0
                    && x.bits().div_ceil(8) > NAT_MAX_BYTES / k as u64
                {
                    return err(
                        "the kernel refused to evaluate `Nat.pow` because the result would exceed the maximum numeral size",
                    );
                }
                x.pow(k)
            }
            NatOp::ShiftLeft => {
                if x == BigUint::ZERO {
                    BigUint::ZERO
                } else {
                    let Ok(k) = u32::try_from(&y) else {
                        return err(
                            "the kernel refused to evaluate `Nat.shiftLeft` because its second argument does not fit in a 32-bit unsigned integer",
                        );
                    };
                    if x.bits().div_ceil(8) + k as u64 / 8 + 1 > NAT_MAX_BYTES {
                        return err(
                            "the kernel refused a `Nat` numeral because its size exceeds the maximum",
                        );
                    }
                    x << k
                }
            }
            NatOp::ShiftRight => match u64::try_from(&y) {
                Ok(k) if k < x.bits() => x >> k,
                _ => BigUint::ZERO,
            },
        };
        if matches!(op, NatOp::Add | NatOp::Sub | NatOp::Mul) {
            Self::nat_size_ok(&r)?;
        }
        Ok(self.st.nat(r))
    }

    pub fn whnf(&mut self, e: ExprId) -> R<ExprId> {
        match self.st.node(e) {
            ExprNode::BVar(_)
            | ExprNode::Sort(_)
            | ExprNode::Pi(..)
            | ExprNode::NatSmall(..)
            | ExprNode::NatBig(_)
            | ExprNode::Str(_) => return Ok(e),
            ExprNode::FVar(_) if self.is_let_fvar(e).is_none() => return Ok(e),
            _ => {}
        }
        if let Some(&r) = self.whnf_cache.get(&e) {
            return Ok(r);
        }
        if !self.st.has_fvar(e)
            && !self.st.has_loose_bvars(e)
            && super::eval::enabled()
            && let Some(v) = super::eval::whnf(self, e)
        {
            self.whnf_cache.insert(e, v);
            return Ok(v);
        }
        let mut t = e;
        loop {
            let t1 = self.whnf_core(t)?;
            if let Some(v) = self.reduce_nat(t1)? {
                self.whnf_cache.insert(e, v);
                return Ok(v);
            }
            match self.unfold_definition(t1) {
                Some(n) => t = n,
                None => {
                    self.whnf_cache.insert(e, t1);
                    return Ok(t1);
                }
            }
        }
    }

    // ---- definitional equality ----

    fn is_def_eq_binding(&mut self, mut t: ExprId, mut s: ExprId) -> R<bool> {
        let lam = matches!(self.st.node(t), ExprNode::Lam(..));
        let mut subst: Vec<ExprId> = Vec::new();
        while let (ExprNode::Lam(_, _, td, tb), ExprNode::Lam(_, sn, sd, sb))
        | (ExprNode::Pi(_, _, td, tb), ExprNode::Pi(_, sn, sd, sb)) =
            (self.st.node(t), self.st.node(s))
        {
            let sbi = match self.st.node(s) {
                ExprNode::Lam(bi, ..) | ExprNode::Pi(bi, ..) => bi,
                _ => unreachable!(),
            };
            let mut var_s_type = None;
            if td != sd {
                let st_ = self.st.instantiate_rev(sd, &subst);
                let tt = self.st.instantiate_rev(td, &subst);
                if !self.is_def_eq(tt, st_)? {
                    return Ok(false);
                }
                var_s_type = Some(st_);
            }
            if self.st.has_loose_bvars(tb) || self.st.has_loose_bvars(sb) {
                let ty = match var_s_type {
                    Some(x) => x,
                    None => self.st.instantiate_rev(sd, &subst),
                };
                let fv = self.push_local(sn, ty, None, sbi);
                subst.push(fv);
            } else {
                // Not referenced: any closed term will do (Lean: `dontcare`).
                subst.push(self.st.sort(LevelId::ZERO));
            }
            t = tb;
            s = sb;
            let same = match (self.st.node(t), self.st.node(s)) {
                (ExprNode::Lam(..), ExprNode::Lam(..)) => lam,
                (ExprNode::Pi(..), ExprNode::Pi(..)) => !lam,
                _ => false,
            };
            if !same {
                break;
            }
        }
        let t = self.st.instantiate_rev(t, &subst);
        let s = self.st.instantiate_rev(s, &subst);
        self.is_def_eq(t, s)
    }

    pub fn is_def_eq_level(&mut self, a: LevelId, b: LevelId) -> bool {
        if a == b {
            return true;
        }
        let k = if a < b { (a, b) } else { (b, a) };
        if let Some(&r) = self.level_eq.get(&k) {
            return r;
        }
        let r = univ::equiv(&mut self.st, a, b);
        self.level_eq.insert(k, r);
        r
    }

    pub fn is_def_eq_levels(&mut self, a: LevelList, b: LevelList) -> bool {
        if a == b {
            return true;
        }
        let la: Vec<LevelId> = self.st.list(a).to_vec();
        let lb: Vec<LevelId> = self.st.list(b).to_vec();
        la.len() == lb.len()
            && la
                .iter()
                .zip(&lb)
                .all(|(&x, &y)| self.is_def_eq_level(x, y))
    }

    fn is_lit(n: &ExprNode) -> bool {
        matches!(
            n,
            ExprNode::NatSmall(..) | ExprNode::NatBig(_) | ExprNode::Str(_)
        )
    }

    fn quick_is_def_eq(&mut self, t: ExprId, s: ExprId) -> R<Option<bool>> {
        if t == s || self.eq_ok.contains(&pair(t, s)) {
            return Ok(Some(true));
        }
        let (nt, ns) = (self.st.node(t), self.st.node(s));
        Ok(match (nt, ns) {
            (ExprNode::Lam(..), ExprNode::Lam(..)) | (ExprNode::Pi(..), ExprNode::Pi(..)) => {
                Some(self.is_def_eq_binding(t, s)?)
            }
            (ExprNode::Sort(a), ExprNode::Sort(b)) => Some(self.is_def_eq_level(a, b)),
            // Literals are canonical: equal values have equal ids.
            _ if Self::is_lit(&nt) && Self::is_lit(&ns) => Some(false),
            _ => None,
        })
    }

    fn is_def_eq_args(&mut self, t: ExprId, s: ExprId) -> R<bool> {
        let (mut t, mut s) = (t, s);
        loop {
            match (self.st.node(t), self.st.node(s)) {
                (ExprNode::App(tf, ta), ExprNode::App(sf, sa)) => {
                    if !self.is_def_eq(ta, sa)? {
                        return Ok(false);
                    }
                    t = tf;
                    s = sf;
                }
                (ExprNode::App(..), _) | (_, ExprNode::App(..)) => return Ok(false),
                _ => return Ok(true),
            }
        }
    }

    fn try_eta_expansion_core(&mut self, t: ExprId, s: ExprId) -> R<bool> {
        if matches!(self.st.node(t), ExprNode::Lam(..))
            && !matches!(self.st.node(s), ExprNode::Lam(..))
        {
            let st_ = self.infer(s)?;
            let s_type = self.whnf(st_)?;
            let ExprNode::Pi(bi, n, d, _) = self.st.node(s_type) else {
                return Ok(false);
            };
            let b0 = self.st.bvar(0);
            let s1 = self.st.lift_loose(s, 0, 1);
            let body = self.st.app(s1, b0);
            let new_s = self.st.lam(bi, n, d, body);
            self.is_def_eq(t, new_s)
        } else {
            Ok(false)
        }
    }

    fn try_eta_expansion(&mut self, t: ExprId, s: ExprId) -> R<bool> {
        Ok(self.try_eta_expansion_core(t, s)? || self.try_eta_expansion_core(s, t)?)
    }

    fn try_eta_struct_core(&mut self, t: ExprId, s: ExprId) -> R<bool> {
        let mut s_args = Vec::new();
        let f = self.st.spine(s, &mut s_args);
        let ExprNode::Const(fname, _) = self.st.node(f) else {
            return Ok(false);
        };
        let Some(d) = self.find(fname) else {
            return Ok(false);
        };
        let DeclKind::Constructor {
            induct,
            num_params,
            num_fields,
            ..
        } = d.kind
        else {
            return Ok(false);
        };
        if s_args.len() != (num_params + num_fields) as usize {
            return Ok(false);
        }
        if !self.is_non_rec_structure(induct) {
            return Ok(false);
        }
        let tt = self.infer(t)?;
        let ts = self.infer(s)?;
        if !self.is_def_eq(tt, ts)? {
            return Ok(false);
        }
        for (i, &a) in s_args.iter().enumerate().skip(num_params as usize) {
            let p = self.st.proj(induct, (i - num_params as usize) as u32, t);
            if !self.is_def_eq(p, a)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn try_eta_struct(&mut self, t: ExprId, s: ExprId) -> R<bool> {
        Ok(self.try_eta_struct_core(t, s)? || self.try_eta_struct_core(s, t)?)
    }

    fn is_def_eq_app(&mut self, t: ExprId, s: ExprId) -> R<bool> {
        if !matches!(self.st.node(t), ExprNode::App(..))
            || !matches!(self.st.node(s), ExprNode::App(..))
        {
            return Ok(false);
        }
        let mut ta = Vec::new();
        let mut sa = Vec::new();
        let tf = self.st.spine(t, &mut ta);
        let sf = self.st.spine(s, &mut sa);
        if ta.len() != sa.len() || !self.is_def_eq(tf, sf)? {
            return Ok(false);
        }
        for i in 0..ta.len() {
            if !self.is_def_eq(ta[i], sa[i])? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn is_def_eq_proof_irrel(&mut self, t: ExprId, s: ExprId) -> R<Option<bool>> {
        let tt = self.infer(t)?;
        if !self.is_prop(tt)? {
            return Ok(None);
        }
        let ts = self.infer(s)?;
        Ok(Some(self.is_def_eq(tt, ts)?))
    }

    fn try_unfold_proj_app(&mut self, e: ExprId) -> R<Option<ExprId>> {
        let f = self.st.head(e);
        if matches!(self.st.node(f), ExprNode::Proj(..)) {
            let n = self.whnf_core(e)?;
            return Ok((n != e).then_some(n));
        }
        Ok(None)
    }

    fn unfold_cheap(&mut self, e: ExprId) -> R<ExprId> {
        let u = self.unfold_definition(e).expect("delta");
        self.whnf_core_with(u, false, true)
    }

    fn lazy_delta_reduction_step(&mut self, t: &mut ExprId, s: &mut ExprId) -> R<Step> {
        let dt = self.is_delta(*t);
        let ds = self.is_delta(*s);
        match (dt, ds) {
            (None, None) => return Ok(Step::Unknown),
            (Some(_), None) => {
                if let Some(s2) = self.try_unfold_proj_app(*s)? {
                    *s = s2;
                } else {
                    *t = self.unfold_cheap(*t)?;
                }
            }
            (None, Some(_)) => {
                if let Some(t2) = self.try_unfold_proj_app(*t)? {
                    *t = t2;
                } else {
                    *s = self.unfold_cheap(*s)?;
                }
            }
            (Some(dt), Some(ds)) => {
                let c = compare_hints(Self::decl_hints(&dt), Self::decl_hints(&ds));
                if c < 0 {
                    *t = self.unfold_cheap(*t)?;
                } else if c > 0 {
                    *s = self.unfold_cheap(*s)?;
                } else {
                    if matches!(self.st.node(*t), ExprNode::App(..))
                        && matches!(self.st.node(*s), ExprNode::App(..))
                        && dt.name == ds.name
                        && matches!(Self::decl_hints(&dt), Hints::Regular(_))
                        && !self.eq_fail.contains(&pair(*t, *s))
                    {
                        let (_, lt) = self.st.head_const(*t).unwrap();
                        let (_, ls) = self.st.head_const(*s).unwrap();
                        if self.is_def_eq_levels(lt, ls) && self.is_def_eq_args(*t, *s)? {
                            return Ok(Step::Equal);
                        }
                        self.eq_fail.insert(pair(*t, *s));
                    }
                    *t = self.unfold_cheap(*t)?;
                    *s = self.unfold_cheap(*s)?;
                }
            }
        }
        Ok(match self.quick_is_def_eq(*t, *s)? {
            Some(true) => Step::Equal,
            Some(false) => Step::Diff,
            None => Step::Continue,
        })
    }

    fn is_nat_zero(&self, t: ExprId) -> bool {
        match self.st.node(t) {
            ExprNode::Const(n, ls) => Some(n) == self.ext.nat_zero && ls == LevelList::EMPTY,
            ExprNode::NatSmall(0, 0) => true,
            _ => false,
        }
    }

    fn is_nat_succ(&mut self, t: ExprId) -> Option<ExprId> {
        match self.st.node(t) {
            ExprNode::NatSmall(lo, hi) => {
                let v = (hi as u64) << 32 | lo as u64;
                (v != 0).then(|| self.st.nat_u64(v - 1))
            }
            ExprNode::NatBig(b) => {
                let v = self.st.big(b) - 1u32;
                Some(self.st.nat(v))
            }
            ExprNode::App(f, a) => match self.st.node(f) {
                ExprNode::Const(n, ls)
                    if Some(n) == self.ext.nat_succ && ls == LevelList::EMPTY =>
                {
                    Some(a)
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn is_def_eq_offset(&mut self, t: ExprId, s: ExprId) -> R<Option<bool>> {
        if self.ext.nat.is_none() {
            return Ok(None);
        }
        if self.is_nat_zero(t) && self.is_nat_zero(s) {
            return Ok(Some(true));
        }
        if let Some(pt) = self.is_nat_succ(t)
            && let Some(ps) = self.is_nat_succ(s)
        {
            return Ok(Some(self.is_def_eq_core(pt, ps)?));
        }
        Ok(None)
    }

    fn lazy_delta_reduction(&mut self, t: &mut ExprId, s: &mut ExprId) -> R<Option<bool>> {
        loop {
            if let Some(r) = self.is_def_eq_offset(*t, *s)? {
                return Ok(Some(r));
            }
            if (!self.st.has_fvar(*t) && !self.st.has_fvar(*s)) || self.eager {
                if let Some(tv) = self.reduce_nat(*t)? {
                    return Ok(Some(self.is_def_eq_core(tv, *s)?));
                } else if let Some(sv) = self.reduce_nat(*s)? {
                    return Ok(Some(self.is_def_eq_core(*t, sv)?));
                }
            }
            match self.lazy_delta_reduction_step(t, s)? {
                Step::Continue => {}
                Step::Unknown => return Ok(None),
                Step::Equal => return Ok(Some(true)),
                Step::Diff => return Ok(Some(false)),
            }
        }
    }

    fn lazy_delta_proj_reduction(
        &mut self,
        t: &mut ExprId,
        s: &mut ExprId,
        sname: NameId,
        idx: u32,
    ) -> R<bool> {
        loop {
            match self.lazy_delta_reduction_step(t, s)? {
                Step::Continue => {}
                Step::Equal => return Ok(true),
                Step::Unknown | Step::Diff => {
                    if let Some(t2) = self.reduce_proj_core(*t, sname, idx)?
                        && let Some(s2) = self.reduce_proj_core(*s, sname, idx)?
                    {
                        return self.is_def_eq_core(t2, s2);
                    }
                    return self.is_def_eq_core(*t, *s);
                }
            }
        }
    }

    fn try_string_lit_expansion_core(&mut self, t: ExprId, s: ExprId) -> R<Option<bool>> {
        let Some(x) = self.ext.string() else {
            return Ok(None);
        };
        if let ExprNode::Str(_) = self.st.node(t)
            && let ExprNode::App(f, _) = self.st.node(s)
            && matches!(self.st.node(f), ExprNode::Const(n, ls) if n == x.of_list && ls == LevelList::EMPTY)
        {
            let c = self.string_lit_to_constructor(t)?;
            let c = self.whnf(c)?;
            return Ok(Some(self.is_def_eq_core(c, s)?));
        }
        Ok(None)
    }

    fn try_string_lit_expansion(&mut self, t: ExprId, s: ExprId) -> R<Option<bool>> {
        if let Some(r) = self.try_string_lit_expansion_core(t, s)? {
            return Ok(Some(r));
        }
        self.try_string_lit_expansion_core(s, t)
    }

    fn is_def_eq_unit_like(&mut self, t: ExprId, s: ExprId) -> R<bool> {
        let tt = self.infer(t)?;
        let t_type = self.whnf(tt)?;
        let Some((i, _)) = self.st.head_const(t_type) else {
            return Ok(false);
        };
        if !self.is_non_rec_structure(i) {
            return Ok(false);
        }
        let Some(c) = self.first_ctor(i) else {
            return Ok(false);
        };
        match self.get(c)?.kind {
            DeclKind::Constructor { num_fields: 0, .. } => {}
            _ => return Ok(false),
        }
        let ts = self.infer(s)?;
        self.is_def_eq_core(t_type, ts)
    }

    fn is_bool_true(&self, e: ExprId) -> bool {
        matches!(self.st.node(e), ExprNode::Const(n, ls) if Some(n) == self.ext.bool_true && ls == LevelList::EMPTY)
    }

    pub fn is_def_eq_core(&mut self, t: ExprId, s: ExprId) -> R<bool> {
        if let Some(r) = self.quick_is_def_eq(t, s)? {
            return Ok(r);
        }
        if (!self.st.has_fvar(t) || self.eager) && self.is_bool_true(s) {
            let w = self.whnf(t)?;
            if self.is_bool_true(w) {
                return Ok(true);
            }
        }
        let mut tn = self.whnf_core_with(t, false, true)?;
        let mut sn = self.whnf_core_with(s, false, true)?;
        if (tn != t || sn != s)
            && let Some(r) = self.quick_is_def_eq(tn, sn)?
        {
            return Ok(r);
        }
        if let Some(r) = self.is_def_eq_proof_irrel(tn, sn)? {
            return Ok(r);
        }
        if let Some(r) = self.lazy_delta_reduction(&mut tn, &mut sn)? {
            return Ok(r);
        }
        if let (ExprNode::Const(a, la), ExprNode::Const(b, lb)) =
            (self.st.node(tn), self.st.node(sn))
            && a == b
            && self.is_def_eq_levels(la, lb)
        {
            return Ok(true);
        }
        if let (ExprNode::FVar(a), ExprNode::FVar(b)) = (self.st.node(tn), self.st.node(sn))
            && a == b
        {
            return Ok(true);
        }
        if let (ExprNode::Proj(sa, ia, xa), ExprNode::Proj(sb, ib, xb)) =
            (self.st.node(tn), self.st.node(sn))
            && sa == sb
            && ia == ib
        {
            let (mut tc, mut sc) = (xa, xb);
            if self.lazy_delta_proj_reduction(&mut tc, &mut sc, sa, ia)? {
                return Ok(true);
            }
        }
        let tnn = self.whnf_core(tn)?;
        let snn = self.whnf_core(sn)?;
        if tnn != tn || snn != sn {
            return self.is_def_eq_core(tnn, snn);
        }
        if self.is_def_eq_app(tn, sn)? {
            return Ok(true);
        }
        if self.try_eta_expansion(tn, sn)? {
            return Ok(true);
        }
        if self.try_eta_struct(tn, sn)? {
            return Ok(true);
        }
        if let Some(r) = self.try_string_lit_expansion(tn, sn)? {
            return Ok(r);
        }
        self.is_def_eq_unit_like(tn, sn)
    }

    pub fn is_def_eq(&mut self, t: ExprId, s: ExprId) -> R<bool> {
        let r = self.is_def_eq_core(t, s)?;
        if r {
            self.eq_ok.insert(pair(t, s));
        }
        Ok(r)
    }
}

fn compare_hints(h1: Hints, h2: Hints) -> i32 {
    match (h1, h2) {
        (Hints::Regular(a), Hints::Regular(b)) => {
            if a == b {
                0
            } else if a > b {
                -1
            } else {
                1
            }
        }
        (Hints::Opaque, Hints::Opaque) | (Hints::Abbrev, Hints::Abbrev) => 0,
        (Hints::Opaque, _) => 1,
        (_, Hints::Opaque) => -1,
        (Hints::Abbrev, _) => -1,
        (_, Hints::Abbrev) => 1,
    }
}

fn num_integer_gcd(mut a: BigUint, mut b: BigUint) -> BigUint {
    while b != BigUint::ZERO {
        let r = &a % &b;
        a = b;
        b = r;
    }
    a
}
