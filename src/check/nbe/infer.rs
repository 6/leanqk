//! Type inference and checking. Terms are inferred in an environment of
//! values for their loose bound variables; types are values. Checking a
//! λ against a known Π type goes binder by binder (Lean infers the λ's
//! type and compares it with the Π, which makes the same comparisons).

use crate::env::{DeclKind, Safety};
use crate::expr::{BinderInfo, ExprData, ExprId, ExprNode};
use crate::level::{LevelId, LevelList};
use crate::name::NameId;

use super::super::tc::{KErr, NAT_MAX_BYTES, R};
use super::super::univ;
use super::val::{Elim, Env, Ls, NONE, Sp, V, Val};
use super::{BOTTOM, INFER_SLOTS, Nbe};

fn err<T>(msg: impl Into<String>) -> R<T> {
    Err(KErr::new(msg.into()))
}

/// Whether an argument's type is compared with the domain as a term
/// (`syn_eq_term`) before the domain's value is made.
const SYN_DOM: bool = true;

/// Past this many environment entries in range, `infer_term`'s memo goes
/// through a thunk.
const INFER_MEMO_RANGE: u32 = 32;

/// A key of `infer_term`'s memo.
#[derive(Clone, Copy)]
enum IKey {
    Memo(usize),
    Thunk(V),
}

enum LambdaExpected {
    Value(V),
    Pi(ExprNode, Env, Ls),
}

/// Whether the codomain of a Π type instantiated at an argument is
/// remembered when it is an application (see `eval_codomain`).
const CODOMAIN_SLOT: bool = true;

impl Nbe<'_> {
    // ---- binders ----

    /// The domain of a λ, Π or `PiInfer` value.
    pub fn binder_dom(&mut self, v: V) -> V {
        let (Val::Lam(t, env, ls) | Val::Pi(t, env, ls) | Val::PiInfer(t, env, ls)) = self.a.get(v)
        else {
            unreachable!()
        };
        let (ExprNode::Lam(_, _, d, _) | ExprNode::Pi(_, _, d, _)) = self.st.node(t) else {
            unreachable!()
        };
        self.thunk(d, env, ls)
    }

    /// The value of a binder's body `b` in `env`. An application is
    /// remembered by its exact term and environment (`eval_slot`): the type
    /// of one application is often inferred more than once.
    fn eval_codomain(&mut self, b: ExprId, env: Env, ls: Ls) -> V {
        if CODOMAIN_SLOT && matches!(self.st.node(b), ExprNode::App(..)) {
            return self.eval_slot(b, env, ls);
        }
        self.eval(b, env, ls)
    }

    /// Whether the body of a binder value may refer to its variable.
    pub fn body_uses_var(&self, v: V) -> bool {
        match self.a.get(v) {
            Val::Lam(t, ..) | Val::Pi(t, ..) => match self.st.node(t) {
                ExprNode::Lam(_, _, _, b) | ExprNode::Pi(_, _, _, b) => self.st.has_loose_bvars(b),
                _ => true,
            },
            _ => true,
        }
    }

    /// The body of a binder value with its variable bound to `x`.
    pub fn instantiate(&mut self, v: V, x: V) -> R<V> {
        self.instantiate_binder(self.a.get(v), x)
    }

    fn instantiate_binder(&mut self, binder: Val, x: V) -> R<V> {
        match binder {
            Val::Lam(t, env, ls) | Val::Pi(t, env, ls) => {
                let (ExprNode::Lam(_, _, _, b) | ExprNode::Pi(_, _, _, b)) = self.st.node(t) else {
                    unreachable!()
                };
                let env2 = self.bind_value(b, env, x);
                Ok(self.eval_codomain(b, env2, ls))
            }
            Val::PiInfer(t, env, ls) => {
                let ExprNode::Lam(_, _, _, b) = self.st.node(t) else {
                    unreachable!()
                };
                let env2 = self.bind_value(b, env, x);
                self.infer_term(b, env2, ls, true)
            }
            _ => unreachable!(),
        }
    }

    #[inline]
    fn bind_value(&mut self, body: ExprId, env: Env, arg: V) -> Env {
        if self.st.has_loose_bvars(body) {
            self.a.cons(env, arg)
        } else {
            Env::NIL
        }
    }

    fn sort_level(&self, v: V) -> Option<LevelId> {
        match self.a.get(v) {
            Val::Sort(l) => Some(l),
            _ => None,
        }
    }

    pub fn ensure_sort(&mut self, v: V) -> R<LevelId> {
        let v = self.force(v);
        if let Some(l) = self.sort_level(v) {
            return Ok(l);
        }
        let w = self.whnf(v)?;
        match self.sort_level(w) {
            Some(l) => Ok(l),
            None => err(format!("type expected, got {}", self.pp(v))),
        }
    }

    #[inline]
    fn ensure_pi(&mut self, v: V) -> R<Val> {
        let binder = self.a.get(v);
        if matches!(binder, Val::Pi(..) | Val::PiInfer(..)) {
            return Ok(binder);
        }
        self.reduce_to_pi(v)
    }

    #[inline(never)]
    fn reduce_to_pi(&mut self, v: V) -> R<Val> {
        let v = self.force(v);
        let binder = self.a.get(v);
        if matches!(binder, Val::Pi(..) | Val::PiInfer(..)) {
            return Ok(binder);
        }
        let whnf = self.whnf(v)?;
        let binder = self.a.get(whnf);
        if matches!(binder, Val::Pi(..) | Val::PiInfer(..)) {
            Ok(binder)
        } else {
            err(format!("function expected, got {}", self.pp(v)))
        }
    }

    /// Whether the type `t` is a proposition.
    pub fn is_prop(&mut self, t: V) -> R<bool> {
        let tt = self.infer_value(t)?;
        let l = self.ensure_sort(tt)?;
        Ok(univ::normalizes_to_zero(&self.st, l))
    }

    fn check_level(&self, l: LevelId) -> R<()> {
        if let Some(p) = univ::undefined_param(&self.st, l, &self.lparams) {
            return err(format!(
                "invalid reference to undefined universe level parameter '{}'",
                self.st.show(p)
            ));
        }
        Ok(())
    }

    fn nat_type(&mut self) -> R<V> {
        match self.ext.nat {
            Some(n) if self.find(n).is_some() => Ok(self.cnst(n, LevelList::EMPTY)),
            _ => err(
                "a `Nat` literal needs the prelude's `Nat` (absent or not the expected inductive type)",
            ),
        }
    }

    fn string_type(&mut self) -> R<V> {
        match self.ext.string() {
            Some(s) if self.find(s.string).is_some() && self.find(s.of_list).is_some() => {
                let n = s.string;
                Ok(self.cnst(n, LevelList::EMPTY))
            }
            _ => err(
                "a `String` literal needs the prelude's `String`, `String.ofList`, `Char.ofNat` and `List` (absent or not the expected declarations)",
            ),
        }
    }

    // ---- types of values ----

    /// The type of a value.
    #[inline]
    pub fn infer_value(&mut self, v: V) -> R<V> {
        let c = self.a.r(v).ty;
        if c != super::val::NONE {
            return Ok(V(c));
        }
        self.infer_value_uncached(v)
    }

    #[inline(never)]
    fn infer_value_uncached(&mut self, v: V) -> R<V> {
        let r = match self.a.get(v) {
            Val::Sort(l) => {
                let l = self.st.succ(l);
                self.a.mk(Val::Sort(l))
            }
            Val::Nat(..) | Val::NatBig(_) => self.nat_type()?,
            Val::Str(_) => self.string_type()?,
            Val::Lam(t, env, ls) => self.a.mk(Val::PiInfer(t, env, ls)),
            Val::Pi(t, env, ls) | Val::Thunk(t, env, ls) => self.infer_term(t, env, ls, true)?,
            Val::PiInfer(t, env, ls) => {
                let ExprNode::Lam(bi, n, d, b) = self.st.node(t) else {
                    unreachable!()
                };
                let dv = self.thunk(d, env, ls);
                let ds = self.infer_value(dv)?;
                let u = self.ensure_sort(ds)?;
                let x = self.push_fvar(n, dv, None, bi);
                let env2 = self.a.cons(env, x);
                let bt = self.infer_term(b, env2, ls, true)?;
                let bs = self.infer_value(bt)?;
                let w = self.ensure_sort(bs)?;
                self.pop_fvar(x);
                let r = univ::mk_imax(&mut self.st, u, w);
                self.a.mk(Val::Sort(r))
            }
            Val::Const(n, l, sp) => {
                let d = self.get(n)?;
                let t = self.const_type(&d, l);
                self.apply_type(v, t, sp)?
            }
            Val::FVar(k, sp) => {
                if k == BOTTOM {
                    return err("ill-typed term met during reduction");
                }
                let t = self.fvars[k as usize].ty;
                self.apply_type(v, t, sp)?
            }
        };
        self.a.rm(v).ty = r.0;
        Ok(r)
    }

    /// The type of the neutral `v` with spine `sp`, given the type of its head.
    fn apply_type(&mut self, v: V, mut t: V, sp: Sp) -> R<V> {
        if sp == Sp::NIL {
            return Ok(t);
        }
        if !self.a.sp_has_proj(sp) {
            return self.apply_type_args(t, sp);
        }
        let mut last_proj = None;
        for i in 0..self.a.sp_len(sp) {
            match self.a.sp_elim(sp, i) {
                Elim::Arg(a) => {
                    let binder = self.ensure_pi(t)?;
                    t = self.instantiate_binder(binder, a)?;
                }
                Elim::Proj(s, j) => {
                    // A projection can use the value of its prefix in the
                    // field type. Replay from the last projection, which may
                    // have reduced to a constructor field.
                    let cur = if let Some((mut cur, start)) = last_proj {
                        for k in start..i {
                            let e = self.a.sp_elim(sp, k);
                            cur = self.apply_elim(cur, e);
                        }
                        cur
                    } else {
                        let prefix = self.a.sp_prefix(sp, i);
                        let head = match self.a.get(v) {
                            Val::Const(n, ls, _) => Val::Const(n, ls, prefix),
                            Val::FVar(k, _) => Val::FVar(k, prefix),
                            _ => unreachable!(),
                        };
                        self.a.mk(head)
                    };
                    t = self.proj_type(cur, t, s, j)?;
                    last_proj = Some((cur, i));
                }
            }
        }
        Ok(t)
    }

    /// Walk ordinary Π binders in an application-only spine without
    /// allocating a value for each intermediate binder.
    fn apply_type_args(&mut self, mut ty: V, sp: Sp) -> R<V> {
        let end = self.a.sp_len(sp);
        let mut i = 0;
        while i < end {
            let pi = self.ensure_pi(ty)?;
            let Val::Pi(e, mut env, ls) = pi else {
                let arg = self.a.sp_arg(sp, i);
                ty = self.instantiate_binder(pi, arg)?;
                i += 1;
                continue;
            };
            let first = i;
            let mut binder = self.st.node(e);
            let body = loop {
                let ExprNode::Pi(_, _, _, body) = binder else {
                    unreachable!()
                };
                i += 1;
                if i < end {
                    binder = self.st.node(body);
                    if matches!(binder, ExprNode::Pi(..)) {
                        continue;
                    }
                }
                break body;
            };
            // Only the final codomain is evaluated. Its loose variables
            // determine which arguments and outer bindings it can read.
            let data = self.st.data(body);
            let range = data.loose_bvar_range();
            let applied = i - first;
            if range <= applied {
                env = Env::NIL;
            }
            for j in i - range.min(applied)..i {
                let arg = if data.may_use_bvar(i - 1 - j) {
                    self.a.sp_arg(sp, j)
                } else {
                    self.hole()
                };
                env = self.a.cons(env, arg);
            }
            ty = self.eval(body, env, ls);
        }
        Ok(ty)
    }

    fn proj_error(&mut self, x: V, s: NameId, i: u32) -> KErr {
        let e = self.readback(x);
        let e = self.st.proj(s, i, e);
        KErr::new(format!("invalid projection {}", self.pp_term(e)))
    }

    /// The type of `x.idx` (of the structure `sname`), given the type `xt`
    /// of `x` (Lean's `infer_proj`).
    fn proj_type(&mut self, x: V, xt: V, sname: NameId, idx: u32) -> R<V> {
        let ty = self.whnf(xt)?;
        let Val::Const(i_name, i_lvls, sp) = self.a.get(ty) else {
            return Err(self.proj_error(x, sname, idx));
        };
        if i_name != sname {
            return Err(self.proj_error(x, sname, idx));
        }
        let i_decl = self.get(i_name)?;
        let DeclKind::Inductive {
            num_params,
            num_indices,
            ctors,
            ..
        } = i_decl.kind
        else {
            return Err(self.proj_error(x, sname, idx));
        };
        if self.a.sp_has_proj(sp)
            || ctors.len() != 1
            || self.a.sp_len(sp) != num_params + num_indices
        {
            return Err(self.proj_error(x, sname, idx));
        }
        let ctor = self.st.name_list(ctors)[0];
        let c_decl = self.get(ctor)?;
        let mut r = self.const_type(&c_decl, i_lvls);
        for i in 0..num_params {
            let Elim::Arg(a) = self.a.sp_elim(sp, i) else {
                unreachable!()
            };
            r = self.whnf(r)?;
            if !matches!(self.a.get(r), Val::Pi(..) | Val::PiInfer(..)) {
                return Err(self.proj_error(x, sname, idx));
            }
            r = self.instantiate(r, a)?;
        }
        let is_prop_type = self.is_prop(ty)?;
        for i in 0..idx {
            r = self.whnf(r)?;
            if !matches!(self.a.get(r), Val::Pi(..) | Val::PiInfer(..)) {
                return Err(self.proj_error(x, sname, idx));
            }
            if self.body_uses_var(r) {
                if is_prop_type {
                    let d = self.binder_dom(r);
                    if !self.is_prop(d)? {
                        return Err(self.proj_error(x, sname, idx));
                    }
                }
                let p = self.proj(x, i_name, i);
                r = self.instantiate(r, p)?;
            } else {
                let dc = self.a.mk(Val::Sort(LevelId::ZERO));
                r = self.instantiate(r, dc)?;
            }
        }
        r = self.whnf(r)?;
        if !matches!(self.a.get(r), Val::Pi(..) | Val::PiInfer(..)) {
            return Err(self.proj_error(x, sname, idx));
        }
        let d = self.binder_dom(r);
        if is_prop_type && !self.is_prop(d)? {
            return Err(self.proj_error(x, sname, idx));
        }
        Ok(d)
    }

    // ---- types of terms ----

    /// The type of `e` in `env`; with `infer_only` false, also check `e`.
    pub fn infer_term(&mut self, e: ExprId, env: Env, ls: Ls, infer_only: bool) -> R<V> {
        self.infer_node(e, self.st.node(e), env, ls, infer_only)
    }

    #[inline(always)]
    fn infer_node(
        &mut self,
        e: ExprId,
        node: ExprNode,
        env: Env,
        ls: Ls,
        infer_only: bool,
    ) -> R<V> {
        match node {
            ExprNode::BVar(i) => {
                return match self.a.lookup(env, i) {
                    Some(v) => self.infer_value(v),
                    None => err("type checker does not support loose bound variables"),
                };
            }
            ExprNode::Sort(l) => {
                if !infer_only {
                    self.check_level(l)?;
                }
                let l = self.inst_level(l, ls);
                let l = self.st.succ(l);
                return Ok(self.a.mk(Val::Sort(l)));
            }
            ExprNode::Const(n, lv) => {
                return self.infer_const_expr(e, n, lv, ls, infer_only);
            }
            ExprNode::NatSmall(..) => return self.nat_type(),
            ExprNode::NatBig(b) => {
                if self.st.big(b).bits().div_ceil(8) > NAT_MAX_BYTES {
                    return err(
                        "the kernel refused a `Nat` numeral because its size exceeds the maximum",
                    );
                }
                return self.nat_type();
            }
            ExprNode::Str(_) => return self.string_type(),
            ExprNode::FVar(k) => {
                let v = self.a.mk(Val::FVar(k, Sp::NIL));
                return self.infer_value(v);
            }
            ExprNode::Lam(..) if infer_only => {
                let d = self.st.data(e);
                let env = self.trim_prune(env, d);
                let ls = if d.has_level_param() { ls } else { Ls::ID };
                return Ok(self.a.mk(Val::PiInfer(e, env, ls)));
            }
            _ => {}
        }
        let d = self.st.data(e);
        if !d.has_loose_bvars() && !d.has_fvar() && !d.has_level_param() {
            return self.infer_closed(e, node, infer_only);
        }
        let key_env = if d.has_loose_bvars() { env } else { Env::NIL };
        let has_level_param = d.has_level_param();
        let key_ls = if has_level_param { ls } else { Ls::ID };
        let hash = crate::hash::hash2(e.0 as u64 | (key_ls.0 as u64) << 32, key_env.0 as u64);
        let slot = (hash >> 50) as usize & (INFER_SLOTS - 1);
        let [expr, cached_env, cached_ls, entry] = self.infer_slots[slot];
        let mut memo = None;
        if expr == e.0 && cached_env == key_env.0 {
            if cached_ls == key_ls.0 {
                let i = entry as usize;
                let words = self.infer_memo.get(i);
                let ty = words[0];
                if ty != NONE && (infer_only || self.infer_memo_checked(words[1])) {
                    if !infer_only && !has_level_param {
                        self.infer_slots[slot] = [e.0, key_env.0, NONE, ty];
                    }
                    return Ok(V(ty));
                }
                memo = Some(i);
            } else if !has_level_param && cached_ls == NONE {
                return Ok(V(entry));
            }
        }
        self.infer_open_miss(e, node, d, (env, ls), (slot, memo), infer_only)
    }

    #[inline(never)]
    fn infer_open_miss(
        &mut self,
        e: ExprId,
        node: ExprNode,
        d: ExprData,
        (env, ls): (Env, Ls),
        (slot, memo): (usize, Option<usize>),
        infer_only: bool,
    ) -> R<V> {
        let key_env = if d.has_loose_bvars() { env } else { Env::NIL };
        let has_level_param = d.has_level_param();
        let key = if let Some(i) = memo {
            IKey::Memo(i)
        } else {
            let key_ls = if has_level_param { ls } else { Ls::ID };
            let key = self.infer_key(e, d, key_env, key_ls);
            if let IKey::Memo(i) = key {
                self.infer_slots[slot] = [e.0, key_env.0, key_ls.0, i as u32];
            }
            key
        };
        let ty = self.infer_memoized(e, node, d, (env, ls), infer_only, key)?;
        if !infer_only && !has_level_param {
            // This check survives declaration changes. The tagged slot
            // can return the type directly on subsequent exact hits.
            self.infer_slots[slot] = [e.0, key_env.0, NONE, ty.0];
        }
        Ok(ty)
    }

    fn infer_memoized(
        &mut self,
        e: ExprId,
        node: ExprNode,
        d: ExprData,
        (env, ls): (Env, Ls),
        infer_only: bool,
        key: IKey,
    ) -> R<V> {
        // A memo keyed by the term in its environment, without the entries
        // it does not use.
        let c = self.ikey_ty(key);
        if c != super::val::NONE && (infer_only || self.ikey_checked(key)) {
            return Ok(V(c));
        }
        // A closed term of the environment checked in an earlier
        // declaration (under the same universe parameters, if it has any)
        // only needs its type.
        // So is an open term checked under the same binders.
        let ctx = if infer_only || d.has_fvar() || ls != Ls::ID || self.st.is_local_expr(e) {
            None
        } else if !d.has_loose_bvars() {
            Some(0)
        } else {
            self.ctx(env)
        };
        let ck = if let Some(ctx) = ctx {
            let lk = if d.has_level_param() {
                self.lparams_key()
            } else {
                0
            };
            // One word: the term, its context and its universe parameters
            // (past what fits, not remembered).
            let k = (ctx < 1 << 20 && lk < 1 << 12)
                .then_some(e.0 as u64 | (ctx as u64) << 32 | lk << 52);
            if let Some(k) = k
                && self.checked_closed.contains(&k)
            {
                let r = if c != NONE {
                    V(c)
                } else if matches!(node, ExprNode::Lam(..)) {
                    // Inference trims a lambda's environment.
                    self.infer_node(e, node, env, ls, true)?
                } else {
                    // The memo key is already available.
                    let ty = self.infer_complex(e, node, env, ls, true)?;
                    self.ikey_set_ty(key, ty);
                    ty
                };
                self.ikey_set_checked(key, d.has_level_param());
                return Ok(r);
            }
            k
        } else {
            None
        };
        let r = self.infer_complex(e, node, env, ls, infer_only)?;
        if c == NONE {
            self.ikey_set_ty(key, r);
        }
        if !infer_only && !self.ikey_checked(key) {
            self.ikey_set_checked(key, d.has_level_param());
        }
        if let Some(k) = ck {
            self.checked_closed.insert(k);
        }
        Ok(if c == NONE { r } else { V(c) })
    }

    /// Terms with no free variables or universe parameters have one type
    /// per expression id. A slot tagged with `NONE` in the environment
    /// word stores the type itself and whether the term was checked.
    #[inline(always)]
    fn infer_closed(&mut self, e: ExprId, node: ExprNode, infer_only: bool) -> R<V> {
        let i = (e.0.wrapping_mul(0x9e37_79b9) >> (32 - INFER_SLOTS.ilog2())) as usize;
        let [expr, tag, checked, ty] = self.infer_slots[i];
        let cached = expr == e.0 && tag == NONE;
        if cached && (infer_only || checked != 0) {
            return Ok(V(ty));
        }
        self.infer_closed_miss(e, node, infer_only, i, cached.then_some(V(ty)))
    }

    #[inline(never)]
    fn infer_closed_miss(
        &mut self,
        e: ExprId,
        node: ExprNode,
        infer_only: bool,
        i: usize,
        cached: Option<V>,
    ) -> R<V> {
        let shared = !infer_only && !self.st.is_local_expr(e);
        let checked_before = shared && self.checked_closed.contains(&(e.0 as u64));
        let ty = if let Some(ty) = cached.filter(|_| checked_before) {
            ty
        } else {
            self.infer_complex(e, node, Env::NIL, Ls::ID, infer_only || checked_before)?
        };
        if shared && !checked_before {
            self.checked_closed.insert(e.0 as u64);
        }
        self.infer_slots[i] = [e.0, NONE, u32::from(!infer_only), ty.0];
        Ok(ty)
    }

    fn infer_complex(
        &mut self,
        e: ExprId,
        node: ExprNode,
        env: Env,
        ls: Ls,
        infer_only: bool,
    ) -> R<V> {
        match node {
            ExprNode::App(f, a) => self.infer_app(f, a, env, ls, infer_only),
            ExprNode::Lam(..) if infer_only => Ok(self.a.mk(Val::PiInfer(e, env, ls))),
            ExprNode::Lam(..) => self.check_lambda(e, env, ls),
            ExprNode::Pi(..) => self.infer_pi(e, env, ls, infer_only),
            ExprNode::Let(..) => self.infer_let(e, env, ls, infer_only),
            ExprNode::Proj(s, i, x) => {
                let xt = self.infer_term(x, env, ls, infer_only)?;
                let xv = self.thunk(x, env, ls);
                self.proj_type(xv, xt, s, i)
            }
            _ => unreachable!(),
        }
    }

    /// The key of `infer_term`'s memo for `e` in `env` under `ls`: by the
    /// entries `e` reads (`memo`), or else a thunk.
    fn infer_key(&mut self, e: ExprId, d: ExprData, env: Env, ls: Ls) -> IKey {
        let trim = self.key_is_trim(e);
        let range = d.loose_bvar_range();
        let n = range.min(self.a.env_len(env));
        if n <= INFER_MEMO_RANGE {
            let holes = if trim {
                d.unused_low() as u64
            } else {
                // Where terms are inferred again and again, sharper.
                !self.used_bvars(e)
            } & ((1u64 << n) - 1);
            if let Some(key) = self.small_infer_key(e, ls, env, range, n, holes) {
                return IKey::Memo(self.infer_memo.find_or_add_small(key));
            }
            let tuple = self.memo_tuple(env, range, n, holes);
            return IKey::Memo(self.infer_memo.find_or_add(e, ls, tuple));
        }
        IKey::Thunk(if trim {
            // The key is the term's thunk, likely made already.
            self.thunk_value(e, env, ls)
        } else {
            let kenv = self.key_env(env, e);
            self.a.mk(Val::Thunk(e, kenv, ls))
        })
    }

    fn ikey_ty(&self, k: IKey) -> u32 {
        match k {
            IKey::Memo(i) => self.infer_memo.get(i)[0],
            IKey::Thunk(t) => self.a.r(t).ty,
        }
    }

    fn ikey_set_ty(&mut self, k: IKey, ty: V) {
        match k {
            IKey::Memo(i) => self.infer_memo.set(i, 0, ty.0),
            IKey::Thunk(t) => self.a.rm(t).ty = ty.0,
        }
    }

    fn ikey_checked(&mut self, k: IKey) -> bool {
        match k {
            IKey::Memo(i) => self.infer_memo_checked(self.infer_memo.get(i)[1]),
            IKey::Thunk(t) => self.a.checked(t),
        }
    }

    #[inline]
    fn infer_memo_checked(&mut self, scope: u32) -> bool {
        scope == u32::MAX || (scope != 0 && u64::from(scope) == self.lparams_key())
    }

    /// Mark `k` checked; under the declaration's universe parameters only
    /// if `levels`.
    fn ikey_set_checked(&mut self, k: IKey, levels: bool) {
        match k {
            IKey::Memo(i) => {
                let scope = if levels {
                    let key = self.lparams_key();
                    if key >= u64::from(u32::MAX) {
                        return;
                    }
                    key as u32
                } else {
                    u32::MAX
                };
                self.infer_memo.set(i, 1, scope);
            }
            IKey::Thunk(t) => {
                self.a.set_checked(t);
                if levels {
                    self.level_checked.push(t);
                }
            }
        }
    }

    /// A constant's cache entry records whether its levels are closed.
    /// Read that entry before inspecting the levels.
    #[inline(always)]
    fn infer_const_expr(
        &mut self,
        e: ExprId,
        n: NameId,
        levels: LevelList,
        ls: Ls,
        infer_only: bool,
    ) -> R<V> {
        let i = (e.0.wrapping_mul(0x9e37_79b9) >> (32 - INFER_SLOTS.ilog2())) as usize;
        let [expr, limit, checked, ty] = self.infer_slots[i];
        let check_identity = ls == Ls::ID && !infer_only;
        if expr == e.0 {
            if limit == NONE {
                if infer_only || checked != 0 {
                    return Ok(V(ty));
                }
            } else if check_identity
                && limit <= self.limit
                && u64::from(checked) == self.lparams_key()
            {
                return Ok(V(ty));
            }
        }
        self.infer_const_expr_miss(e, n, levels, ls, infer_only, i)
    }

    #[inline(never)]
    fn infer_const_expr_miss(
        &mut self,
        e: ExprId,
        n: NameId,
        levels: LevelList,
        ls: Ls,
        infer_only: bool,
        i: usize,
    ) -> R<V> {
        if !self.st.list_has_param(levels) {
            let ty = self.infer_constant(n, levels, infer_only)?;
            self.infer_slots[i] = [e.0, NONE, u32::from(!infer_only), ty.0];
            return Ok(ty);
        }
        let levels = self.inst_list(levels, ls);
        let ty = self.infer_constant(n, levels, infer_only)?;
        if ls == Ls::ID
            && !infer_only
            && let Ok(params) = u32::try_from(self.lparams_key())
        {
            self.infer_slots[i] = [e.0, self.limit, params, ty.0];
        }
        Ok(ty)
    }

    fn infer_constant(&mut self, n: NameId, ls: LevelList, infer_only: bool) -> R<V> {
        let d = self.get(n)?;
        let nps = d.level_params.len();
        let nls = self.st.list(ls).len();
        if nps != nls {
            return err(format!(
                "incorrect number of universe levels parameters for '{}', #{nps} expected, #{nls} provided",
                self.st.show(n)
            ));
        }
        if !infer_only {
            if super::super::tc::Tc::decl_is_unsafe(&d) {
                return err(format!(
                    "invalid declaration, it uses unsafe declaration '{}'",
                    self.st.show(n)
                ));
            }
            if let DeclKind::Definition {
                safety: Safety::Partial,
                ..
            } = d.kind
            {
                return err(format!(
                    "invalid declaration, safe declaration must not contain partial declaration '{}'",
                    self.st.show(n)
                ));
            }
            for i in 0..nls {
                let l = self.st.list(ls)[i];
                self.check_level(l)?;
            }
        }
        Ok(self.const_type(&d, ls))
    }

    fn infer_app(&mut self, mut f: ExprId, a: ExprId, env: Env, ls: Ls, infer_only: bool) -> R<V> {
        // The arguments go on the `terms` stack, which calls below leave
        // as they found it. Inference reads them back from the top.
        let base = self.terms.len();
        self.terms.push(a);
        let head = loop {
            match self.st.node(f) {
                ExprNode::App(g, a) => {
                    self.terms.push(a);
                    f = g;
                }
                node => break node,
            }
        };
        let r = self.infer_app_args(f, head, base, env, ls, infer_only);
        self.terms.truncate(base);
        r
    }

    fn infer_app_args(
        &mut self,
        f: ExprId,
        head: ExprNode,
        base: usize,
        env: Env,
        ls: Ls,
        infer_only: bool,
    ) -> R<V> {
        let mut k = self.terms.len();
        let mut ft = self.infer_node(f, head, env, ls, infer_only)?;
        while k > base {
            let pi = self.ensure_pi(ft)?;
            let Val::Pi(t, mut pi_env, pi_ls) = pi else {
                let Val::PiInfer(t, pi_env, pi_ls) = pi else {
                    unreachable!()
                };
                let ExprNode::Lam(_, _, d, b) = self.st.node(t) else {
                    unreachable!()
                };
                k -= 1;
                let a = self.terms[k];
                if !infer_only {
                    self.check_arg(a, env, ls, (d, pi_env, pi_ls), false)?;
                }
                let pi_env = self.bind_arg(b, pi_env, a, env, ls);
                ft = self.infer_term(b, pi_env, pi_ls, true)?;
                continue;
            };
            // Through the Π binders of the term itself, without building
            // the values in between: the same values as instantiating one
            // binder at a time.
            let mut binder = self.st.node(t);
            loop {
                let ExprNode::Pi(_, _, d, b) = binder else {
                    unreachable!()
                };
                k -= 1;
                let a = self.terms[k];
                if !infer_only {
                    self.check_arg(a, env, ls, (d, pi_env, pi_ls), SYN_DOM)?;
                }
                pi_env = self.bind_arg(b, pi_env, a, env, ls);
                if k > base {
                    binder = self.st.node(b);
                    if matches!(binder, ExprNode::Pi(..)) {
                        continue;
                    }
                }
                ft = self.eval_codomain(b, pi_env, pi_ls);
                break;
            }
        }
        Ok(ft)
    }

    /// Extend a binder environment for its body. A closed body needs no
    /// environment; a body that only uses older entries needs a placeholder.
    #[inline]
    fn bind_arg(&mut self, body: ExprId, binder_env: Env, arg: ExprId, env: Env, ls: Ls) -> Env {
        let data = self.st.data(body);
        if !data.has_loose_bvars() {
            return Env::NIL;
        }
        let v = if data.may_use_bvar(0) {
            self.thunk(arg, env, ls)
        } else {
            self.hole()
        };
        self.a.cons(binder_env, v)
    }

    /// Check the argument `a` against its domain, trying syntax first for
    /// ordinary Π binders when that comparison is enabled.
    #[inline(always)]
    fn check_arg(
        &mut self,
        a: ExprId,
        env: Env,
        ls: Ls,
        (d, pi_env, pi_ls): (ExprId, Env, Ls),
        syn_dom: bool,
    ) -> R<()> {
        let node = self.st.node(a);
        let eager = if let (ExprNode::App(f, _), Some(n)) = (node, self.ext.eager_reduce)
            && let ExprNode::App(g, _) = self.st.node(f)
        {
            matches!(self.st.node(g), ExprNode::Const(m, _) if m == n)
        } else {
            false
        };
        if syn_dom && !matches!(node, ExprNode::Lam(..)) && !eager {
            let at = self.infer_node(a, node, env, ls, false)?;
            let same = if let ExprNode::Sort(level) = self.st.node(d)
                && let Val::Sort(actual) = self.a.get(at)
            {
                self.inst_level(level, pi_ls) == actual
            } else {
                self.syn_eq_term(at, d, pi_env, pi_ls)
            };
            if same {
                return Ok(());
            }
            return self.check_arg_def_eq(a, node, (env, ls), (d, pi_env, pi_ls), at);
        }
        self.check_arg_against(a, node, (env, ls), (d, pi_env, pi_ls), eager)
    }

    #[inline(never)]
    fn check_arg_def_eq(
        &mut self,
        a: ExprId,
        node: ExprNode,
        (env, ls): (Env, Ls),
        (d, pi_env, pi_ls): (ExprId, Env, Ls),
        at: V,
    ) -> R<()> {
        let dom = self.thunk(d, pi_env, pi_ls);
        if !self.is_def_eq(at, dom)? {
            return Err(self.arg_mismatch(a, node, env, ls, dom)?);
        }
        Ok(())
    }

    #[inline(never)]
    fn check_arg_against(
        &mut self,
        a: ExprId,
        node: ExprNode,
        (env, ls): (Env, Ls),
        (d, pi_env, pi_ls): (ExprId, Env, Ls),
        eager: bool,
    ) -> R<()> {
        if matches!(node, ExprNode::Lam(..))
            && !eager
            && let pi @ ExprNode::Pi(..) = self.st.node(d)
        {
            let expected = LambdaExpected::Pi(pi, pi_env, pi_ls);
            if self.check_lambda_against(a, node, env, ls, expected)? {
                return Ok(());
            }
            let dom = self.thunk(d, pi_env, pi_ls);
            return Err(self.arg_mismatch(a, node, env, ls, dom)?);
        }
        let dom = self.thunk(d, pi_env, pi_ls);
        let ok = if eager {
            let saved = std::mem::replace(&mut self.eager, true);
            let r = self.check_against_node(a, node, env, ls, dom);
            self.eager = saved;
            r?
        } else {
            self.check_against_node(a, node, env, ls, dom)?
        };
        if !ok {
            return Err(self.arg_mismatch(a, node, env, ls, dom)?);
        }
        Ok(())
    }

    /// Format a failed argument comparison.
    fn arg_mismatch(&mut self, a: ExprId, node: ExprNode, env: Env, ls: Ls, dom: V) -> R<KErr> {
        let av = self.thunk(a, env, ls);
        let at = self.infer_node(a, node, env, ls, true)?;
        Ok(KErr::new(format!(
            "application type mismatch: argument {} has type {} but is expected to have type {}",
            self.pp(av),
            self.pp(at),
            self.pp(dom)
        )))
    }

    /// Check `e` in `env` and whether its type is `expected`. A λ is
    /// checked against a Π binder by binder; anything else is inferred
    /// and compared.
    #[inline]
    pub fn check_against(&mut self, e: ExprId, env: Env, ls: Ls, expected: V) -> R<bool> {
        self.check_against_node(e, self.st.node(e), env, ls, expected)
    }

    #[inline]
    fn check_against_node(
        &mut self,
        e: ExprId,
        node: ExprNode,
        env: Env,
        ls: Ls,
        expected: V,
    ) -> R<bool> {
        if matches!(node, ExprNode::Lam(..)) {
            return self.check_lambda_against(e, node, env, ls, LambdaExpected::Value(expected));
        }
        let t = self.infer_node(e, node, env, ls, false)?;
        self.is_def_eq(t, expected)
    }

    /// Check a λ spine against successive Π binders.
    #[inline(never)]
    fn check_lambda_against(
        &mut self,
        mut e: ExprId,
        mut node: ExprNode,
        mut env: Env,
        ls: Ls,
        mut expected: LambdaExpected,
    ) -> R<bool> {
        let base = env;
        let result = (|| {
            while let ExprNode::Lam(bi, n, dom, body) = node {
                let (pi_node, pi_env, pi_ls) = match expected {
                    LambdaExpected::Pi(node, env, ls) => (node, env, ls),
                    LambdaExpected::Value(v) => {
                        let ex = self.force(v);
                        let mut binder = self.a.get(ex);
                        if !matches!(binder, Val::Pi(..) | Val::PiInfer(..)) {
                            let w = self.whnf(ex)?;
                            binder = self.a.get(w);
                        }
                        let (Val::Pi(t, env, ls) | Val::PiInfer(t, env, ls)) = binder else {
                            break;
                        };
                        (self.st.node(t), env, ls)
                    }
                };
                let (ExprNode::Pi(_, _, pi_dom, pi_body) | ExprNode::Lam(_, _, pi_dom, pi_body)) =
                    pi_node
                else {
                    unreachable!()
                };
                let dom_node = self.st.node(dom);
                let dv = if let ExprNode::BVar(i) = dom_node {
                    let Some(v) = self.a.lookup(env, i) else {
                        return err("type checker does not support loose bound variables");
                    };
                    let s = self.infer_value(v)?;
                    self.ensure_sort(s)?;
                    v
                } else {
                    let s = self.infer_node(dom, dom_node, env, ls, false)?;
                    self.ensure_sort(s)?;
                    self.thunk(dom, env, ls)
                };
                if !self.syn_eq_term(dv, pi_dom, pi_env, pi_ls) {
                    let ed = self.thunk(pi_dom, pi_env, pi_ls);
                    if dv != ed && !self.is_def_eq(dv, ed)? {
                        // Lean compares the domains first and fails there.
                        return Ok(false);
                    }
                }
                let x = self.push_fvar(n, dv, None, bi);
                let next = self.a.cons(env, x);
                self.ctx_push(env, dom, ls, next);
                env = next;
                e = body;
                node = self.st.node(body);
                let pi_env = self.bind_value(pi_body, pi_env, x);
                expected = if matches!(pi_node, ExprNode::Lam(..)) {
                    LambdaExpected::Value(self.infer_term(pi_body, pi_env, pi_ls, true)?)
                } else if matches!(node, ExprNode::Lam(..))
                    && let pi @ ExprNode::Pi(..) = self.st.node(pi_body)
                {
                    // The next comparison only needs the closure. Trimming
                    // and interning the Π would preserve these same bindings.
                    LambdaExpected::Pi(pi, pi_env, pi_ls)
                } else {
                    LambdaExpected::Value(self.eval(pi_body, pi_env, pi_ls))
                };
            }
            let LambdaExpected::Value(expected) = expected else {
                unreachable!()
            };
            let t = self.infer_node(e, node, env, ls, false)?;
            self.is_def_eq(t, expected)
        })();
        // Each step prepends one free variable. The environment records
        // the whole scope, including the binders opened before an error.
        while env != base {
            self.pop_fvar(self.a.env_head(env));
            env = self.a.env_tail(env);
        }
        result
    }

    fn check_lambda(&mut self, e: ExprId, env: Env, ls: Ls) -> R<V> {
        let mut cur = e;
        let mut env2 = env;
        let base = self.infer_opened.len();
        let result = (|| {
            while let ExprNode::Lam(bi, n, dom, body) = self.st.node(cur) {
                let s = self.infer_term(dom, env2, ls, false)?;
                self.ensure_sort(s)?;
                env2 = self.open_inferred_binder((bi, n, dom, body), env2, ls);
                cur = body;
            }
            self.infer_term(cur, env2, ls, false)
        })();
        self.close_inferred_binders(base);
        result?;
        let d = self.st.data(e);
        let env = self.trim_prune(env, d);
        let ls = if d.has_level_param() { ls } else { Ls::ID };
        Ok(self.a.mk(Val::PiInfer(e, env, ls)))
    }

    /// Open a binder after checking its domain. An unused variable needs
    /// only a placeholder if the body reads older variables.
    fn open_inferred_binder(
        &mut self,
        (bi, name, dom, body): (BinderInfo, NameId, ExprId, ExprId),
        env: Env,
        ls: Ls,
    ) -> Env {
        let data = self.st.data(body);
        if !data.has_loose_bvars() {
            return Env::NIL;
        }
        if !data.may_use_bvar(0) {
            // This environment does not describe a context of binders.
            let hole = self.hole();
            return self.a.cons(env, hole);
        }
        let dv = self.thunk(dom, env, ls);
        let x = self.push_fvar(name, dv, None, bi);
        self.infer_opened.push(x);
        let next = self.a.cons(env, x);
        self.ctx_push(env, dom, ls, next);
        next
    }

    fn close_inferred_binders(&mut self, base: usize) {
        while self.infer_opened.len() > base {
            let x = self.infer_opened.pop().unwrap();
            self.pop_fvar(x);
        }
    }

    fn infer_pi(&mut self, e: ExprId, env: Env, ls: Ls, infer_only: bool) -> R<V> {
        let mut cur = e;
        let mut env2 = env;
        let opened = self.infer_opened.len();
        let sorts = self.infer_sorts.len();
        let result = (|| {
            while let ExprNode::Pi(bi, n, dom, body) = self.st.node(cur) {
                let s = self.infer_term(dom, env2, ls, infer_only)?;
                let sort = self.ensure_sort(s)?;
                self.infer_sorts.push(sort);
                env2 = self.open_inferred_binder((bi, n, dom, body), env2, ls);
                cur = body;
            }
            let s = self.infer_term(cur, env2, ls, infer_only)?;
            self.ensure_sort(s)
        })();
        self.close_inferred_binders(opened);
        let r = result.map(|mut r| {
            for &u in self.infer_sorts[sorts..].iter().rev() {
                r = univ::mk_imax(&mut self.st, u, r);
            }
            r
        });
        self.infer_sorts.truncate(sorts);
        Ok(self.a.mk(Val::Sort(r?)))
    }

    fn infer_let(&mut self, e: ExprId, env: Env, ls: Ls, infer_only: bool) -> R<V> {
        let mut cur = e;
        let mut env2 = env;
        while let ExprNode::Let(h, body) = self.st.node(cur) {
            let lb = self.st.let_binder(h);
            if !infer_only {
                let s = self.infer_term(lb.ty, env2, ls, false)?;
                self.ensure_sort(s)?;
                let tv = self.thunk(lb.ty, env2, ls);
                let vt = self.infer_term(lb.value, env2, ls, false)?;
                if !self.is_def_eq(vt, tv)? {
                    let vv = self.thunk(lb.value, env2, ls);
                    let _ = vv;
                    return err(format!(
                        "type mismatch at let '{}': value has type {} but is expected to have type {}",
                        self.st.show(lb.name),
                        self.pp(vt),
                        self.pp(tv)
                    ));
                }
            }
            let v = self.thunk(lb.value, env2, ls);
            env2 = self.a.cons(env2, v);
            cur = body;
        }
        self.infer_term(cur, env2, ls, infer_only)
    }

    // ---- declarations ----

    /// Lean's `check_constant_val` for a declaration's type.
    pub fn check_type(&mut self, ty: ExprId) -> R<()> {
        self.check_type_sort(ty).map(|_| ())
    }

    pub(in crate::check) fn check_type_sort(&mut self, ty: ExprId) -> R<LevelId> {
        let s = self.infer_term(ty, Env::NIL, Ls::ID, false)?;
        self.ensure_sort(s)
    }

    pub fn check_is_prop(&mut self, ty: ExprId) -> R<bool> {
        let t = self.thunk(ty, Env::NIL, Ls::ID);
        self.is_prop(t)
    }

    /// Check that `value` has type `ty`.
    pub fn check_value(&mut self, value: ExprId, ty: ExprId) -> R<()> {
        let tv = self.thunk(ty, Env::NIL, Ls::ID);
        if !self.check_against(value, Env::NIL, Ls::ID, tv)? {
            return self.value_type_mismatch(value, tv);
        }
        Ok(())
    }

    /// Check a value against its already checked declaration type.
    pub(in crate::check) fn check_decl_value(&mut self, value: ExprId, ty: ExprId) -> R<()> {
        if !self.check_decl_value_type(value, ty)? {
            let tv = self.thunk(ty, Env::NIL, Ls::ID);
            return self.value_type_mismatch(value, tv);
        }
        Ok(())
    }

    fn value_type_mismatch(&mut self, value: ExprId, expected: V) -> R<()> {
        let given = self.infer_term(value, Env::NIL, Ls::ID, true)?;
        err(format!(
            "declaration type mismatch, value has type {} but is expected to have type {}",
            self.pp(given),
            self.pp(expected)
        ))
    }

    fn check_decl_value_type(&mut self, mut value: ExprId, mut ty: ExprId) -> R<bool> {
        let mut env = Env::NIL;
        let opened = self.infer_opened.len();
        while let ExprNode::Lam(bi, n, dom, body) = self.st.node(value)
            && let ExprNode::Pi(_, _, expected_dom, expected_body) = self.st.node(ty)
            && dom == expected_dom
        {
            // Both annotations are the same term in the same environment.
            // The declaration type check already verified the domain.
            let dv = self.thunk(dom, env, Ls::ID);
            let x = self.push_fvar(n, dv, None, bi);
            let next = self.a.cons(env, x);
            self.ctx_push(env, dom, Ls::ID, next);
            self.infer_opened.push(x);
            env = next;
            value = body;
            ty = expected_body;
        }
        let expected = self.thunk(ty, env, Ls::ID);
        let result = self.check_against(value, env, Ls::ID, expected);
        self.close_inferred_binders(opened);
        result
    }

    /// The binder info of free variable `k`, for printing.
    pub fn fvar_bi(&self, k: u32) -> BinderInfo {
        self.fvars[k as usize].bi
    }
}
