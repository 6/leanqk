//! Type inference and checking. Terms are inferred in an environment of
//! values for their loose bound variables; types are values. Checking a
//! λ against a known Π type goes binder by binder (Lean infers the λ's
//! type and compares it with the Π, which makes the same comparisons).

use crate::env::{DeclKind, Safety};
use crate::expr::{BinderInfo, ExprId, ExprNode};
use crate::level::{LevelId, LevelList};
use crate::name::NameId;

use super::super::tc::{KErr, NAT_MAX_BYTES, R};
use super::super::univ;
use super::val::{Elim, Env, Ls, Sp, V, Val};
use super::{BOTTOM, Nbe};

fn err<T>(msg: impl Into<String>) -> R<T> {
    Err(KErr::new(msg.into()))
}

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
        match self.a.get(v) {
            Val::Lam(t, env, ls) | Val::Pi(t, env, ls) => {
                let (ExprNode::Lam(_, _, _, b) | ExprNode::Pi(_, _, _, b)) = self.st.node(t) else {
                    unreachable!()
                };
                let env2 = self.a.cons(env, x);
                Ok(self.eval(b, env2, ls))
            }
            Val::PiInfer(t, env, ls) => {
                let ExprNode::Lam(_, _, _, b) = self.st.node(t) else {
                    unreachable!()
                };
                let env2 = self.a.cons(env, x);
                self.infer_term(b, env2, ls, true)
            }
            _ => unreachable!(),
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

    pub fn ensure_pi(&mut self, v: V) -> R<V> {
        let v = self.force(v);
        if matches!(self.a.get(v), Val::Pi(..) | Val::PiInfer(..)) {
            return Ok(v);
        }
        let w = self.whnf(v)?;
        if matches!(self.a.get(w), Val::Pi(..) | Val::PiInfer(..)) {
            Ok(w)
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
    pub fn infer_value(&mut self, v: V) -> R<V> {
        let c = self.a.r(v).ty;
        if c != super::val::NONE {
            return Ok(V(c));
        }
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
                let h = self.cnst(n, l);
                self.apply_type(h, t, sp)?
            }
            Val::FVar(k, sp) => {
                if k == BOTTOM {
                    return err("ill-typed term met during reduction");
                }
                let t = self.fvars[k as usize].ty;
                let h = self.a.mk(Val::FVar(k, Sp::NIL));
                self.apply_type(h, t, sp)?
            }
        };
        self.a.rm(v).ty = r.0;
        Ok(r)
    }

    /// The type of `head` applied to the eliminations of `sp`, given the
    /// type `t` of `head`.
    fn apply_type(&mut self, head: V, mut t: V, sp: Sp) -> R<V> {
        if sp == Sp::NIL {
            return Ok(t);
        }
        let mut es = self.take_elims();
        self.a.elims(sp, &mut es);
        let mut cur = head;
        let mut i = 0;
        while i < es.len() {
            match es[i] {
                Elim::Arg(a) => {
                    t = self.ensure_pi(t)?;
                    t = self.instantiate(t, a)?;
                    cur = self.apply(cur, a);
                }
                Elim::Proj(s, j) => {
                    t = self.proj_type(cur, t, s, j)?;
                    cur = self.proj(cur, s, j);
                }
            }
            i += 1;
        }
        self.put_elims(es);
        Ok(t)
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
        let mut args = Vec::new();
        if !self.a.args(sp, &mut args)
            || ctors.len() != 1
            || args.len() != (num_params + num_indices) as usize
        {
            return Err(self.proj_error(x, sname, idx));
        }
        let ctor = self.st.name_list(ctors)[0];
        let c_decl = self.get(ctor)?;
        let mut r = self.const_type(&c_decl, i_lvls);
        for &a in args.iter().take(num_params as usize) {
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
        let node = self.st.node(e);
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
                let lv = self.inst_list(lv, ls);
                return self.infer_constant(n, lv, infer_only);
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
        // A memo keyed by the term in its environment, without the entries
        // it does not use.
        let d = self.st.data(e);
        let key = if self.key_is_trim(e) {
            // The key is the term's thunk, likely made already.
            self.thunk_value(e, env, ls)
        } else {
            let kenv = self.key_env(env, e);
            let kls = if d.has_level_param() { ls } else { Ls::ID };
            self.a.mk(Val::Thunk(e, kenv, kls))
        };
        let c = self.a.r(key).ty;
        if c != super::val::NONE && (infer_only || self.a.checked(key)) {
            return Ok(V(c));
        }
        // A closed term of the environment checked in an earlier
        // declaration (under the same universe parameters, if it has any)
        // only needs its type.
        // So is an open term checked under the same binders.
        let ctx =
            if infer_only || d.has_fvar() || ls != Ls::ID || super::super::store::is_local(e.0) {
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
                let r = self.infer_term(e, env, ls, true)?;
                self.a.set_checked(key);
                if d.has_level_param() {
                    self.level_checked.push(key);
                }
                return Ok(r);
            }
            k
        } else {
            None
        };
        let r = match node {
            ExprNode::App(..) => self.infer_app(e, env, ls, infer_only)?,
            ExprNode::Lam(..) => self.check_lambda(e, env, ls)?,
            ExprNode::Pi(..) => self.infer_pi(e, env, ls, infer_only)?,
            ExprNode::Let(..) => self.infer_let(e, env, ls, infer_only)?,
            ExprNode::Proj(s, i, x) => {
                let xt = self.infer_term(x, env, ls, infer_only)?;
                let xv = self.thunk(x, env, ls);
                self.proj_type(xv, xt, s, i)?
            }
            _ => unreachable!(),
        };
        if c == super::val::NONE {
            self.a.rm(key).ty = r.0;
        }
        if !infer_only && !self.a.checked(key) {
            self.a.set_checked(key);
            if d.has_level_param() {
                self.level_checked.push(key);
            }
        }
        if let Some(k) = ck {
            self.checked_closed.insert(k);
        }
        Ok(if c == super::val::NONE { r } else { V(c) })
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

    fn is_eager_reduce(&self, e: ExprId) -> bool {
        match self.ext.eager_reduce {
            Some(n) => {
                self.st.nargs(e) == 2
                    && matches!(self.st.node(self.st.head(e)), ExprNode::Const(m, _) if m == n)
            }
            None => false,
        }
    }

    fn infer_app(&mut self, e: ExprId, env: Env, ls: Ls, infer_only: bool) -> R<V> {
        // The arguments go on the `terms` stack, which calls below leave
        // as they found it (or with more on top, after an error).
        let base = self.terms.len();
        let mut f = e;
        while let ExprNode::App(g, a) = self.st.node(f) {
            self.terms.push(a);
            f = g;
        }
        let n = self.terms.len() - base;
        self.terms[base..].reverse();
        let r = self.infer_app_args(f, base, n, env, ls, infer_only);
        self.terms.truncate(base);
        r
    }

    fn infer_app_args(
        &mut self,
        f: ExprId,
        base: usize,
        n: usize,
        env: Env,
        ls: Ls,
        infer_only: bool,
    ) -> R<V> {
        let mut ft = self.infer_term(f, env, ls, infer_only)?;
        let mut k = base;
        while k < base + n {
            ft = self.ensure_pi(ft)?;
            let Val::Pi(mut t, mut pi_env, pi_ls) = self.a.get(ft) else {
                let a = self.terms[k];
                let av = self.thunk(a, env, ls);
                if !infer_only {
                    let dom = self.binder_dom(ft);
                    self.check_arg(a, env, ls, dom)?;
                }
                ft = self.instantiate(ft, av)?;
                k += 1;
                continue;
            };
            // Through the Π binders of the term itself, without building
            // the values in between: the same values as instantiating one
            // binder at a time.
            loop {
                let ExprNode::Pi(_, _, d, b) = self.st.node(t) else {
                    unreachable!()
                };
                let a = self.terms[k];
                if !infer_only {
                    let dom = self.thunk(d, pi_env, pi_ls);
                    self.check_arg(a, env, ls, dom)?;
                }
                // The argument's value only if the codomain may read it.
                let av = if self.st.data(b).may_use_bvar(0) {
                    self.thunk(a, env, ls)
                } else {
                    self.hole()
                };
                pi_env = self.a.cons(pi_env, av);
                k += 1;
                if k < base + n && matches!(self.st.node(b), ExprNode::Pi(..)) {
                    t = b;
                } else {
                    ft = self.eval(b, pi_env, pi_ls);
                    break;
                }
            }
        }
        Ok(ft)
    }

    /// Check the argument `a` against the domain `dom`.
    fn check_arg(&mut self, a: ExprId, env: Env, ls: Ls, dom: V) -> R<()> {
        let ok = if self.is_eager_reduce(a) {
            let saved = std::mem::replace(&mut self.eager, true);
            let r = self.check_against(a, env, ls, dom);
            self.eager = saved;
            r?
        } else {
            self.check_against(a, env, ls, dom)?
        };
        if !ok {
            let av = self.thunk(a, env, ls);
            let at = self.infer_term(a, env, ls, true)?;
            return err(format!(
                "application type mismatch: argument {} has type {} but is expected to have type {}",
                self.pp(av),
                self.pp(at),
                self.pp(dom)
            ));
        }
        Ok(())
    }

    /// Check `e` in `env` and whether its type is `expected`. A λ is
    /// checked against a Π binder by binder; anything else is inferred
    /// and compared.
    #[inline]
    pub fn check_against(&mut self, e: ExprId, env: Env, ls: Ls, expected: V) -> R<bool> {
        if matches!(self.st.node(e), ExprNode::Lam(..)) {
            return self.check_lambda_against(e, env, ls, expected);
        }
        let t = self.infer_term(e, env, ls, false)?;
        self.is_def_eq(t, expected)
    }

    /// `check_against` of a λ.
    #[inline(never)]
    fn check_lambda_against(&mut self, e: ExprId, env: Env, ls: Ls, expected: V) -> R<bool> {
        if let ExprNode::Lam(bi, n, dom, body) = self.st.node(e) {
            let ex = self.force(expected);
            let ex = if matches!(self.a.get(ex), Val::Pi(..) | Val::PiInfer(..)) {
                Some(ex)
            } else {
                let w = self.whnf(ex)?;
                matches!(self.a.get(w), Val::Pi(..) | Val::PiInfer(..)).then_some(w)
            };
            if let Some(ex) = ex {
                let s = self.infer_term(dom, env, ls, false)?;
                self.ensure_sort(s)?;
                let dv = self.thunk(dom, env, ls);
                let ed = self.binder_dom(ex);
                if dv != ed && !self.is_def_eq(dv, ed)? {
                    // Lean compares the domains first and fails there.
                    return Ok(false);
                }
                let x = self.push_fvar(n, dv, None, bi);
                let env2 = self.a.cons(env, x);
                self.ctx_push(env, dom, ls, env2);
                let ebody = self.instantiate(ex, x)?;
                let r = self.check_against(body, env2, ls, ebody);
                self.pop_fvar(x);
                return r;
            }
        }
        let t = self.infer_term(e, env, ls, false)?;
        self.is_def_eq(t, expected)
    }

    fn check_lambda(&mut self, e: ExprId, env: Env, ls: Ls) -> R<V> {
        let mut cur = e;
        let mut env2 = env;
        let mut opened = Vec::new();
        while let ExprNode::Lam(bi, n, dom, body) = self.st.node(cur) {
            let s = self.infer_term(dom, env2, ls, false)?;
            self.ensure_sort(s)?;
            let dv = self.thunk(dom, env2, ls);
            let x = self.push_fvar(n, dv, None, bi);
            opened.push(x);
            let env3 = self.a.cons(env2, x);
            self.ctx_push(env2, dom, ls, env3);
            env2 = env3;
            cur = body;
        }
        self.infer_term(cur, env2, ls, false)?;
        for &x in opened.iter().rev() {
            self.pop_fvar(x);
        }
        let d = self.st.data(e);
        let env = self.trim_prune(env, d);
        let ls = if d.has_level_param() { ls } else { Ls::ID };
        Ok(self.a.mk(Val::PiInfer(e, env, ls)))
    }

    fn infer_pi(&mut self, e: ExprId, env: Env, ls: Ls, infer_only: bool) -> R<V> {
        let mut cur = e;
        let mut env2 = env;
        let mut us = Vec::new();
        let mut opened = Vec::new();
        while let ExprNode::Pi(bi, n, dom, body) = self.st.node(cur) {
            let s = self.infer_term(dom, env2, ls, infer_only)?;
            us.push(self.ensure_sort(s)?);
            let dv = self.thunk(dom, env2, ls);
            let x = self.push_fvar(n, dv, None, bi);
            opened.push(x);
            let env3 = self.a.cons(env2, x);
            self.ctx_push(env2, dom, ls, env3);
            env2 = env3;
            cur = body;
        }
        let s = self.infer_term(cur, env2, ls, infer_only)?;
        let mut r = self.ensure_sort(s)?;
        for &x in opened.iter().rev() {
            self.pop_fvar(x);
        }
        for &u in us.iter().rev() {
            r = univ::mk_imax(&mut self.st, u, r);
        }
        Ok(self.a.mk(Val::Sort(r)))
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
        let s = self.infer_term(ty, Env::NIL, Ls::ID, false)?;
        self.ensure_sort(s)?;
        Ok(())
    }

    pub fn check_is_prop(&mut self, ty: ExprId) -> R<bool> {
        let t = self.thunk(ty, Env::NIL, Ls::ID);
        self.is_prop(t)
    }

    /// Check that `value` has type `ty`.
    pub fn check_value(&mut self, value: ExprId, ty: ExprId) -> R<()> {
        let tv = self.thunk(ty, Env::NIL, Ls::ID);
        if !self.check_against(value, Env::NIL, Ls::ID, tv)? {
            let vt = self.infer_term(value, Env::NIL, Ls::ID, true)?;
            return err(format!(
                "declaration type mismatch, value has type {} but is expected to have type {}",
                self.pp(vt),
                self.pp(tv)
            ));
        }
        Ok(())
    }

    /// The binder info of free variable `k`, for printing.
    pub fn fvar_bi(&self, k: u32) -> BinderInfo {
        self.fvars[k as usize].bi
    }
}
