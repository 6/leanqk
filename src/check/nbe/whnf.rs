//! Weak head normal forms: `whnf_core` (projections, recursors, quotients,
//! let-bound variables; β is done by evaluation) and `whnf` (also δ and the
//! `Nat` operations), as in `type_checker.cpp`.

use num_bigint::BigUint;

use crate::env::{Decl, DeclKind};
use crate::level::{LevelId, LevelList};
use crate::name::NameId;

use super::super::ext::NatOp;
use super::super::tc::{KErr, NAT_MAX_BYTES, R};
use super::val::{Elim, Sp, V, Val};
use super::{BOTTOM, Nbe};

impl Nbe<'_> {
    /// The value bound to the let-variable `k`, if it is one.
    #[inline]
    fn let_value(&self, k: u32) -> Option<V> {
        if k == BOTTOM {
            return None;
        }
        self.fvars[k as usize].val
    }

    pub fn whnf_core(&mut self, v: V, cheap_rec: bool, cheap_proj: bool) -> R<V> {
        let v = self.force(v);
        match self.a.get(v) {
            Val::Const(_, _, sp) if sp != Sp::NIL => {}
            Val::FVar(k, sp) => {
                return match self.let_value(k) {
                    Some(x) => {
                        let r = self.apply_spine(x, sp);
                        self.whnf_core(r, cheap_rec, cheap_proj)
                    }
                    None => Ok(v),
                };
            }
            _ => return Ok(v),
        }
        let full = !cheap_rec && !cheap_proj;
        if full {
            let c = self.a.r(v).whnf_core;
            if c != super::val::NONE {
                return Ok(V(c));
            }
        }
        let r = self.whnf_core_app(v, cheap_rec, cheap_proj)?;
        if full {
            self.a.rm(v).whnf_core = r.0;
        }
        Ok(r)
    }

    fn whnf_core_app(&mut self, v: V, cheap_rec: bool, cheap_proj: bool) -> R<V> {
        let Val::Const(c, l, sp) = self.a.get(v) else {
            unreachable!()
        };
        let mut es = self.take_elims();
        self.a.elims(sp, &mut es);
        let p = es
            .iter()
            .position(|e| matches!(e, Elim::Proj(..)))
            .unwrap_or(es.len());
        let mut args = Vec::with_capacity(p);
        for e in &es[..p] {
            let Elim::Arg(a) = *e else { unreachable!() };
            args.push(a);
        }
        let r = if let Some(r) = self.reduce_recursor(c, l, &args, cheap_rec, cheap_proj)? {
            let r = self.apply_elims(r, &es[p..]);
            self.whnf_core(r, cheap_rec, cheap_proj)?
        } else if p < es.len() {
            let Elim::Proj(s, i) = es[p] else {
                unreachable!()
            };
            let pre = self.a.sp_prefix(sp, p as u32);
            let x = self.a.mk(Val::Const(c, l, pre));
            let x = if cheap_proj {
                self.whnf_core(x, cheap_rec, cheap_proj)?
            } else {
                self.whnf(x)?
            };
            match self.reduce_proj_core(x, s, i)? {
                Some(f) => {
                    let r = self.apply_elims(f, &es[p + 1..]);
                    self.whnf_core(r, cheap_rec, cheap_proj)?
                }
                None => v,
            }
        } else {
            v
        };
        self.put_elims(es);
        Ok(r)
    }

    /// Lean's `reduce_proj_core`, on a struct already in whnf.
    pub fn reduce_proj_core(&mut self, mut c: V, s: NameId, i: u32) -> R<Option<V>> {
        if let Val::Str(_) = self.a.get(c) {
            let x = self.string_lit_to_constructor(c)?;
            c = self.whnf(x)?;
        }
        Ok(self.ctor_field(c, s, i))
    }

    fn reduce_recursor(
        &mut self,
        c: NameId,
        l: LevelList,
        args: &[V],
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> R<Option<V>> {
        if let Some(r) = self.quot_reduce_rec(c, args)? {
            return Ok(Some(r));
        }
        self.inductive_reduce_rec(c, l, args, cheap_rec, cheap_proj)
    }

    fn quot_reduce_rec(&mut self, f: NameId, args: &[V]) -> R<Option<V>> {
        let Some(q) = self.ext.quot.as_ref() else {
            return Ok(None);
        };
        let (mk_pos, arg_pos) = if f == q.lift {
            (5, 3)
        } else if f == q.ind {
            (4, 3)
        } else {
            return Ok(None);
        };
        let qmk = q.mk;
        match self.find(f) {
            Some(Decl {
                kind: DeclKind::Quot { .. },
                ..
            }) => {}
            _ => return Ok(None),
        }
        if args.len() <= mk_pos {
            return Ok(None);
        }
        let mk = self.whnf(args[mk_pos])?;
        let Val::Const(n, _, msp) = self.a.get(mk) else {
            return Ok(None);
        };
        let mut margs = Vec::new();
        if n != qmk || !self.a.args(msp, &mut margs) || margs.len() != 3 {
            return Ok(None);
        }
        let r = self.apply(args[arg_pos], margs[2]);
        Ok(Some(self.apply_all(r, &args[mk_pos + 1..])))
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
                crate::expr::ExprNode::Pi(_, _, _, b) => t = b,
                _ => return None,
            }
        }
        let crate::expr::ExprNode::Pi(_, _, dom, _) = self.st.node(t) else {
            return None;
        };
        let (n, _) = self.st.head_const(dom)?;
        self.major_induct.insert(rec, n);
        Some(n)
    }

    fn rec_whnf(&mut self, v: V, cheap_rec: bool, cheap_proj: bool) -> R<V> {
        if cheap_rec {
            self.whnf_core(v, cheap_rec, cheap_proj)
        } else {
            self.whnf(v)
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

    /// The constant at the head of `v` (forced), with its spine.
    pub fn head_const(&mut self, v: V) -> Option<(NameId, LevelList, Sp)> {
        let v = self.force(v);
        match self.a.get(v) {
            Val::Const(n, l, sp) => Some((n, l, sp)),
            _ => None,
        }
    }

    fn is_constructor_app(&mut self, v: V) -> bool {
        match self.head_const(v) {
            Some((n, _, _)) => matches!(
                self.find(n),
                Some(Decl {
                    kind: DeclKind::Constructor { .. },
                    ..
                })
            ),
            None => false,
        }
    }

    pub fn first_ctor(&self, i: NameId) -> Option<NameId> {
        match self.find(i)?.kind {
            DeclKind::Inductive { ctors, .. } => self.st.name_list(ctors).first().copied(),
            _ => None,
        }
    }

    fn ctor_when_k(&mut self, induct: NameId, nparams: u32, e: V) -> R<V> {
        let t = self.infer_value(e)?;
        let app_type = self.whnf(t)?;
        let Val::Const(i_name, i_lvls, sp) = self.a.get(app_type) else {
            return Ok(e);
        };
        if i_name != induct {
            return Ok(e);
        }
        let Some(c) = self.first_ctor(i_name) else {
            return Ok(e);
        };
        let mut args = Vec::new();
        if !self.a.args(sp, &mut args) || args.len() < nparams as usize {
            return Ok(e);
        }
        let c = self.cnst(c, i_lvls);
        let new_c = self.apply_all(c, &args[..nparams as usize]);
        let new_t = self.infer_value(new_c)?;
        if !self.is_def_eq(app_type, new_t)? {
            return Ok(e);
        }
        Ok(new_c)
    }

    /// `mk params (e.1) … (e.n)` for `e` of the structure type `e_type`.
    pub fn expand_eta_struct(&mut self, e_type: V, e: V) -> R<V> {
        let Val::Const(i_name, i_lvls, sp) = self.a.get(e_type) else {
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
        let mut args = Vec::new();
        if !self.a.args(sp, &mut args) {
            return Ok(e);
        }
        let np = (num_params as usize).min(args.len());
        let c = self.cnst(c, i_lvls);
        let mut r = self.apply_all(c, &args[..np]);
        for k in 0..num_fields {
            let p = self.proj(e, i_name, k);
            r = self.apply(r, p);
        }
        Ok(r)
    }

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

    fn ctor_when_structure(&mut self, rec: &Decl, induct: NameId, e: V) -> R<V> {
        if !self.is_non_rec_structure(induct) || self.is_constructor_app(e) {
            return Ok(e);
        }
        let ef = self.force(e);
        if matches!(self.a.get(ef), Val::Str(_)) {
            return Ok(e);
        }
        let t = self.infer_value(e)?;
        let e_type = self.whnf(t)?;
        match self.head_const(e_type) {
            Some((n, _, _)) if n == induct => {}
            _ => return Ok(e),
        }
        // Divergence (corpus/divergences.md), as in `tc.rs`.
        if !self.is_large_elim(rec) {
            return Ok(e);
        }
        self.expand_eta_struct(e_type, e)
    }

    fn inductive_reduce_rec(
        &mut self,
        rec_name: NameId,
        rec_lvls: LevelList,
        args: &[V],
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> R<Option<V>> {
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
        major = self.ctor_when_structure(&d, induct, major)?;
        major = self.rec_whnf(major, cheap_rec, cheap_proj)?;
        match self.a.get(major) {
            Val::Nat(..) | Val::NatBig(_) => {
                major = self.nat_lit_to_constructor(major)?;
            }
            Val::Str(_) => {
                let x = self.string_lit_to_constructor(major)?;
                major = self.whnf(x)?;
            }
            _ => {}
        }
        let Val::Const(ctor, _, msp) = self.a.get(major) else {
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
        let mut margs = Vec::new();
        if !self.a.args(msp, &mut margs) {
            return Ok(None);
        }
        let nfields = rule.nfields as usize;
        if nfields > margs.len() {
            return Ok(None);
        }
        if self.st.list(rec_lvls).len() != d.level_params.len() {
            return Ok(None);
        }
        let ls = self.decl_ls(&d, rec_lvls);
        let mut rhs = self.eval(rule.rhs, super::val::Env::NIL, ls);
        let pmm = (num_params + num_motives + num_minors) as usize;
        rhs = self.apply_all(rhs, &args[..pmm]);
        rhs = self.apply_all(rhs, &margs[margs.len() - nfields..]);
        rhs = self.apply_all(rhs, &args[major_idx + 1..]);
        Ok(Some(rhs))
    }

    /// `n` as `Nat.zero` or `Nat.succ (n - 1)`.
    pub fn nat_lit_to_constructor(&mut self, v: V) -> R<V> {
        let Some(n) = self.nat_value(v) else {
            unreachable!()
        };
        let (Some(zero), Some(succ)) = (self.ext.nat_zero, self.ext.nat_succ) else {
            return Err(KErr("a `Nat` literal needs the prelude's `Nat`".into()));
        };
        if n == BigUint::ZERO {
            return Ok(self.cnst(zero, LevelList::EMPTY));
        }
        let p = self.nat(n - 1u32);
        let s = self.cnst(succ, LevelList::EMPTY);
        Ok(self.apply(s, p))
    }

    /// `String.ofList [Char.ofNat c₁, …]` for a string literal.
    pub fn string_lit_to_constructor(&mut self, v: V) -> R<V> {
        let Val::Str(s) = self.a.get(v) else {
            unreachable!()
        };
        let Some(x) = self.ext.string() else {
            return Err(KErr(
                "a `String` literal needs the prelude's `String`".into(),
            ));
        };
        let x = *x;
        let chars: Vec<u32> = self.st.str(s).chars().map(|c| c as u32).collect();
        let zero = LevelList::EMPTY;
        let char_ty = self.cnst(x.char, zero);
        let zero_list = self.st.mk_list(&[LevelId::ZERO]);
        let nil = self.cnst(x.list_nil, zero_list);
        let cons = self.cnst(x.list_cons, zero_list);
        let nil = self.apply(nil, char_ty);
        let cons = self.apply(cons, char_ty);
        let of_nat = self.cnst(x.char_of_nat, zero);
        let mut r = nil;
        for &c in chars.iter().rev() {
            let n = self.nat_u64(c as u64);
            let ch = self.apply(of_nat, n);
            let a = self.apply(cons, ch);
            r = self.apply(a, r);
        }
        let of_list = self.cnst(x.of_list, zero);
        Ok(self.apply(of_list, r))
    }

    /// The definition at the head of `v`, if `v` can be unfolded.
    pub fn is_delta(&mut self, v: V) -> Option<Decl> {
        let v = self.force(v);
        let Val::Const(n, ls, sp) = self.a.get(v) else {
            return None;
        };
        if self.a.sp_has_proj(sp) {
            return None;
        }
        let d = self.find(n)?;
        Self::decl_value(&d)?;
        (self.st.list(ls).len() == d.level_params.len()).then_some(d)
    }

    pub fn unfold_definition(&mut self, v: V) -> Option<V> {
        let v = self.force(v);
        let m = self.a.r(v).delta;
        if m != super::val::NONE {
            return Some(V(m));
        }
        let d = self.is_delta(v)?;
        let value = Self::decl_value(&d)?;
        let Val::Const(_, ls, sp) = self.a.get(v) else {
            unreachable!()
        };
        let body = self.const_value(&d, value, ls);
        let r = self.apply_spine(body, sp);
        self.a.rm(v).delta = r.0;
        Some(r)
    }

    /// The value of a literal or of `Nat.zero`.
    fn nat_lit_ext(&self, v: V) -> Option<BigUint> {
        match self.a.get(v) {
            Val::Const(n, ls, Sp::NIL)
                if Some(n) == self.ext.nat_zero && ls == LevelList::EMPTY =>
            {
                Some(BigUint::ZERO)
            }
            _ => self.nat_value(v),
        }
    }

    fn nat_size_ok(v: &BigUint) -> R<()> {
        if v.bits().div_ceil(8) > NAT_MAX_BYTES {
            return Err(KErr(
                "the kernel refused a `Nat` numeral because its size exceeds the maximum".into(),
            ));
        }
        Ok(())
    }

    fn mk_bool(&mut self, b: bool) -> R<V> {
        let n = if b {
            self.ext.bool_true
        } else {
            self.ext.bool_false
        };
        match n {
            Some(n) => Ok(self.cnst(n, LevelList::EMPTY)),
            None => Err(KErr("`Bool` is missing".into())),
        }
    }

    pub fn reduce_nat(&mut self, v: V) -> R<Option<V>> {
        if self.ext.nat.is_none() {
            return Ok(None);
        }
        let v = self.force(v);
        let Val::Const(n, ls, sp) = self.a.get(v) else {
            return Ok(None);
        };
        if ls != LevelList::EMPTY || self.a.sp_has_proj(sp) {
            return Ok(None);
        }
        match self.a.sp_len(sp) {
            1 if Some(n) == self.ext.nat_succ => {
                let Elim::Arg(a) = self.a.sp_last(sp).1 else {
                    unreachable!()
                };
                let a = self.whnf(a)?;
                let Some(x) = self.nat_lit_ext(a) else {
                    return Ok(None);
                };
                let x = x + 1u32;
                Self::nat_size_ok(&x)?;
                Ok(Some(self.nat(x)))
            }
            2 => {
                let Some(op) = self.ext.nat_op(n) else {
                    return Ok(None);
                };
                let (p, e_r) = self.a.sp_last(sp);
                let (_, e_l) = self.a.sp_last(p);
                let (Elim::Arg(a_l), Elim::Arg(a_r)) = (e_l, e_r) else {
                    unreachable!()
                };
                let x = self.whnf(a_l)?;
                let Some(x) = self.nat_lit_ext(x) else {
                    return Ok(None);
                };
                let y = self.whnf(a_r)?;
                let Some(y) = self.nat_lit_ext(y) else {
                    return Ok(None);
                };
                self.nat_op(op, x, y).map(Some)
            }
            _ => Ok(None),
        }
    }

    fn nat_op(&mut self, op: NatOp, x: BigUint, y: BigUint) -> R<V> {
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
            NatOp::Gcd => {
                let (mut a, mut b) = (x, y);
                while b != BigUint::ZERO {
                    let r = &a % &b;
                    a = b;
                    b = r;
                }
                a
            }
            NatOp::Beq => return self.mk_bool(x == y),
            NatOp::Ble => return self.mk_bool(x <= y),
            NatOp::Land => x & y,
            NatOp::Lor => x | y,
            NatOp::Xor => x ^ y,
            NatOp::Pow => {
                let Ok(k) = u32::try_from(&y) else {
                    return Err(KErr(
                        "the kernel refused to evaluate `Nat.pow` because its second argument does not fit in a 32-bit unsigned integer".into(),
                    ));
                };
                if x > BigUint::from(1u32)
                    && k != 0
                    && x.bits().div_ceil(8) > NAT_MAX_BYTES / k as u64
                {
                    return Err(KErr(
                        "the kernel refused to evaluate `Nat.pow` because the result would exceed the maximum numeral size".into(),
                    ));
                }
                x.pow(k)
            }
            NatOp::ShiftLeft => {
                if x == BigUint::ZERO {
                    BigUint::ZERO
                } else {
                    let Ok(k) = u32::try_from(&y) else {
                        return Err(KErr(
                            "the kernel refused to evaluate `Nat.shiftLeft` because its second argument does not fit in a 32-bit unsigned integer".into(),
                        ));
                    };
                    if x.bits().div_ceil(8) + k as u64 / 8 + 1 > NAT_MAX_BYTES {
                        return Err(KErr(
                            "the kernel refused a `Nat` numeral because its size exceeds the maximum".into(),
                        ));
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
        Ok(self.nat(r))
    }

    pub fn whnf(&mut self, v: V) -> R<V> {
        let v = self.force(v);
        match self.a.get(v) {
            Val::Sort(_)
            | Val::Pi(..)
            | Val::PiInfer(..)
            | Val::Lam(..)
            | Val::Nat(..)
            | Val::NatBig(_)
            | Val::Str(_) => return Ok(v),
            Val::FVar(k, _) if self.let_value(k).is_none() => return Ok(v),
            _ => {}
        }
        let c = self.a.r(v).whnf;
        if c != super::val::NONE {
            return Ok(V(c));
        }
        let mut t = v;
        let mut first = true;
        loop {
            let t_l = self.whnf_core(t, false, false)?;
            if let Some(n) = self.reduce_nat(t_l)? {
                self.a.rm(v).whnf = n.0;
                return Ok(n);
            }
            if first && self.is_delta(t_l).is_some() {
                first = false;
                if let Some(n) = self.closed_whnf(t_l) {
                    self.a.rm(v).whnf = n.0;
                    self.a.rm(n).whnf = n.0;
                    return Ok(n);
                }
            }
            match self.unfold_definition(t_l) {
                Some(n) => t = n,
                None => {
                    self.a.rm(v).whnf = t_l.0;
                    return Ok(t_l);
                }
            }
        }
    }
}
