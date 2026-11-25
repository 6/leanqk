//! Definitional equality on values, following `is_def_eq_core` of
//! `type_checker.cpp` step by step.

use crate::env::{DeclKind, Hints};
use crate::expr::ExprNode;
use crate::level::{LevelId, LevelList};

use super::super::tc::R;
use super::super::univ;
use super::Nbe;
use super::val::{Elim, Sp, V, Val};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Step {
    Continue,
    Unknown,
    Equal,
    Diff,
}

fn pair(a: V, b: V) -> (V, V) {
    if a <= b { (a, b) } else { (b, a) }
}

fn compare_hints(h_l: Hints, h_r: Hints) -> i32 {
    match (h_l, h_r) {
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

fn decl_hints(d: &crate::env::Decl) -> Hints {
    match d.kind {
        DeclKind::Definition { hints, .. } => hints,
        _ => Hints::Opaque,
    }
}

impl Nbe<'_> {
    /// Whether `v` is a binder closure: `Some(true)` for a λ, `Some(false)`
    /// for a Π.
    fn binder_kind(&self, v: V) -> Option<bool> {
        match self.a.get(v) {
            Val::Lam(..) => Some(true),
            Val::Pi(..) | Val::PiInfer(..) => Some(false),
            _ => None,
        }
    }

    fn is_def_eq_binding(&mut self, t: V, s: V) -> R<bool> {
        let mut opened = Vec::new();
        let r = self.is_def_eq_binding_in(t, s, &mut opened);
        for &x in opened.iter().rev() {
            self.pop_fvar(x);
        }
        r
    }

    fn is_def_eq_binding_in(&mut self, mut t: V, mut s: V, opened: &mut Vec<V>) -> R<bool> {
        let lam = self.binder_kind(t) == Some(true);
        loop {
            let (tterm, senv_term) = match (self.a.get(t), self.a.get(s)) {
                (Val::Lam(a, ..), Val::Lam(b, ..)) => (a, b),
                (Val::Pi(a, ..) | Val::PiInfer(a, ..), Val::Pi(b, ..) | Val::PiInfer(b, ..)) => {
                    (a, b)
                }
                _ => break,
            };
            let td = self.binder_dom(t);
            let sd = self.binder_dom(s);
            if td != sd && !self.is_def_eq(td, sd)? {
                return Ok(false);
            }
            let (sn, sbi) = match self.st.node(senv_term) {
                ExprNode::Lam(bi, n, ..) | ExprNode::Pi(bi, n, ..) => (n, bi),
                _ => unreachable!(),
            };
            let uses = self.body_uses_var(t) || self.body_uses_var(s);
            let _ = tterm;
            let x = if uses {
                let x = self.push_fvar(sn, sd, None, sbi);
                opened.push(x);
                x
            } else {
                // Not referenced: any closed value will do (Lean: `dontcare`).
                self.a.mk(Val::Sort(LevelId::ZERO))
            };
            t = self.instantiate(t, x)?;
            s = self.instantiate(s, x)?;
            t = self.force(t);
            s = self.force(s);
            let same = match (self.binder_kind(t), self.binder_kind(s)) {
                (Some(a), Some(b)) => a == b && a == lam,
                _ => false,
            };
            if !same {
                break;
            }
        }
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

    fn is_lit(v: &Val) -> bool {
        matches!(v, Val::Nat(..) | Val::NatBig(_) | Val::Str(_))
    }

    fn quick_is_def_eq(&mut self, t: V, s: V) -> R<Option<bool>> {
        if t == s || self.eq_ok.contains(&pair(t, s)) {
            return Ok(Some(true));
        }
        if self.syn_eq(t, s) {
            return Ok(Some(true));
        }
        let (nt, ns) = (self.a.get(t), self.a.get(s));
        Ok(match (nt, ns) {
            (Val::Lam(..), Val::Lam(..))
            | (Val::Pi(..) | Val::PiInfer(..), Val::Pi(..) | Val::PiInfer(..)) => {
                Some(self.is_def_eq_binding(t, s)?)
            }
            (Val::Sort(a), Val::Sort(b)) => Some(self.is_def_eq_level(a, b)),
            // Literals are canonical: equal values have equal ids.
            _ if Self::is_lit(&nt) && Self::is_lit(&ns) => Some(false),
            _ => None,
        })
    }

    /// The arguments after the last projection of a neutral's spine, and
    /// the spine before them.
    fn split_args(&mut self, sp: Sp, out: &mut Vec<V>) -> Sp {
        out.clear();
        let n = self.a.sp_len(sp);
        let mut k = n;
        while k > 0 {
            match self.a.sp_elim(sp, k - 1) {
                Elim::Arg(v) => {
                    out.push(v);
                    k -= 1;
                }
                Elim::Proj(..) => break,
            }
        }
        out.reverse();
        self.a.sp_prefix(sp, k)
    }

    /// Whether the term `d`, under binders whose domains are `ctx`
    /// (innermost last), is surely a proposition by its form alone: a Π
    /// into one, or a constant or bound variable applied to as many
    /// arguments as its type has Π binders, ending in `Prop`.
    fn surely_prop(&mut self, d: crate::expr::ExprId, ctx: &mut Vec<crate::expr::ExprId>) -> bool {
        use crate::expr::ExprNode;
        match self.st.node(d) {
            ExprNode::Pi(_, _, a, b) => {
                ctx.push(a);
                let r = self.surely_prop(b, ctx);
                ctx.pop();
                r
            }
            _ => {
                let mut f = d;
                let mut k = 0;
                while let ExprNode::App(g, _) = self.st.node(f) {
                    f = g;
                    k += 1;
                }
                let ty = match self.st.node(f) {
                    ExprNode::Const(n, _) => match self.find(n) {
                        Some(c) => {
                            // `autoParam T stx`, `optParam T v`: as `T`.
                            if let Some(j) = self.returns_param(&c, k) {
                                let mut a = d;
                                for _ in 0..k - 1 - j {
                                    let ExprNode::App(g, _) = self.st.node(a) else {
                                        return false;
                                    };
                                    a = g;
                                }
                                let ExprNode::App(_, x) = self.st.node(a) else {
                                    return false;
                                };
                                return self.surely_prop(x, ctx);
                            }
                            c.ty
                        }
                        None => return false,
                    },
                    ExprNode::BVar(j) => match (ctx.len() as u32).checked_sub(j + 1) {
                        Some(i) => ctx[i as usize],
                        None => return false,
                    },
                    _ => return false,
                };
                let mut t = ty;
                for _ in 0..k {
                    match self.st.node(t) {
                        ExprNode::Pi(_, _, _, b) => t = b,
                        _ => return false,
                    }
                }
                matches!(self.st.node(t), ExprNode::Sort(l) if l == crate::level::LevelId::ZERO)
            }
        }
    }

    /// If `c` is a definition `fun x_0 ... x_(k-1) => x_j` (as `autoParam`
    /// and `optParam` are), `j`.
    fn returns_param(&self, c: &crate::env::Decl, k: u32) -> Option<u32> {
        let DeclKind::Definition { value, .. } = c.kind else {
            return None;
        };
        if crate::env::is_lazy(value) {
            return None;
        }
        let mut e = value;
        let mut n = 0;
        while let ExprNode::Lam(_, _, _, b) = self.st.node(e) {
            e = b;
            n += 1;
        }
        match self.st.node(e) {
            ExprNode::BVar(i) if n == k && i < n => Some(n - 1 - i),
            _ => None,
        }
    }

    /// The argument positions (below 64) of constant `n` whose declared
    /// types are surely propositions.
    fn prop_positions(&mut self, n: crate::name::NameId) -> u64 {
        if let Some(&m) = self.prop_pos.get(&n) {
            return m;
        }
        let Some(d) = self.find(n) else {
            return 0;
        };
        use crate::expr::ExprNode;
        let mut ctx = Vec::new();
        let mut m = 0u64;
        let mut t = d.ty;
        let mut i = 0;
        while let ExprNode::Pi(_, _, a, b) = self.st.node(t) {
            if i >= 64 {
                break;
            }
            if self.surely_prop(a, &mut ctx) {
                m |= 1 << i;
            }
            ctx.push(a);
            t = b;
            i += 1;
        }
        self.prop_pos.insert(n, m);
        m
    }

    fn is_def_eq_args(&mut self, t: V, s: V) -> R<bool> {
        let (Val::Const(n, _, tsp), Val::Const(n_r, _, ssp)) = (self.a.get(t), self.a.get(s))
        else {
            return Ok(false);
        };
        // Same constant: a proof argument need not be compared, as the
        // arguments before it are (by induction from the left) equal, so
        // its type is the same proposition on both sides.
        let props = if n == n_r && !self.a.sp_has_proj(tsp) && !self.a.sp_has_proj(ssp) {
            self.prop_positions(n)
        } else {
            0
        };
        let len = self.a.sp_len(tsp);
        if len != self.a.sp_len(ssp) {
            return Ok(false);
        }
        for pos in (0..len).rev() {
            let te = self.a.sp_elim(tsp, pos);
            let se = self.a.sp_elim(ssp, pos);
            match (te, se) {
                (Elim::Arg(_), Elim::Arg(_)) if pos < 64 && props & 1 << pos != 0 => {}
                (Elim::Arg(a), Elim::Arg(b)) => {
                    if !self.is_def_eq(a, b)? {
                        return Ok(false);
                    }
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    fn try_eta_expansion_core(&mut self, t: V, s: V) -> R<bool> {
        if self.binder_kind(t) == Some(true) && self.binder_kind(s) != Some(true) {
            let st_ = self.infer_value(s)?;
            let s_type = self.whnf(st_)?;
            let (Val::Pi(pt, ..) | Val::PiInfer(pt, ..)) = self.a.get(s_type) else {
                return Ok(false);
            };
            let (n, bi) = match self.st.node(pt) {
                ExprNode::Pi(bi, n, ..) | ExprNode::Lam(bi, n, ..) => (n, bi),
                _ => unreachable!(),
            };
            let d = self.binder_dom(s_type);
            let td = self.binder_dom(t);
            if td != d && !self.is_def_eq(td, d)? {
                return Ok(false);
            }
            let x = self.push_fvar(n, d, None, bi);
            let r = self.instantiate(t, x).and_then(|tb| {
                let sb = self.apply(s, x);
                self.is_def_eq(tb, sb)
            });
            self.pop_fvar(x);
            r
        } else {
            Ok(false)
        }
    }

    fn try_eta_expansion(&mut self, t: V, s: V) -> R<bool> {
        Ok(self.try_eta_expansion_core(t, s)? || self.try_eta_expansion_core(s, t)?)
    }

    fn try_eta_struct_core(&mut self, t: V, s: V) -> R<bool> {
        let Val::Const(fname, _, ssp) = self.a.get(s) else {
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
        let mut s_args = Vec::new();
        if !self.a.args(ssp, &mut s_args) || s_args.len() != (num_params + num_fields) as usize {
            return Ok(false);
        }
        if !self.is_non_rec_structure(induct) {
            return Ok(false);
        }
        let tt = self.infer_value(t)?;
        let ts = self.infer_value(s)?;
        if !self.is_def_eq(tt, ts)? {
            return Ok(false);
        }
        // A proof field need not be compared: with the types and the fields
        // before it equal, both sides are proofs of one proposition.
        let props = self.prop_positions(fname);
        for (i, &a) in s_args.iter().enumerate().skip(num_params as usize) {
            if i < 64 && props & 1 << i != 0 {
                continue;
            }
            let p = self.proj(t, induct, (i - num_params as usize) as u32);
            if !self.is_def_eq(p, a)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn try_eta_struct(&mut self, t: V, s: V) -> R<bool> {
        Ok(self.try_eta_struct_core(t, s)? || self.try_eta_struct_core(s, t)?)
    }

    /// Both neutrals end in arguments: compare what comes before them and
    /// the arguments, pairwise.
    fn is_def_eq_app(&mut self, t: V, s: V) -> R<bool> {
        let (th, tsp, sh, ssp) = match (self.a.get(t), self.a.get(s)) {
            (Val::Const(n_l, l_l, sp1), Val::Const(n_r, l_r, sp2)) => (
                Val::Const(n_l, l_l, Sp::NIL),
                sp1,
                Val::Const(n_r, l_r, Sp::NIL),
                sp2,
            ),
            (Val::FVar(k_l, sp1), Val::FVar(k_r, sp2)) => {
                (Val::FVar(k_l, Sp::NIL), sp1, Val::FVar(k_r, Sp::NIL), sp2)
            }
            (Val::Const(n_l, l_l, sp1), Val::FVar(k_r, sp2)) => (
                Val::Const(n_l, l_l, Sp::NIL),
                sp1,
                Val::FVar(k_r, Sp::NIL),
                sp2,
            ),
            (Val::FVar(k_l, sp1), Val::Const(n_r, l_r, sp2)) => (
                Val::FVar(k_l, Sp::NIL),
                sp1,
                Val::Const(n_r, l_r, Sp::NIL),
                sp2,
            ),
            _ => return Ok(false),
        };
        let mut ta = Vec::new();
        let mut sa = Vec::new();
        let tpre = self.split_args(tsp, &mut ta);
        let spre = self.split_args(ssp, &mut sa);
        if ta.is_empty() || sa.is_empty() || ta.len() != sa.len() {
            return Ok(false);
        }
        let tf = self.with_spine(th, tpre);
        let sf = self.with_spine(sh, spre);
        if !self.is_def_eq(tf, sf)? {
            return Ok(false);
        }
        // The heads are equal, so (as in `is_def_eq_args`) proof arguments
        // of the same constant at the same levels need no comparison.
        let props = match (th, sh) {
            (Val::Const(n_l, l_l, _), Val::Const(n_r, l_r, _))
                if n_l == n_r && l_l == l_r && tpre == Sp::NIL && spre == Sp::NIL =>
            {
                self.prop_positions(n_l)
            }
            _ => 0,
        };
        for i in 0..ta.len() {
            if i < 64 && props & 1 << i != 0 {
                continue;
            }
            if !self.is_def_eq(ta[i], sa[i])? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn with_spine(&mut self, head: Val, sp: Sp) -> V {
        match head {
            Val::Const(n, l, _) => self.a.mk(Val::Const(n, l, sp)),
            Val::FVar(k, _) => self.a.mk(Val::FVar(k, sp)),
            _ => unreachable!(),
        }
    }

    fn is_def_eq_proof_irrel(&mut self, t: V, s: V) -> R<Option<bool>> {
        if self.surely_not_proof(t) {
            return Ok(None);
        }
        let tt = self.infer_value(t)?;
        if !self.is_prop(tt)? {
            return Ok(None);
        }
        let ts = self.infer_value(s)?;
        Ok(Some(self.is_def_eq(tt, ts)?))
    }

    /// Whether `t` is no proof by its head constant's declared type alone:
    /// past its arguments that type ends in a sort, or in an application
    /// of a constant whose type ends in a sort that is never `Prop`.
    fn surely_not_proof(&mut self, t: V) -> bool {
        if !NOT_PROOF {
            return false;
        }
        let Val::Const(c, _, sp) = self.a.get(t) else {
            return false;
        };
        if self.a.sp_has_proj(sp) {
            return false;
        }
        let k = self.a.sp_len(sp);
        if let Some(&r) = self.not_proof.get(&(c, k)) {
            return r;
        }
        let r = self.not_proof_by_type(c, k);
        self.not_proof.insert((c, k), r);
        r
    }

    fn not_proof_by_type(&self, c: crate::name::NameId, k: u32) -> bool {
        let Some(d) = self.find(c) else {
            return false;
        };
        let mut e = d.ty;
        let mut binders = 0;
        while let ExprNode::Pi(_, _, _, b) = self.st.node(e) {
            e = b;
            binders += 1;
        }
        if binders < k {
            return false;
        }
        while let ExprNode::App(f, _) = self.st.node(e) {
            e = f;
        }
        let head = match self.st.node(e) {
            ExprNode::Sort(_) => return true,
            ExprNode::Const(h, _) => h,
            _ => return false,
        };
        let Some(hd) = self.find(head) else {
            return false;
        };
        let mut e = hd.ty;
        while let ExprNode::Pi(_, _, _, b) = self.st.node(e) {
            e = b;
        }
        matches!(self.st.node(e), ExprNode::Sort(l) if univ::is_not_zero(&self.st, l))
    }

    /// Lean's `try_unfold_proj_app`: a neutral headed by a projection.
    fn try_unfold_proj_app(&mut self, e: V) -> R<Option<V>> {
        let sp = match self.a.get(e) {
            Val::Const(_, _, sp) | Val::FVar(_, sp) => sp,
            _ => return Ok(None),
        };
        if self.a.sp_has_proj(sp) {
            let n = self.whnf_core(e, false, false)?;
            return Ok((n != e).then_some(n));
        }
        Ok(None)
    }

    fn unfold_cheap(&mut self, e: V) -> R<V> {
        let u = self.unfold_definition(e).expect("delta");
        self.whnf_core(u, false, true)
    }

    /// Whether the arguments of two applications of the abbreviation `d`
    /// (spines `a` and `b`) are worth comparing before unfolding: not when
    /// `d` is an eliminator in disguise (a recursor, casesOn or matcher at
    /// the head of its value) and they differ in something other than
    /// neutral values or closures, which the eliminator would reduce.
    fn probe_worth(&mut self, d: &crate::env::Decl, a: Sp, b: Sp) -> bool {
        if self.abbrev_shape(d.name, 0) != SHAPE_ELIM {
            return true;
        }
        if self.a.sp_has_proj(a) || self.a.sp_has_proj(b) {
            return false;
        }
        let (mut xs, mut ys) = (Vec::new(), Vec::new());
        if !self.a.args(a, &mut xs) || !self.a.args(b, &mut ys) || xs.len() != ys.len() {
            return false;
        }
        let mut kind = 0;
        for (&x, &y) in xs.iter().zip(&ys) {
            if x == y {
                continue;
            }
            let k = match (self.a.get(x), self.a.get(y)) {
                (Val::Const(..) | Val::FVar(..), Val::Const(..) | Val::FVar(..)) => 1,
                (Val::Lam(..) | Val::PiInfer(..), Val::Lam(..) | Val::PiInfer(..)) => 2,
                _ => return false,
            };
            if kind != 0 && k != kind {
                return false;
            }
            kind = k;
        }
        true
    }

    /// `SHAPE_ELIM` if the value of definition `n`, past its λs, is headed
    /// by a recursor or (at most four definitions deep) by a definition
    /// that is, else 0.
    fn abbrev_shape(&mut self, n: crate::name::NameId, depth: u32) -> u8 {
        if let Some(&k) = self.shapes.get(&n) {
            return k;
        }
        let k = (|| {
            let d = self.find(n)?;
            let DeclKind::Definition { value, .. } = d.kind else {
                return None;
            };
            if crate::env::is_lazy(value) {
                return None;
            }
            let mut b = value;
            while let ExprNode::Lam(_, _, _, x) = self.st.node(b) {
                b = x;
            }
            while let ExprNode::Proj(_, _, x) = self.st.node(b) {
                b = x;
            }
            while let ExprNode::App(f, _) = self.st.node(b) {
                b = f;
            }
            let ExprNode::Const(h, _) = self.st.node(b) else {
                return None;
            };
            match self.find(h)?.kind {
                DeclKind::Recursor { .. } => Some(SHAPE_ELIM),
                DeclKind::Definition { .. } if depth < 4 && h != n => {
                    (self.abbrev_shape(h, depth + 1) == SHAPE_ELIM).then_some(SHAPE_ELIM)
                }
                _ => None,
            }
        })()
        .unwrap_or(0);
        self.shapes.insert(n, k);
        k
    }

    fn lazy_delta_reduction_step(&mut self, t: &mut V, s: &mut V) -> R<Step> {
        self.tick()?;
        self.decl_steps = self.decl_steps.saturating_add(1);
        let dt = self.is_delta(*t);
        let ds = self.is_delta(*s);
        match (dt, ds) {
            (None, None) => return Ok(Step::Unknown),
            (Some(_), None) => {
                if let Some(s_r) = self.try_unfold_proj_app(*s)? {
                    *s = s_r;
                } else {
                    *t = self.unfold_cheap(*t)?;
                }
            }
            (None, Some(_)) => {
                if let Some(t_r) = self.try_unfold_proj_app(*t)? {
                    *t = t_r;
                } else {
                    *s = self.unfold_cheap(*s)?;
                }
            }
            (Some(dt), Some(ds)) => {
                let c = compare_hints(decl_hints(&dt), decl_hints(&ds));
                if c < 0 {
                    *t = self.unfold_cheap(*t)?;
                } else if c > 0 {
                    *s = self.unfold_cheap(*s)?;
                } else {
                    if let (Val::Const(_, lt, tsp), Val::Const(_, ls, ssp)) =
                        (self.a.get(*t), self.a.get(*s))
                        && tsp != Sp::NIL
                        && ssp != Sp::NIL
                        && dt.name == ds.name
                        && matches!(decl_hints(&dt), Hints::Regular(_))
                        && !self.eq_fail.contains(&pair(*t, *s))
                    {
                        if self.is_def_eq_levels(lt, ls) && self.is_def_eq_args(*t, *s)? {
                            return Ok(Step::Equal);
                        }
                        self.eq_fail.insert(pair(*t, *s));
                    } else if let (Val::Const(_, lt, tsp), Val::Const(_, ls, ssp)) =
                        (self.a.get(*t), self.a.get(*s))
                        && tsp != Sp::NIL
                        && ssp != Sp::NIL
                        && dt.name == ds.name
                        && !matches!(decl_hints(&dt), Hints::Regular(_))
                        && !self.eq_fail.contains(&pair(*t, *s))
                        && self.is_def_eq_levels(lt, ls)
                        && self.probe_worth(&dt, tsp, ssp)
                    {
                        // An abbreviation (an instance, a projection
                        // function): Lean unfolds both sides, but often
                        // the arguments agree, so they are compared first,
                        // within a budget; out of it, both sides unfold.
                        if self.attempt(ARGS_PROBE, |nb| nb.is_def_eq_args(*t, *s))? == Some(true) {
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

    fn is_nat_zero(&self, t: V) -> bool {
        match self.a.get(t) {
            Val::Const(n, ls, Sp::NIL) => Some(n) == self.ext.nat_zero && ls == LevelList::EMPTY,
            Val::Nat(0, 0) => true,
            _ => false,
        }
    }

    fn is_nat_succ(&mut self, t: V) -> Option<V> {
        match self.a.get(t) {
            Val::Nat(lo, hi) => {
                let v = (hi as u64) << 32 | lo as u64;
                (v != 0).then(|| self.nat_u64(v - 1))
            }
            Val::NatBig(b) => {
                let v = self.big(b) - 1u32;
                Some(self.nat(v))
            }
            Val::Const(n, ls, sp)
                if Some(n) == self.ext.nat_succ
                    && ls == LevelList::EMPTY
                    && self.a.sp_len(sp) == 1 =>
            {
                match self.a.sp_elim(sp, 0) {
                    Elim::Arg(a) => Some(a),
                    Elim::Proj(..) => None,
                }
            }
            _ => None,
        }
    }

    fn is_def_eq_offset(&mut self, t: V, s: V) -> R<Option<bool>> {
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

    fn lazy_delta_reduction(&mut self, t: &mut V, s: &mut V) -> R<Option<bool>> {
        loop {
            if let Some(r) = self.is_def_eq_offset(*t, *s)? {
                return Ok(Some(r));
            }
            if (!self.a.has_fvar(*t) && !self.a.has_fvar(*s)) || self.eager {
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
        t: &mut V,
        s: &mut V,
        sname: crate::name::NameId,
        idx: u32,
    ) -> R<bool> {
        loop {
            match self.lazy_delta_reduction_step(t, s)? {
                Step::Continue => {}
                Step::Equal => return Ok(true),
                Step::Unknown | Step::Diff => {
                    if let Some(t_r) = self.reduce_proj_core(*t, sname, idx)?
                        && let Some(s_r) = self.reduce_proj_core(*s, sname, idx)?
                    {
                        return self.is_def_eq_core(t_r, s_r);
                    }
                    return self.is_def_eq_core(*t, *s);
                }
            }
        }
    }

    fn try_string_lit_expansion_core(&mut self, t: V, s: V) -> R<Option<bool>> {
        let Some(x) = self.ext.string() else {
            return Ok(None);
        };
        let of_list = x.of_list;
        if let Val::Str(_) = self.a.get(t)
            && let Val::Const(n, ls, sp) = self.a.get(s)
            && n == of_list
            && ls == LevelList::EMPTY
            && self.a.sp_len(sp) == 1
            && !self.a.sp_has_proj(sp)
        {
            let c = self.string_lit_to_constructor(t)?;
            let c = self.whnf(c)?;
            return Ok(Some(self.is_def_eq_core(c, s)?));
        }
        Ok(None)
    }

    fn try_string_lit_expansion(&mut self, t: V, s: V) -> R<Option<bool>> {
        if let Some(r) = self.try_string_lit_expansion_core(t, s)? {
            return Ok(Some(r));
        }
        self.try_string_lit_expansion_core(s, t)
    }

    fn is_def_eq_unit_like(&mut self, t: V, s: V) -> R<bool> {
        let tt = self.infer_value(t)?;
        let t_type = self.whnf(tt)?;
        let Some((i, _, _)) = self.head_const(t_type) else {
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
        let ts = self.infer_value(s)?;
        self.is_def_eq_core(t_type, ts)
    }

    fn is_bool_true(&self, e: V) -> bool {
        matches!(self.a.get(e), Val::Const(n, ls, Sp::NIL) if Some(n) == self.ext.bool_true && ls == LevelList::EMPTY)
    }

    /// The last elimination of a neutral, if it is a projection: the
    /// structure and the field.
    fn proj_parts(&mut self, v: V) -> Option<(V, crate::name::NameId, u32)> {
        let (head, sp) = match self.a.get(v) {
            Val::Const(n, l, sp) => (Val::Const(n, l, Sp::NIL), sp),
            Val::FVar(k, sp) => (Val::FVar(k, Sp::NIL), sp),
            _ => return None,
        };
        if sp == Sp::NIL {
            return None;
        }
        match self.a.sp_last_elim(sp) {
            Elim::Proj(s, i) => {
                let pre = self.a.sp_prefix(sp, self.a.sp_len(sp) - 1);
                Some((self.with_spine(head, pre), s, i))
            }
            _ => None,
        }
    }

    pub fn is_def_eq_core(&mut self, t: V, s: V) -> R<bool> {
        let t = self.force(t);
        let s = self.force(s);
        if let Some(r) = self.quick_is_def_eq(t, s)? {
            return Ok(r);
        }
        if (!self.a.has_fvar(t) || self.eager) && self.is_bool_true(s) {
            let w = self.whnf(t)?;
            if self.is_bool_true(w) {
                return Ok(true);
            }
        }
        let mut tn = self.whnf_core(t, false, true)?;
        let mut sn = self.whnf_core(s, false, true)?;
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
        match (self.a.get(tn), self.a.get(sn)) {
            (Val::Const(a, la, Sp::NIL), Val::Const(b, lb, Sp::NIL))
                if a == b && self.is_def_eq_levels(la, lb) =>
            {
                return Ok(true);
            }
            (Val::FVar(a, Sp::NIL), Val::FVar(b, Sp::NIL)) if a == b => return Ok(true),
            _ => {}
        }
        if let Some((tx, sa, ia)) = self.proj_parts(tn)
            && let Some((sx, sb, ib)) = self.proj_parts(sn)
            && sa == sb
            && ia == ib
        {
            let (mut tc, mut sc) = (tx, sx);
            if self.lazy_delta_proj_reduction(&mut tc, &mut sc, sa, ia)? {
                return Ok(true);
            }
        }
        let tnn = self.whnf_core(tn, false, false)?;
        let snn = self.whnf_core(sn, false, false)?;
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

    #[inline]
    pub fn is_def_eq(&mut self, t: V, s: V) -> R<bool> {
        if t == s {
            return Ok(true);
        }
        self.is_def_eq_memo(t, s)
    }

    /// `is_def_eq` of two different values.
    #[inline(never)]
    fn is_def_eq_memo(&mut self, t: V, s: V) -> R<bool> {
        if self.neq.contains(&pair(t, s)) {
            return Ok(false);
        }
        // In a heavy declaration, also remember results by the terms the
        // values stand for: different values (a thunk and its value, say,
        // inside them) often stand for one term, and then compare alike.
        let named = if self.decl_steps > HEAVY_STEPS && !self.eq_ok.contains(&pair(t, s)) {
            match (self.name(t), self.name(s)) {
                (Some(a), Some(b)) => {
                    if a == b {
                        return Ok(true);
                    }
                    let k = if a.0 <= b.0 { (a, b) } else { (b, a) };
                    if let Some(&r) = self.name_eq.get(&k) {
                        return Ok(r);
                    }
                    Some(k)
                }
                _ => None,
            }
        } else {
            None
        };
        let r = self.is_def_eq_core(t, s)?;
        if let Some(k) = named {
            self.name_eq.insert(k, r);
        }
        if r {
            self.eq_ok.insert(pair(t, s));
        } else {
            self.neq.insert(pair(t, s));
        }
        Ok(r)
    }
}

/// Whether proof irrelevance first asks `surely_not_proof`.
const NOT_PROOF: bool = true;

/// Lazy delta steps after which a declaration counts as heavy, and
/// definitional equality also goes by names (`is_def_eq`).
pub(super) const HEAVY_STEPS: u32 = 1 << 10;

/// Steps the arguments of two applications of an abbreviation may take
/// to be found equal before both sides unfold.
const ARGS_PROBE: u64 = 1024;

/// `abbrev_shape` of an eliminator in disguise.
const SHAPE_ELIM: u8 = 4;

/// Bound on the nodes one structural comparison may visit.
const SYN_BUDGET: u32 = 1 << 10;

impl Nbe<'_> {
    /// Whether `t` and `s` are the same term up to how they are represented
    /// (Lean's `eqv_manager` check): equal closures over equal environments,
    /// equal spines. Nothing is reduced. Sound, and much cheaper than a
    /// comparison by reduction when two routes built the same computation.
    pub(super) fn syn_eq(&mut self, t: V, s: V) -> bool {
        let mut budget = SYN_BUDGET;
        let r = self.syn_eq_v(t, s, &mut budget);
        if !r {
            // Out of budget too: a heuristic, not tried again on this pair.
            self.syn_fail.insert(pair(t, s));
        }
        r
    }

    fn syn_eq_v(&mut self, t: V, s: V, budget: &mut u32) -> bool {
        if t == s {
            return true;
        }
        if *budget == 0 {
            return false;
        }
        *budget -= 1;
        let k = pair(t, s);
        if self.eq_ok.contains(&k) || self.syn_ok.contains(&k) {
            return true;
        }
        if self.syn_fail.contains(&k) {
            return false;
        }
        let r = match (self.a.get(t), self.a.get(s)) {
            (Val::Thunk(t_l, e_l, l_l), Val::Thunk(t_r, e_r, l_r))
            | (Val::Lam(t_l, e_l, l_l), Val::Lam(t_r, e_r, l_r))
            | (Val::Pi(t_l, e_l, l_l), Val::Pi(t_r, e_r, l_r))
            | (Val::PiInfer(t_l, e_l, l_l), Val::PiInfer(t_r, e_r, l_r)) => {
                self.syn_eq_t(t_l, e_l, l_l, 0, t_r, e_r, l_r, 0, 0, budget)
            }
            (Val::Thunk(..), _) | (_, Val::Thunk(..)) => {
                let (ft, fs) = (self.forced_or(t), self.forced_or(s));
                (ft != t || fs != s) && self.syn_eq_v(ft, fs, budget)
            }
            (Val::Const(n_l, l_l, sp1), Val::Const(n_r, l_r, sp2)) => {
                n_l == n_r
                    && (l_l == l_r || self.is_def_eq_levels(l_l, l_r))
                    && self.syn_eq_sp(sp1, sp2, budget)
            }
            (Val::FVar(k_l, sp1), Val::FVar(k_r, sp2)) => {
                k_l == k_r && self.syn_eq_sp(sp1, sp2, budget)
            }
            _ => false,
        };
        if r {
            self.syn_ok.insert(k);
        } else if *budget > 0 {
            self.syn_fail.insert(k);
        }
        r
    }

    fn forced_or(&self, v: V) -> V {
        let f = self.a.r(v).forced;
        if f != super::val::NONE { V(f) } else { v }
    }

    fn syn_eq_sp(&mut self, a: Sp, b: Sp, budget: &mut u32) -> bool {
        let n = self.a.sp_len(a);
        if n != self.a.sp_len(b) {
            return false;
        }
        if a == b {
            return true;
        }
        for i in (0..n).rev() {
            let ea = self.a.sp_elim(a, i);
            let eb = self.a.sp_elim(b, i);
            let ok = match (ea, eb) {
                (Elim::Arg(x), Elim::Arg(y)) => self.syn_eq_v(x, y, budget),
                (Elim::Proj(s_l, i_l), Elim::Proj(s_r, i_r)) => s_l == s_r && i_l == i_r,
                _ => false,
            };
            if !ok {
                return false;
            }
        }
        true
    }

    /// `t_l` in `e_l` (under `k_l` binders) against `t_r` in `e_r` (under `k_r`
    /// binders), the last `d` of which were entered in both together: a
    /// bound variable below `d` must be the same on both sides, one below
    /// `k_l` (or `k_r`) but not `d` has no counterpart, and one above is a
    /// value of the environment.
    #[allow(clippy::too_many_arguments)]
    fn syn_eq_t(
        &mut self,
        t_l: crate::expr::ExprId,
        e_l: super::val::Env,
        l_l: super::val::Ls,
        k_l: u32,
        t_r: crate::expr::ExprId,
        e_r: super::val::Env,
        l_r: super::val::Ls,
        k_r: u32,
        d: u32,
        budget: &mut u32,
    ) -> bool {
        if t_l == t_r && k_l == k_r && k_l == d {
            let d_l = self.st.data(t_l);
            let closed = d_l.loose_bvar_range() <= d || e_l == e_r;
            let lvl = !d_l.has_level_param() || l_l == l_r;
            if closed && lvl {
                return true;
            }
        }
        if *budget == 0 {
            return false;
        }
        // Terms are DAGs: remember what was compared at the same depth.
        let memo = k_l == d
            && k_r == d
            && matches!(self.st.node(t_l), ExprNode::App(..))
            && matches!(self.st.node(t_r), ExprNode::App(..));
        let key = (t_l, e_l, l_l, t_r, e_r, l_r, d);
        if memo {
            if let Some(&r) = self.syn_t.get(&key) {
                return r;
            }
            let r = self.syn_eq_t_node(t_l, e_l, l_l, k_l, t_r, e_r, l_r, k_r, d, budget);
            if r || *budget > 0 {
                self.syn_t.insert(key, r);
            }
            return r;
        }
        self.syn_eq_t_node(t_l, e_l, l_l, k_l, t_r, e_r, l_r, k_r, d, budget)
    }

    #[allow(clippy::too_many_arguments)]
    fn syn_eq_t_node(
        &mut self,
        t_l: crate::expr::ExprId,
        e_l: super::val::Env,
        l_l: super::val::Ls,
        k_l: u32,
        t_r: crate::expr::ExprId,
        e_r: super::val::Env,
        l_r: super::val::Ls,
        k_r: u32,
        d: u32,
        budget: &mut u32,
    ) -> bool {
        *budget -= 1;
        let (n_l, n_r) = (self.st.node(t_l), self.st.node(t_r));
        match (n_l, n_r) {
            (ExprNode::BVar(i), ExprNode::BVar(j)) if i < d || j < d => return i == j,
            (ExprNode::BVar(i), _) if i >= d => {
                if i < k_l {
                    return false;
                }
                return match self.a.lookup(e_l, i - k_l) {
                    Some(x) => self.syn_eq_vt(x, t_r, e_r, l_r, k_r, budget, false),
                    None => false,
                };
            }
            (_, ExprNode::BVar(j)) if j >= d => {
                if j < k_r {
                    return false;
                }
                return match self.a.lookup(e_r, j - k_r) {
                    Some(y) => self.syn_eq_vt(y, t_l, e_l, l_l, k_l, budget, true),
                    None => false,
                };
            }
            _ => {}
        }
        match (n_l, n_r) {
            (ExprNode::App(f_l, a_l), ExprNode::App(f_r, a_r)) => {
                self.syn_eq_t(f_l, e_l, l_l, k_l, f_r, e_r, l_r, k_r, d, budget)
                    && self.syn_eq_t(a_l, e_l, l_l, k_l, a_r, e_r, l_r, k_r, d, budget)
            }
            (ExprNode::Lam(_, _, a_l, b_l), ExprNode::Lam(_, _, a_r, b_r))
            | (ExprNode::Pi(_, _, a_l, b_l), ExprNode::Pi(_, _, a_r, b_r)) => {
                self.syn_eq_t(a_l, e_l, l_l, k_l, a_r, e_r, l_r, k_r, d, budget)
                    && self.syn_eq_t(
                        b_l,
                        e_l,
                        l_l,
                        k_l + 1,
                        b_r,
                        e_r,
                        l_r,
                        k_r + 1,
                        d + 1,
                        budget,
                    )
            }
            (ExprNode::Let(h_l, b_l), ExprNode::Let(h_r, b_r)) => {
                let (x, y) = (self.st.let_binder(h_l), self.st.let_binder(h_r));
                self.syn_eq_t(x.ty, e_l, l_l, k_l, y.ty, e_r, l_r, k_r, d, budget)
                    && self.syn_eq_t(x.value, e_l, l_l, k_l, y.value, e_r, l_r, k_r, d, budget)
                    && self.syn_eq_t(
                        b_l,
                        e_l,
                        l_l,
                        k_l + 1,
                        b_r,
                        e_r,
                        l_r,
                        k_r + 1,
                        d + 1,
                        budget,
                    )
            }
            (ExprNode::Proj(s_l, i_l, x_l), ExprNode::Proj(s_r, i_r, x_r)) => {
                s_l == s_r
                    && i_l == i_r
                    && self.syn_eq_t(x_l, e_l, l_l, k_l, x_r, e_r, l_r, k_r, d, budget)
            }
            (ExprNode::Const(n_l, ls1), ExprNode::Const(n_r, ls2)) => {
                n_l == n_r && {
                    let a = self.inst_list(ls1, l_l);
                    let b = self.inst_list(ls2, l_r);
                    a == b || self.is_def_eq_levels(a, b)
                }
            }
            (ExprNode::Sort(a), ExprNode::Sort(b)) => {
                let (a, b) = (self.inst_level(a, l_l), self.inst_level(b, l_r));
                a == b || self.is_def_eq_level(a, b)
            }
            (ExprNode::NatSmall(a, b), ExprNode::NatSmall(c, d)) => (a, b) == (c, d),
            (ExprNode::NatBig(a), ExprNode::NatBig(b)) => self.st.big(a) == self.st.big(b),
            (ExprNode::Str(a), ExprNode::Str(b)) => a == b,
            _ => false,
        }
    }

    /// The value `x` (outside every binder) against the term `t` in `e`
    /// under `k` binders: `t` may not use those binders.
    #[allow(clippy::too_many_arguments)]
    fn syn_eq_vt(
        &mut self,
        x: V,
        t: crate::expr::ExprId,
        e: super::val::Env,
        l: super::val::Ls,
        k: u32,
        budget: &mut u32,
        flip: bool,
    ) -> bool {
        if *budget == 0 {
            return false;
        }
        *budget -= 1;
        if let ExprNode::BVar(j) = self.st.node(t) {
            if j < k {
                return false;
            }
            return match self.a.lookup(e, j - k) {
                Some(y) => self.syn_eq_v(x, y, budget),
                None => false,
            };
        }
        let x = self.forced_or(x);
        match self.a.get(x) {
            Val::Thunk(t_l, e_l, l_l) | Val::Lam(t_l, e_l, l_l) | Val::Pi(t_l, e_l, l_l) => {
                if flip {
                    self.syn_eq_t(t, e, l, k, t_l, e_l, l_l, 0, 0, budget)
                } else {
                    self.syn_eq_t(t_l, e_l, l_l, 0, t, e, l, k, 0, budget)
                }
            }
            Val::Const(_, _, sp) | Val::FVar(_, sp) => {
                let head = self.a.get(x);
                let mut cur = t;
                let mut m = self.a.sp_len(sp);
                loop {
                    match self.st.node(cur) {
                        ExprNode::BVar(j) if j >= k => {
                            let Some(y) = self.a.lookup(e, j - k) else {
                                return false;
                            };
                            let pre = self.a.sp_prefix(sp, m);
                            let h = self.with_spine(head, pre);
                            return self.syn_eq_v(h, y, budget);
                        }
                        ExprNode::App(f, a) if m > 0 => {
                            let el = self.a.sp_elim(sp, m - 1);
                            let Elim::Arg(y) = el else {
                                return false;
                            };
                            if !self.syn_eq_vt(y, a, e, l, k, budget, flip) {
                                return false;
                            }
                            cur = f;
                            m -= 1;
                        }
                        ExprNode::Proj(s_r, i_r, b) if m > 0 => {
                            if self.a.sp_elim(sp, m - 1) != Elim::Proj(s_r, i_r) {
                                return false;
                            }
                            cur = b;
                            m -= 1;
                        }
                        n => {
                            if m > 0 {
                                return false;
                            }
                            return match (head, n) {
                                (Val::Const(m, ls, _), ExprNode::Const(m_r, ls2)) => {
                                    m == m_r && {
                                        let l2 = self.inst_list(ls2, l);
                                        l2 == ls || self.is_def_eq_levels(l2, ls)
                                    }
                                }
                                (Val::FVar(a, _), ExprNode::FVar(b)) => a == b,
                                _ => false,
                            };
                        }
                    }
                }
            }
            Val::Sort(a) => match self.st.node(t) {
                ExprNode::Sort(b) => self.inst_level(b, l) == a,
                _ => false,
            },
            Val::Nat(lo, hi) => self.st.node(t) == ExprNode::NatSmall(lo, hi),
            Val::Str(s) => self.st.node(t) == ExprNode::Str(s),
            _ => false,
        }
    }
}
