//! Substitution on terms: instantiating and abstracting bound variables,
//! lifting them, and instantiating universe parameters. These follow
//! `instantiate.cpp` and `abstract.cpp` in Lean's kernel. Each traversal
//! skips subterms that cannot change (by their cached loose-bvar range,
//! free-variable flag or level-parameter flag) and memoizes on
//! `(subterm, binder depth)`, so shared subterms are visited once.

use std::mem;

use crate::expr::{ExprId, ExprNode};
use crate::level::{LevelId, LevelList, LevelNode};
use crate::name::NameId;

use super::store::{IdMap, Store};

/// What a traversal does at the leaves.
#[derive(Clone, Copy)]
enum Op<'a> {
    /// `#(off + i) ↦ s[i]` for `i < s.len()` (or `s[len - 1 - i]` if `rev`);
    /// larger indices drop by `s.len()`.
    Inst { s: &'a [ExprId], rev: bool },
    /// `fvars[i] ↦ #(off + len - 1 - i)`.
    Abstract { fvars: &'a [ExprId] },
    /// Indices at least `off + s` move up by `d`.
    Lift { s: u32, d: u32 },
    /// Indices at least `off + s` move down by `d` (they must be `>= off + s + d`).
    Lower { s: u32, d: u32 },
}

impl Store<'_> {
    fn take_memo(&mut self) -> IdMap<(ExprId, u32), ExprId> {
        let mut m = mem::take(&mut self.memo);
        m.clear();
        m
    }

    fn put_memo(&mut self, mut m: IdMap<(ExprId, u32), ExprId>) {
        if m.capacity() > 1 << 14 {
            m = IdMap::default();
        }
        self.memo = m;
    }

    fn skip(&self, e: ExprId, off: u32, op: Op<'_>) -> bool {
        let d = self.data(e);
        match op {
            Op::Inst { .. } => d.loose_bvar_range() <= off,
            Op::Lift { s, .. } | Op::Lower { s, .. } => d.loose_bvar_range() <= off + s,
            Op::Abstract { .. } => !d.has_fvar(),
        }
    }

    fn walk(
        &mut self,
        e: ExprId,
        off: u32,
        op: Op<'_>,
        memo: &mut IdMap<(ExprId, u32), ExprId>,
    ) -> ExprId {
        if self.skip(e, off, op) {
            return e;
        }
        let node = self.node(e);
        match node {
            ExprNode::BVar(i) => {
                return match op {
                    Op::Inst { s, rev } => {
                        let n = s.len() as u32;
                        if i < off {
                            e
                        } else if i - off < n {
                            let k = (i - off) as usize;
                            let v = if rev { s[s.len() - 1 - k] } else { s[k] };
                            if off > 0 && self.has_loose_bvars(v) {
                                self.lift_loose(v, 0, off)
                            } else {
                                v
                            }
                        } else {
                            self.bvar(i - n)
                        }
                    }
                    Op::Lift { s, d } => {
                        if i >= off + s {
                            self.bvar(i + d)
                        } else {
                            e
                        }
                    }
                    Op::Lower { s, d } => {
                        if i >= off + s {
                            self.bvar(i - d)
                        } else {
                            e
                        }
                    }
                    Op::Abstract { .. } => e,
                };
            }
            ExprNode::FVar(_) => {
                if let Op::Abstract { fvars } = op {
                    let n = fvars.len();
                    if let Some(p) = fvars.iter().rposition(|&f| f == e) {
                        return self.bvar(off + (n - 1 - p) as u32);
                    }
                }
                return e;
            }
            ExprNode::Sort(_)
            | ExprNode::Const(..)
            | ExprNode::NatSmall(..)
            | ExprNode::NatBig(_)
            | ExprNode::Str(_) => return e,
            _ => {}
        }
        if let Some(&r) = memo.get(&(e, off)) {
            return r;
        }
        let r = match node {
            ExprNode::App(f, a) => {
                let f2 = self.walk(f, off, op, memo);
                let a2 = self.walk(a, off, op, memo);
                self.app(f2, a2)
            }
            ExprNode::Lam(bi, n, t, b) => {
                let t2 = self.walk(t, off, op, memo);
                let b2 = self.walk(b, off + 1, op, memo);
                self.lam(bi, n, t2, b2)
            }
            ExprNode::Pi(bi, n, t, b) => {
                let t2 = self.walk(t, off, op, memo);
                let b2 = self.walk(b, off + 1, op, memo);
                self.pi(bi, n, t2, b2)
            }
            ExprNode::Let(h, b) => {
                let lb = self.let_binder(h);
                let t2 = self.walk(lb.ty, off, op, memo);
                let v2 = self.walk(lb.value, off, op, memo);
                let b2 = self.walk(b, off + 1, op, memo);
                self.mk_let(lb.name, t2, v2, b2)
            }
            ExprNode::Proj(s, i, x) => {
                let x2 = self.walk(x, off, op, memo);
                self.proj(s, i, x2)
            }
            _ => unreachable!(),
        };
        memo.insert((e, off), r);
        r
    }

    fn run(&mut self, e: ExprId, op: Op<'_>) -> ExprId {
        if self.skip(e, 0, op) {
            return e;
        }
        let mut memo = self.take_memo();
        let r = self.walk(e, 0, op, &mut memo);
        self.put_memo(memo);
        r
    }

    /// Lean's `instantiate(e, n, s)`: `#i ↦ s[i]`.
    pub fn instantiate(&mut self, e: ExprId, s: &[ExprId]) -> ExprId {
        if s.is_empty() {
            return e;
        }
        self.run(e, Op::Inst { s, rev: false })
    }

    /// Lean's `instantiate_rev(e, n, s)`: `#i ↦ s[n - 1 - i]`.
    pub fn instantiate_rev(&mut self, e: ExprId, s: &[ExprId]) -> ExprId {
        if s.is_empty() {
            return e;
        }
        self.run(e, Op::Inst { s, rev: true })
    }

    pub fn instantiate1(&mut self, e: ExprId, v: ExprId) -> ExprId {
        self.run(
            e,
            Op::Inst {
                s: &[v],
                rev: false,
            },
        )
    }

    /// Replace `fvars[i]` with `#(n - 1 - i)`, as when binding them in order.
    pub fn abstract_fvars(&mut self, e: ExprId, fvars: &[ExprId]) -> ExprId {
        if fvars.is_empty() {
            return e;
        }
        self.run(e, Op::Abstract { fvars })
    }

    pub fn lift_loose(&mut self, e: ExprId, s: u32, d: u32) -> ExprId {
        if d == 0 {
            return e;
        }
        // A fresh memo: this may run inside another traversal.
        let op = Op::Lift { s, d };
        if self.skip(e, 0, op) {
            return e;
        }
        let mut memo = IdMap::default();
        self.walk(e, 0, op, &mut memo)
    }

    pub fn lower_loose(&mut self, e: ExprId, s: u32, d: u32) -> ExprId {
        if d == 0 {
            return e;
        }
        let op = Op::Lower { s, d };
        if self.skip(e, 0, op) {
            return e;
        }
        let mut memo = IdMap::default();
        self.walk(e, 0, op, &mut memo)
    }

    /// Whether `#i` occurs loose in `e`.
    pub fn has_loose_bvar(&self, e: ExprId, i: u32) -> bool {
        let mut seen = IdMap::<(ExprId, u32), ()>::default();
        self.has_bvar_rec(e, i, &mut seen)
    }

    fn has_bvar_rec(&self, e: ExprId, i: u32, seen: &mut IdMap<(ExprId, u32), ()>) -> bool {
        if self.data(e).loose_bvar_range() <= i {
            return false;
        }
        match self.node(e) {
            ExprNode::BVar(j) => j == i,
            ExprNode::App(f, a) => {
                if seen.insert((e, i), ()).is_some() {
                    return false;
                }
                self.has_bvar_rec(f, i, seen) || self.has_bvar_rec(a, i, seen)
            }
            ExprNode::Lam(_, _, t, b) | ExprNode::Pi(_, _, t, b) => {
                if seen.insert((e, i), ()).is_some() {
                    return false;
                }
                self.has_bvar_rec(t, i, seen) || self.has_bvar_rec(b, i + 1, seen)
            }
            ExprNode::Let(h, b) => {
                if seen.insert((e, i), ()).is_some() {
                    return false;
                }
                let lb = self.let_binder(h);
                self.has_bvar_rec(lb.ty, i, seen)
                    || self.has_bvar_rec(lb.value, i, seen)
                    || self.has_bvar_rec(b, i + 1, seen)
            }
            ExprNode::Proj(_, _, x) => self.has_bvar_rec(x, i, seen),
            _ => false,
        }
    }

    // ---- universe parameters ----

    pub fn inst_level(&mut self, l: LevelId, ps: &[NameId], ls: &[LevelId]) -> LevelId {
        if !self.level_has_param(l) {
            return l;
        }
        match self.level(l) {
            LevelNode::Zero => l,
            LevelNode::Succ(a) => {
                let a = self.inst_level(a, ps, ls);
                self.succ(a)
            }
            LevelNode::Max(a, b) => {
                let a = self.inst_level(a, ps, ls);
                let b = self.inst_level(b, ps, ls);
                self.max(a, b)
            }
            LevelNode::IMax(a, b) => {
                let a = self.inst_level(a, ps, ls);
                let b = self.inst_level(b, ps, ls);
                self.imax(a, b)
            }
            LevelNode::Param(n) => match ps.iter().position(|&p| p == n) {
                Some(i) if i < ls.len() => ls[i],
                _ => l,
            },
        }
    }

    pub fn inst_list(&mut self, ll: LevelList, ps: &[NameId], ls: &[LevelId]) -> LevelList {
        if !self.list_has_param(ll) {
            return ll;
        }
        let v: Vec<LevelId> = self.list(ll).to_vec();
        let v: Vec<LevelId> = v.into_iter().map(|l| self.inst_level(l, ps, ls)).collect();
        self.mk_list(&v)
    }

    /// Replace the universe parameters `ps` with `ls` throughout `e`.
    pub fn instantiate_lparams(&mut self, e: ExprId, ps: &[NameId], ls: &[LevelId]) -> ExprId {
        if ps.is_empty() || !self.data(e).has_level_param() {
            return e;
        }
        let mut memo = self.take_memo();
        let r = self.inst_lp(e, ps, ls, &mut memo);
        self.put_memo(memo);
        r
    }

    fn inst_lp(
        &mut self,
        e: ExprId,
        ps: &[NameId],
        ls: &[LevelId],
        memo: &mut IdMap<(ExprId, u32), ExprId>,
    ) -> ExprId {
        if !self.data(e).has_level_param() {
            return e;
        }
        if let Some(&r) = memo.get(&(e, 0)) {
            return r;
        }
        let r = match self.node(e) {
            ExprNode::Sort(l) => {
                let l = self.inst_level(l, ps, ls);
                self.sort(l)
            }
            ExprNode::Const(n, ll) => {
                let ll = self.inst_list(ll, ps, ls);
                self.cnst(n, ll)
            }
            ExprNode::App(f, a) => {
                let f = self.inst_lp(f, ps, ls, memo);
                let a = self.inst_lp(a, ps, ls, memo);
                self.app(f, a)
            }
            ExprNode::Lam(bi, n, t, b) => {
                let t = self.inst_lp(t, ps, ls, memo);
                let b = self.inst_lp(b, ps, ls, memo);
                self.lam(bi, n, t, b)
            }
            ExprNode::Pi(bi, n, t, b) => {
                let t = self.inst_lp(t, ps, ls, memo);
                let b = self.inst_lp(b, ps, ls, memo);
                self.pi(bi, n, t, b)
            }
            ExprNode::Let(h, b) => {
                let lb = self.let_binder(h);
                let t = self.inst_lp(lb.ty, ps, ls, memo);
                let v = self.inst_lp(lb.value, ps, ls, memo);
                let b = self.inst_lp(b, ps, ls, memo);
                self.mk_let(lb.name, t, v, b)
            }
            ExprNode::Proj(s, i, x) => {
                let x = self.inst_lp(x, ps, ls, memo);
                self.proj(s, i, x)
            }
            _ => e,
        };
        memo.insert((e, 0), r);
        r
    }
}
