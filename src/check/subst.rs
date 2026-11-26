//! Substitution on terms: instantiating and abstracting bound variables,
//! lifting them, and instantiating universe parameters. These follow
//! `instantiate.cpp` and `abstract.cpp` in Lean's kernel. Each traversal
//! skips subterms that cannot change (by their cached loose-bvar range,
//! free-variable flag or level-parameter flag) and memoizes on
//! `(subterm, binder depth)`, so shared subterms are visited once.

use std::mem;

use crate::expr::{ExprData, ExprId, ExprNode};
use crate::level::{LevelId, LevelList};
use crate::name::NameId;

use super::store::{IdMap, Store};
use super::univ;

fn lookup_param(ps: &[NameId], ls: &[LevelId], n: NameId) -> Option<LevelId> {
    let i = ps.iter().position(|&p| p == n)?;
    ls.get(i).copied()
}

/// The metadata needed to skip a subtree, and the effect on its leaves.
trait Rewrite: Copy {
    fn affects(self, data: ExprData, off: u32) -> bool;

    fn bvar(self, _store: &mut Store<'_>, e: ExprId, _i: u32, _off: u32) -> ExprId {
        e
    }

    fn fvar(self, _store: &mut Store<'_>, e: ExprId, _off: u32) -> ExprId {
        e
    }
}

#[derive(Clone, Copy)]
struct Instantiate<'a> {
    args: &'a [ExprId],
    rev: bool,
}

impl Rewrite for Instantiate<'_> {
    fn affects(self, data: ExprData, off: u32) -> bool {
        data.loose_bvar_range() > off
    }

    fn bvar(self, store: &mut Store<'_>, _e: ExprId, i: u32, off: u32) -> ExprId {
        let slot = i - off;
        let len = self.args.len();
        if slot >= len as u32 {
            return store.bvar(i - len as u32);
        }
        let slot = slot as usize;
        let v = self.args[if self.rev { len - 1 - slot } else { slot }];
        if off > 0 && store.has_loose_bvars(v) {
            store.lift_loose(v, 0, off)
        } else {
            v
        }
    }
}

#[derive(Clone, Copy)]
struct Abstract<'a>(&'a [ExprId]);

impl Rewrite for Abstract<'_> {
    fn affects(self, data: ExprData, _off: u32) -> bool {
        data.has_fvar()
    }

    fn fvar(self, store: &mut Store<'_>, e: ExprId, off: u32) -> ExprId {
        match self.0.iter().rev().position(|&f| f == e) {
            Some(i) => store.bvar(off + i as u32),
            None => e,
        }
    }
}

#[derive(Clone, Copy)]
struct Shift<const UP: bool> {
    cutoff: u32,
    amount: u32,
}

impl<const UP: bool> Rewrite for Shift<UP> {
    fn affects(self, data: ExprData, off: u32) -> bool {
        data.loose_bvar_range() > off + self.cutoff
    }

    fn bvar(self, store: &mut Store<'_>, _e: ExprId, i: u32, _off: u32) -> ExprId {
        store.bvar(if UP { i + self.amount } else { i - self.amount })
    }
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

    #[inline(always)]
    fn walk(
        &mut self,
        e: ExprId,
        off: u32,
        op: impl Rewrite,
        memo: &mut IdMap<(ExprId, u32), ExprId>,
    ) -> ExprId {
        if op.affects(self.data(e), off) {
            self.rewrite(e, off, op, memo)
        } else {
            e
        }
    }

    // The node's metadata has already passed the operation's subtree check.
    fn rewrite(
        &mut self,
        e: ExprId,
        off: u32,
        op: impl Rewrite,
        memo: &mut IdMap<(ExprId, u32), ExprId>,
    ) -> ExprId {
        let node = self.node(e);
        match node {
            ExprNode::BVar(i) => return op.bvar(self, e, i, off),
            ExprNode::FVar(_) => return op.fvar(self, e, off),
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

    fn run(&mut self, e: ExprId, op: impl Rewrite) -> ExprId {
        if !op.affects(self.data(e), 0) {
            return e;
        }
        let mut memo = self.take_memo();
        let r = self.rewrite(e, 0, op, &mut memo);
        self.put_memo(memo);
        r
    }

    /// Lean's `instantiate(e, n, s)`: `#i ↦ s[i]`.
    pub fn instantiate(&mut self, e: ExprId, s: &[ExprId]) -> ExprId {
        if s.is_empty() {
            return e;
        }
        self.run(
            e,
            Instantiate {
                args: s,
                rev: false,
            },
        )
    }

    /// Lean's `instantiate_rev(e, n, s)`: `#i ↦ s[n - 1 - i]`.
    pub fn instantiate_rev(&mut self, e: ExprId, s: &[ExprId]) -> ExprId {
        if s.is_empty() {
            return e;
        }
        self.run(e, Instantiate { args: s, rev: true })
    }

    pub fn instantiate1(&mut self, e: ExprId, v: ExprId) -> ExprId {
        self.run(
            e,
            Instantiate {
                args: &[v],
                rev: false,
            },
        )
    }

    /// Replace `fvars[i]` with `#(n - 1 - i)`, as when binding them in order.
    pub fn abstract_fvars(&mut self, e: ExprId, fvars: &[ExprId]) -> ExprId {
        if fvars.is_empty() {
            return e;
        }
        self.run(e, Abstract(fvars))
    }

    pub fn lift_loose(&mut self, e: ExprId, s: u32, d: u32) -> ExprId {
        if d == 0 {
            return e;
        }
        // A fresh memo: this may run inside another traversal.
        let op = Shift::<true> {
            cutoff: s,
            amount: d,
        };
        if !op.affects(self.data(e), 0) {
            return e;
        }
        let mut memo = IdMap::default();
        self.rewrite(e, 0, op, &mut memo)
    }

    pub fn lower_loose(&mut self, e: ExprId, s: u32, d: u32) -> ExprId {
        if d == 0 {
            return e;
        }
        let op = Shift::<false> {
            cutoff: s,
            amount: d,
        };
        if !op.affects(self.data(e), 0) {
            return e;
        }
        let mut memo = IdMap::default();
        self.rewrite(e, 0, op, &mut memo)
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
        univ::instantiate_level(self, l, |_, n| lookup_param(ps, ls, n))
    }

    pub fn inst_list(&mut self, ll: LevelList, ps: &[NameId], ls: &[LevelId]) -> LevelList {
        univ::instantiate_list(self, ll, |_, n| lookup_param(ps, ls, n))
    }

    /// Replace the universe parameters `ps` with `ls` throughout `e`.
    pub fn instantiate_lparams(&mut self, e: ExprId, ps: &[NameId], ls: &[LevelId]) -> ExprId {
        if ps.is_empty()
            || !self.data(e).has_level_param()
            || super::univ::OWN_LEVELS && self.is_own_levels(ps, ls)
        {
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
