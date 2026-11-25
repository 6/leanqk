//! Closed values handed to the closed-term evaluator (`check/eval`), which
//! computes with machine integers, arrays and lists far faster than
//! evaluation on values does. A closed value is read back to a term, the
//! evaluator computes its weak head normal form, and that term is
//! evaluated back into a value. The evaluator only takes the kernel's own
//! reduction steps (see `docs/kernel-compute.md`), so the result is a
//! reduct of the value; when it gives up, `whnf` goes on by itself.

use crate::expr::ExprId;
use crate::name::NameId;

use super::super::store::IdMap;
use super::super::tc::Tc;
use super::Nbe;
use super::val::{Elim, Env, Ls, Sp, V, Val};

/// Terms names may add to the store before naming stops.
const NAMES_LIMIT: usize = 1 << 20;

/// How deep a read back may nest before the evaluator is not used.
const MAX_DEPTH: u32 = 4096;

impl<'e> Nbe<'e> {
    /// The weak head normal form of the closed value `v` by the closed-term
    /// evaluator, if it computes one that differs from `v`.
    pub(super) fn closed_whnf(&mut self, v: V) -> Option<V> {
        if !self.closed_eval || self.a.has_fvar(v) {
            return None;
        }
        let mut memo = IdMap::default();
        let e = self.term_of(v, 0, &mut memo, false)?;
        let mut ev = match self.ev.take() {
            Some(ev) => ev,
            None => Box::new(Tc::new(self.st.fresh(), self.ext, self.limit)),
        };
        ev.limit = self.limit;
        // The evaluator works in the checker's store, so that the terms
        // it caches stay meaningful from one call to the next.
        std::mem::swap(&mut self.st, &mut ev.st);
        let r = super::super::eval::whnf(&mut ev, e);
        std::mem::swap(&mut self.st, &mut ev.st);
        self.ev = Some(ev);
        self.ev_used = true;
        let r = r?;
        if r == e {
            return None;
        }
        Some(self.eval(r, Env::NIL, Ls::ID))
    }

    /// The term `v` stands for, remembered.
    pub(super) fn name(&mut self, v: V) -> Option<ExprId> {
        if let Some(&e) = self.names.get(&v) {
            return (e.0 != super::val::NONE).then_some(e);
        }
        if self.name_exprs > NAMES_LIMIT {
            return None;
        }
        let mut memo = std::mem::take(&mut self.names);
        let before = self.st.local_exprs();
        let r = self.term_of(v, 0, &mut memo, true);
        self.name_exprs += self.st.local_exprs() - before;
        self.names = memo;
        if r.is_none() {
            self.names.insert(v, ExprId(super::val::NONE));
        }
        r
    }

    /// Drop the names (their terms stay in the store until it is cleared).
    pub(super) fn forget_names(&mut self) {
        super::shrink(&mut self.names);
        super::shrink(&mut self.name_eq);
    }

    /// The term a value stands for (its closures' terms with their
    /// environments substituted), or `None` if it nests too deep or holds a
    /// value with no term of its own. Free variables are the store's `FVar`
    /// terms if `open`, else `None`.
    pub(super) fn term_of(
        &mut self,
        v: V,
        depth: u32,
        memo: &mut IdMap<V, ExprId>,
        open: bool,
    ) -> Option<ExprId> {
        if depth > MAX_DEPTH {
            return None;
        }
        if let Some(&e) = memo.get(&v) {
            return Some(e);
        }
        let e = match self.a.get(v) {
            Val::Sort(l) => self.st.sort(l),
            Val::Nat(lo, hi) => self.st.nat_u64((hi as u64) << 32 | lo as u64),
            Val::NatBig(i) => {
                let n = self.big(i).clone();
                self.st.nat(n)
            }
            Val::Str(s) => self.st.mk(crate::expr::ExprNode::Str(s)),
            Val::Lam(t, env, ls) | Val::Pi(t, env, ls) | Val::Thunk(t, env, ls) => {
                self.term_in_env(t, env, ls, depth, memo, open)?
            }
            Val::PiInfer(..) => return None,
            Val::FVar(k, sp) => {
                if !open || k == super::BOTTOM {
                    return None;
                }
                let h = self.st.fvar(k);
                self.spine_term(h, sp, depth, memo, open)?
            }
            Val::Const(n, l, sp) => {
                let h = self.st.cnst(n, l);
                self.spine_term(h, sp, depth, memo, open)?
            }
        };
        memo.insert(v, e);
        Some(e)
    }

    fn spine_term(
        &mut self,
        mut h: ExprId,
        sp: Sp,
        depth: u32,
        memo: &mut IdMap<V, ExprId>,
        open: bool,
    ) -> Option<ExprId> {
        if sp != Sp::NIL {
            let mut es = Vec::new();
            self.a.elims(sp, &mut es);
            for el in es {
                h = match el {
                    Elim::Arg(a) => {
                        let a = self.term_of(a, depth + 1, memo, open)?;
                        self.st.app(h, a)
                    }
                    Elim::Proj(s, i) => self.st.proj(s, i, h),
                };
            }
        }
        Some(h)
    }

    fn term_in_env(
        &mut self,
        mut e: ExprId,
        env: Env,
        ls: Ls,
        depth: u32,
        memo: &mut IdMap<V, ExprId>,
        open: bool,
    ) -> Option<ExprId> {
        if ls != Ls::ID {
            let node = self.a.ls(ls);
            let ps: Vec<NameId> = self.st.name_list(node.params).to_vec();
            let lv: Vec<crate::level::LevelId> = self.st.list(node.levels).to_vec();
            e = self.st.instantiate_lparams(e, &ps, &lv);
        }
        if self.st.has_loose_bvars(e) {
            let mut vs = Vec::new();
            self.a.env_values(env, &mut vs);
            let n = self.st.data(e).loose_bvar_range() as usize;
            vs.truncate(n);
            let mut ts = Vec::with_capacity(vs.len());
            for v in vs {
                ts.push(self.term_of(v, depth + 1, memo, open)?);
            }
            e = self.st.instantiate(e, &ts);
        }
        Some(e)
    }
}
