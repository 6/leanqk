//! Closed values handed to the closed-term evaluator (`check/eval`), which
//! computes with machine integers, arrays and lists far faster than
//! evaluation on values does. A closed value is read back to a term, the
//! evaluator computes its weak head normal form, and that term is
//! evaluated back into a value. The evaluator only takes the kernel's own
//! reduction steps (see `docs/kernel-compute.md`), so the result is a
//! reduct of the value; when it gives up, `whnf` goes on by itself.

use crate::expr::ExprId;
use crate::name::NameId;

use super::super::store::{IdMap, Store};
use super::super::tc::Tc;
use super::Nbe;
use super::val::{Elim, Env, Ls, Sp, V, Val};

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
        let e = self.readback_closed(v, 0, &mut memo)?;
        let mut ev = match self.ev.take() {
            Some(ev) => ev,
            None => Box::new(Tc::new(Store::new(self.st.env), self.ext, self.limit)),
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

    /// The term of a closed value, or `None` if it nests too deep or holds
    /// a value with no term of its own.
    fn readback_closed(&mut self, v: V, depth: u32, memo: &mut IdMap<V, ExprId>) -> Option<ExprId> {
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
                self.closed_term_in(t, env, ls, depth, memo)?
            }
            Val::PiInfer(..) | Val::FVar(..) => return None,
            Val::Const(n, l, sp) => {
                let mut h = self.st.cnst(n, l);
                if sp != Sp::NIL {
                    let mut es = Vec::new();
                    self.a.elims(sp, &mut es);
                    for el in es {
                        h = match el {
                            Elim::Arg(a) => {
                                let a = self.readback_closed(a, depth + 1, memo)?;
                                self.st.app(h, a)
                            }
                            Elim::Proj(s, i) => self.st.proj(s, i, h),
                        };
                    }
                }
                h
            }
        };
        memo.insert(v, e);
        Some(e)
    }

    fn closed_term_in(
        &mut self,
        mut e: ExprId,
        env: Env,
        ls: Ls,
        depth: u32,
        memo: &mut IdMap<V, ExprId>,
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
                ts.push(self.readback_closed(v, depth + 1, memo)?);
            }
            e = self.st.instantiate(e, &ts);
        }
        Some(e)
    }
}
