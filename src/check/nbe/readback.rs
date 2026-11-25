//! Values back to terms, for error messages only. Free variables become
//! the store's `FVar` terms, printed with the names of their binders.

use crate::expr::{ExprId, ExprNode};

use super::super::pp;
use super::super::tc::LocalDecl;
use super::val::{Elim, Env, Ls, V, Val};
use super::{BOTTOM, Nbe};

/// How deep a read back may go before it gives up on the rest.
const MAX_DEPTH: u32 = 64;

impl Nbe<'_> {
    /// `e` with its loose bound variables replaced by the read back values
    /// of `env` and its universe parameters by `ls`.
    fn term_in(&mut self, e: ExprId, env: Env, ls: Ls, depth: u32) -> ExprId {
        let mut e = e;
        if ls != super::val::Ls::ID {
            let (ps, lv) = self.ls_parts(ls);
            e = self.st.instantiate_lparams(e, &ps, &lv);
            self.ls_put(ps, lv);
        }
        if self.st.has_loose_bvars(e) {
            let mut vs = Vec::new();
            self.a.env_values(env, &mut vs);
            let n = self.st.data(e).loose_bvar_range() as usize;
            vs.truncate(n);
            let ts: Vec<ExprId> = vs.iter().map(|&v| self.readback_at(v, depth + 1)).collect();
            e = self.st.instantiate(e, &ts);
        }
        e
    }

    fn readback_at(&mut self, v: V, depth: u32) -> ExprId {
        if depth > MAX_DEPTH {
            return self.st.sort(crate::level::LevelId::ZERO);
        }
        match self.a.get(v) {
            Val::Sort(l) => self.st.sort(l),
            Val::Nat(lo, hi) => self.st.nat_u64((hi as u64) << 32 | lo as u64),
            Val::NatBig(i) => {
                let n = self.big(i).clone();
                self.st.nat(n)
            }
            Val::Str(s) => self.st.mk(ExprNode::Str(s)),
            Val::Lam(t, env, ls) | Val::Pi(t, env, ls) | Val::Thunk(t, env, ls) => {
                self.term_in(t, env, ls, depth)
            }
            Val::PiInfer(t, env, ls) => {
                // Print the λ's own binder and the inferred type of its body.
                let ExprNode::Lam(bi, n, d, b) = self.st.node(t) else {
                    unreachable!()
                };
                let dv = self.thunk(d, env, ls);
                let x = self.push_fvar(n, dv, None, bi);
                let env2 = self.a.cons(env, x);
                let body = match self.infer_term(b, env2, ls, true) {
                    Ok(bt) => self.readback_at(bt, depth + 1),
                    Err(_) => self.st.sort(crate::level::LevelId::ZERO),
                };
                let xt = self.readback_at(x, depth + 1);
                let dt = self.readback_at(dv, depth + 1);
                self.pop_fvar(x);
                let body = self.st.abstract_fvars(body, &[xt]);
                self.st.pi(bi, n, dt, body)
            }
            Val::Const(n, l, sp) => {
                let h = self.st.cnst(n, l);
                self.readback_spine(h, sp, depth)
            }
            Val::FVar(k, sp) => {
                let h = if k == BOTTOM {
                    let n = self.st.mk_name(crate::name::NameNode::Anon);
                    self.st.cnst(n, crate::level::LevelList::EMPTY)
                } else {
                    self.st.fvar(k)
                };
                self.readback_spine(h, sp, depth)
            }
        }
    }

    fn readback_spine(&mut self, mut h: ExprId, sp: super::val::Sp, depth: u32) -> ExprId {
        let mut es = Vec::new();
        self.a.elims(sp, &mut es);
        for e in es {
            h = match e {
                Elim::Arg(a) => {
                    let a = self.readback_at(a, depth + 1);
                    self.st.app(h, a)
                }
                Elim::Proj(s, i) => self.st.proj(s, i, h),
            };
        }
        h
    }

    pub fn readback(&mut self, v: V) -> ExprId {
        self.readback_at(v, 0)
    }

    /// `v` printed.
    pub fn pp(&mut self, v: V) -> String {
        let e = self.readback(v);
        self.pp_term(e)
    }

    /// A term over the open free variables, printed.
    pub fn pp_term(&mut self, e: ExprId) -> String {
        let dummy = self.st.sort(crate::level::LevelId::ZERO);
        let lctx: Vec<LocalDecl> = self
            .fvars
            .iter()
            .map(|f| LocalDecl {
                name: f.name,
                ty: dummy,
                val: None,
                bi: f.bi,
            })
            .collect();
        pp::pp(&self.st, &lctx, e)
    }
}
