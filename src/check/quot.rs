//! Quotients: `quot.cpp`. Lean's kernel adds `Quot`, `Quot.mk`,
//! `Quot.lift` and `Quot.ind` itself, with fixed types, once `Eq` is
//! declared as expected. An export lists the four as declarations; each
//! must have its expected name and type (up to binder names and binder
//! annotations, and with its own names for the universe parameters).

use crate::env::{Decl, DeclKind, QuotKind};
use crate::expr::{BinderInfo, ExprId, ExprNode};
use crate::level::{LevelId, LevelList};
use crate::name::NameId;

use super::inductive::alpha_eq;
use super::tc::{R, Tc, err};

impl Tc<'_> {
    fn arrow(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let b = self.st.lift_loose(b, 0, 1);
        self.st.pi(BinderInfo::Default, NameId::ANON, a, b)
    }

    fn local(&mut self, ty: ExprId, implicit: bool) -> ExprId {
        let bi = if implicit {
            BinderInfo::Implicit
        } else {
            BinderInfo::Default
        };
        self.push_local(NameId::ANON, ty, None, bi)
    }

    fn check_eq_type(&mut self) -> R<NameId> {
        let Some(eq) = self.ext.eq else {
            return err("failed to initialize quot module, environment does not have 'Eq' type");
        };
        let Some(d) = self.find(eq) else {
            return err("failed to initialize quot module, environment does not have 'Eq' type");
        };
        let DeclKind::Inductive { ctors, .. } = d.kind else {
            return err("failed to initialize quot module, environment does not have 'Eq' type");
        };
        let lps = self.st.lparams(&d).to_vec();
        if lps.len() != 1 {
            return err(
                "failed to initialize quot module, unexpected number of universe params at 'Eq' type",
            );
        }
        let cs = self.st.name_list(ctors).to_vec();
        if cs.len() != 1 {
            return err(
                "failed to initialize quot module, unexpected number of constructors for 'Eq' type",
            );
        }
        let u = self.st.param(lps[0]);
        let su = self.st.sort(u);
        let prop = self.st.sort(LevelId::ZERO);
        let alpha = self.local(su, true);
        let t = self.arrow(alpha, prop);
        let t = self.arrow(alpha, t);
        let want = self.mk_pi(&[alpha], t);
        if !alpha_eq(self, want, d.ty) {
            return err("failed to initialize quot module, 'Eq' has an unexpected type");
        }
        let refl = self.get(cs[0])?;
        let rl = self.st.lparams(&refl).to_vec();
        if rl.len() != 1 {
            return err(
                "failed to initialize quot module, unexpected type for 'Eq' type constructor",
            );
        }
        let u = self.st.param(rl[0]);
        let su = self.st.sort(u);
        let alpha = self.local(su, true);
        let a = self.local(alpha, false);
        let ls = self.st.mk_list(&[u]);
        let eqc = self.st.cnst(eq, ls);
        let body = self.st.apps(eqc, &[alpha, a, a]);
        let want = self.mk_pi(&[alpha, a], body);
        if !alpha_eq(self, want, refl.ty) {
            return err(
                "failed to initialize quot module, unexpected type for 'Eq' type constructor",
            );
        }
        Ok(eq)
    }

    /// Check one of the quotient declarations.
    pub fn check_quot(&mut self, d: &Decl, kind: QuotKind) -> R<()> {
        let Some(q) = self.ext.quot else {
            return err("unexpected quotient declaration");
        };
        let eq = self.check_eq_type()?;
        let want_name = match kind {
            QuotKind::Type => q.quot,
            QuotKind::Ctor => q.mk,
            QuotKind::Lift => q.lift,
            QuotKind::Ind => q.ind,
        };
        if d.name != want_name {
            return err(format!(
                "quotient declaration '{}' must be named '{}'",
                self.show(d.name),
                self.show(want_name)
            ));
        }
        let lps = self.st.lparams(d).to_vec();
        let nlps = if kind == QuotKind::Lift { 2 } else { 1 };
        if lps.len() != nlps || (nlps == 2 && lps[0] == lps[1]) {
            return err("quotient declaration with unexpected universe parameters");
        }
        // The declarations a quotient's type mentions come first.
        let needs: &[NameId] = match kind {
            QuotKind::Type => &[],
            QuotKind::Ctor | QuotKind::Lift => &[q.quot],
            QuotKind::Ind => &[q.quot, q.mk],
        };
        for &n in needs {
            match self.find(n) {
                Some(Decl {
                    kind: DeclKind::Quot { .. },
                    ..
                }) => {}
                _ => {
                    return err(format!(
                        "'{}' must be declared before '{}'",
                        self.show(n),
                        self.show(d.name)
                    ));
                }
            }
        }
        let u = self.st.param(lps[0]);
        let ul = self.st.mk_list(&[u]);
        let sort_u = self.st.sort(u);
        let prop = self.st.sort(LevelId::ZERO);
        let alpha = self.local(sort_u, true);
        let rel = {
            let t = self.arrow(alpha, prop);
            self.arrow(alpha, t)
        };
        let want = match kind {
            QuotKind::Type => {
                let r = self.local(rel, false);
                self.mk_pi(&[alpha, r], sort_u)
            }
            QuotKind::Ctor => {
                let r = self.local(rel, false);
                let a = self.local(alpha, false);
                let qc = self.st.cnst(q.quot, ul);
                let qr = self.st.apps(qc, &[alpha, r]);
                self.mk_pi(&[alpha, r, a], qr)
            }
            QuotKind::Lift => {
                let r = self.local(rel, true);
                let qc = self.st.cnst(q.quot, ul);
                let qr = self.st.apps(qc, &[alpha, r]);
                let v = self.st.param(lps[1]);
                let vl = self.st.mk_list(&[v]);
                let sort_v = self.st.sort(v);
                let beta = self.local(sort_v, true);
                let fty = self.arrow(alpha, beta);
                let f = self.local(fty, false);
                let a = self.local(alpha, false);
                let b = self.local(alpha, false);
                let rab = self.st.apps(r, &[a, b]);
                let eqc = self.st.cnst(eq, vl);
                let fa = self.st.app(f, a);
                let fb = self.st.app(f, b);
                let e = self.st.apps(eqc, &[beta, fa, fb]);
                let imp = self.arrow(rab, e);
                let sanity = self.mk_pi(&[a, b], imp);
                let tail = self.arrow(qr, beta);
                let tail = self.arrow(sanity, tail);
                self.mk_pi(&[alpha, r, beta, f], tail)
            }
            QuotKind::Ind => {
                let r = self.local(rel, true);
                let qc = self.st.cnst(q.quot, ul);
                let qr = self.st.apps(qc, &[alpha, r]);
                let bty = self.arrow(qr, prop);
                let beta = self.local(bty, true);
                let a = self.local(alpha, false);
                let mkc = self.st.cnst(q.mk, ul);
                let mka = self.st.apps(mkc, &[alpha, r, a]);
                let bmk = self.st.app(beta, mka);
                let all = self.mk_pi(&[a], bmk);
                let qv = self.local(qr, false);
                let bq = self.st.app(beta, qv);
                let tail = self.mk_pi(&[qv], bq);
                let tail = self.arrow(all, tail);
                self.mk_pi(&[alpha, r, beta], tail)
            }
        };
        if !alpha_eq(self, want, d.ty) {
            return err(format!(
                "quotient declaration '{}' has an unexpected type {}",
                self.show(d.name),
                self.pp(d.ty)
            ));
        }
        let _ = (ExprNode::BVar(0), LevelList::EMPTY);
        Ok(())
    }
}
