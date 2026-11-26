//! `casesOn`s and matchers reduced directly: a definition whose value has
//! the shape of a `casesOn` or of a matcher's nested `casesOn`s (see
//! `super::super::shape`) is recognised once per constant. Applied to a
//! major premise that is a constructor, it goes straight to the chosen
//! minor premise applied to the fields: unfolding it, then the `casesOn`s,
//! then reducing the recursor gives that same application, but builds the
//! motive and every minor premise on the way. Anything else (a major
//! premise that is not a constructor, a projection in the spine) unfolds
//! as before.

use std::rc::Rc;

use crate::env::{Decl, DeclKind};
use crate::expr::{ExprId, ExprNode};
use crate::level::LevelList;
use crate::name::NameId;

use super::super::shape::{self, CasesInfo, Head, Heads, Minor, RecInfo, Src, Tree, TreeInfo};
use super::super::store::{IdMap, Store, is_local};
use super::super::tc::R;
use super::Nbe;
use super::val::{Env, Ls, Sp, V, Val};

/// Whether `casesOn`s and matchers are reduced directly.
pub const CASES_DIRECT: bool = true;

/// What a constant is for `cases_direct`.
#[derive(Clone)]
pub enum CaseShape {
    Cases(Rc<CasesInfo>),
    Tree(Rc<TreeInfo>),
    Rec(Rc<RecInfo>),
    Ctor(u32),
    Other,
}

/// The shapes found, per constant.
#[derive(Default)]
pub struct CaseShapes {
    /// Constants of one of the shapes, recursors and constructors. Their
    /// terms may be the store's, so they go with it (`forget_terms`).
    known: IdMap<NameId, CaseShape>,
    /// Bit `n` for the environment's constant `n` of none of the shapes.
    /// That holds whatever the store, so it stays.
    none: Vec<u64>,
}

impl CaseShapes {
    pub fn forget_terms(&mut self) {
        self.known = IdMap::default();
    }

    #[inline]
    fn is_none(&self, n: NameId) -> bool {
        let i = n.0 as usize;
        !is_local(n.0)
            && self
                .none
                .get(i / 64)
                .is_some_and(|w| w >> (i % 64) & 1 != 0)
    }

    fn set_none(&mut self, n: NameId) {
        if is_local(n.0) {
            return;
        }
        let i = n.0 as usize;
        if self.none.len() <= i / 64 {
            self.none.resize(i / 64 + 1, 0);
        }
        self.none[i / 64] |= 1 << (i % 64);
    }
}

impl Heads for Nbe<'_> {
    fn st(&self) -> &Store<'_> {
        &self.st
    }

    fn head(&mut self, h: ExprId) -> Head {
        let ExprNode::Const(n, _) = self.st.node(h) else {
            return Head::Other;
        };
        match self.case_shape(n) {
            CaseShape::Cases(ci) => Head::Cases(ci),
            CaseShape::Rec(r) => Head::Rec(r),
            CaseShape::Ctor(np) => Head::Ctor(np),
            CaseShape::Tree(_) | CaseShape::Other => Head::Other,
        }
    }
}

impl Nbe<'_> {
    /// What the constant `n` is, computed once.
    pub fn case_shape(&mut self, n: NameId) -> CaseShape {
        if self.case_shapes.is_none(n) {
            return CaseShape::Other;
        }
        if let Some(s) = self.case_shapes.known.get(&n) {
            return s.clone();
        }
        // A definition met again while its own shape is computed is not
        // one of these shapes.
        self.case_shapes.known.insert(n, CaseShape::Other);
        let s = self.compute_case_shape(n);
        match &s {
            CaseShape::Other => {
                self.case_shapes.known.remove(&n);
                // Not recorded for a constant not visible (yet).
                if self.find(n).is_some() {
                    self.case_shapes.set_none(n);
                }
            }
            _ => {
                self.case_shapes.known.insert(n, s.clone());
            }
        }
        s
    }

    fn compute_case_shape(&mut self, n: NameId) -> CaseShape {
        let Some(d) = self.find(n) else {
            return CaseShape::Other;
        };
        match d.kind {
            DeclKind::Definition { .. } => {
                let Some(v) = self.unfold_value(&d) else {
                    return CaseShape::Other;
                };
                if let Some(ci) = shape::cases_shape(self, v) {
                    return CaseShape::Cases(Rc::new(ci));
                }
                match shape::tree_shape(self, v) {
                    Some(t) => CaseShape::Tree(Rc::new(t)),
                    None => CaseShape::Other,
                }
            }
            DeclKind::Constructor { num_params, .. } => CaseShape::Ctor(num_params),
            DeclKind::Recursor {
                num_params,
                num_indices,
                num_motives,
                num_minors,
                rules,
                k,
                ..
            } => {
                let Some(induct) = self.major_induct(n, &d) else {
                    return CaseShape::Other;
                };
                let rs: Vec<_> = self
                    .st
                    .rec_rules(rules)
                    .iter()
                    .map(|r| (r.ctor, r.nfields, r.rhs))
                    .collect();
                CaseShape::Rec(Rc::new(RecInfo {
                    major_idx: (num_params + num_motives + num_minors + num_indices) as usize,
                    pmm: (num_params + num_motives + num_minors) as usize,
                    nparams: num_params,
                    single: num_motives == 1 && num_minors as usize == rs.len(),
                    induct,
                    k,
                    rules: rs,
                }))
            }
            _ => CaseShape::Other,
        }
    }

    /// The major premise `v` as a constructor application: its constructor
    /// and arguments, if it reduces to one.
    fn ctor_of(&mut self, v: V) -> R<Option<(NameId, Sp)>> {
        let mut m = self.whnf(v)?;
        match self.a.get(m) {
            Val::Nat(..) | Val::NatBig(_) => m = self.nat_lit_to_constructor(m)?,
            Val::Str(_) => {
                let x = self.string_lit_to_constructor(m)?;
                m = self.whnf(x)?;
            }
            _ => {}
        }
        let Val::Const(c, _, sp) = self.a.get(m) else {
            return Ok(None);
        };
        Ok((!self.a.sp_has_proj(sp)).then_some((c, sp)))
    }

    /// The application `v` of a `casesOn` or matcher reduced to the chosen
    /// minor premise, applied, if its major premises are constructors.
    pub fn cases_direct(&mut self, v: V) -> R<Option<V>> {
        let Val::Const(n, ls, sp) = self.a.get(v) else {
            return Ok(None);
        };
        if sp == Sp::NIL || self.case_shapes.is_none(n) || self.a.sp_has_proj(sp) {
            return Ok(None);
        }
        let s = self.case_shape(n);
        if matches!(s, CaseShape::Rec(_) | CaseShape::Ctor(_) | CaseShape::Other) {
            return Ok(None);
        }
        let Some(d) = self.find(n) else {
            return Ok(None);
        };
        if self.st.list(ls).len() != d.level_params.len() {
            return Ok(None);
        }
        match s {
            CaseShape::Cases(ci) => self.cases_n(&ci, &d, ls, sp),
            CaseShape::Tree(ti) => {
                let dls = self.decl_ls(&d, ls);
                self.tree_n(&ti, dls, sp)
            }
            _ => Ok(None),
        }
    }

    fn cases_n(&mut self, ci: &CasesInfo, d: &Decl, ls: LevelList, sp: Sp) -> R<Option<V>> {
        let len = self.a.sp_len(sp);
        if (len as usize) < ci.arity {
            return Ok(None);
        }
        let Some((c, msp)) = self.ctor_of(self.a.sp_arg(sp, ci.major as u32))? else {
            return Ok(None);
        };
        let Some((_, nf, e, minor)) = ci.rules.iter().find(|r| r.0 == c) else {
            return Ok(None);
        };
        let mlen = self.a.sp_len(msp);
        let tail = ci.arity as u32 + e;
        if *nf > mlen || len < tail {
            return Ok(None);
        }
        let base = self.vargs.len();
        let f = match minor {
            Minor::Arg(l) => {
                self.a.extend_sp_args(msp, mlen - nf, mlen, &mut self.vargs);
                self.a.sp_arg(sp, *l as u32)
            }
            Minor::Extra(j, ts) => {
                let dls = self.decl_ls(d, ls);
                for &t in ts {
                    let a = self.thunk(t, Env::NIL, dls);
                    self.vargs.push(a);
                }
                self.a.sp_arg(sp, ci.arity as u32 + j)
            }
            Minor::Closed(t) => {
                let dls = self.decl_ls(d, ls);
                self.thunk(*t, Env::NIL, dls)
            }
            Minor::Var(l) => self.a.sp_arg(sp, *l as u32),
        };
        self.a.extend_sp_args(sp, tail, len, &mut self.vargs);
        let r = self.apply_n(f, base);
        self.vargs.truncate(base);
        Ok(Some(r))
    }

    fn src(&mut self, s: Src, dls: Ls, sp: Sp, levels: &[(V, Sp, u32)]) -> V {
        match s {
            Src::Arg(i) => self.a.sp_arg(sp, i as u32),
            Src::Field(l, f) => {
                let (_, msp, start) = levels[l];
                self.a.sp_arg(msp, start + f as u32)
            }
            Src::Major(l) => levels[l].0,
            Src::Closed(e) => self.thunk(e, Env::NIL, dls),
        }
    }

    fn tree_n(&mut self, ti: &TreeInfo, dls: Ls, sp: Sp) -> R<Option<V>> {
        let len = self.a.sp_len(sp);
        if (len as usize) < ti.arity {
            return Ok(None);
        }
        let mut levels = Vec::new();
        let mut t = &ti.tree;
        loop {
            match t {
                Tree::Leaf(h, xs) => {
                    let f = self.src(*h, dls, sp, &levels);
                    let base = self.vargs.len();
                    for &x in xs.iter() {
                        let a = self.src(x, dls, sp, &levels);
                        self.vargs.push(a);
                    }
                    self.a
                        .extend_sp_args(sp, ti.arity as u32, len, &mut self.vargs);
                    let r = self.apply_n(f, base);
                    self.vargs.truncate(base);
                    return Ok(Some(r));
                }
                Tree::Case(m, rules) => {
                    let mv = self.src(*m, dls, sp, &levels);
                    let Some((c, msp)) = self.ctor_of(mv)? else {
                        return Ok(None);
                    };
                    let mlen = self.a.sp_len(msp);
                    let Some(r) = rules.iter().find(|r| r.0 == c && r.1 <= mlen) else {
                        return Ok(None);
                    };
                    levels.push((mv, msp, mlen - r.1));
                    t = &r.2;
                }
            }
        }
    }
}
