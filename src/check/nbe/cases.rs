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

use crate::env::DeclKind;
use crate::expr::{ExprId, ExprNode};
use crate::name::NameId;

use super::super::shape::{self, CasesInfo, Head, Heads, Minor, RecInfo, Src, Tree, TreeInfo};
use super::super::store::Store;
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
        if let Some(s) = self.case_shapes.get(&n) {
            return s.clone();
        }
        // A definition met again while its own shape is computed is not
        // one of these shapes.
        self.case_shapes.insert(n, CaseShape::Other);
        let s = self.compute_case_shape(n);
        self.case_shapes.insert(n, s.clone());
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
    fn ctor_of(&mut self, v: V) -> R<Option<(NameId, Vec<V>)>> {
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
        let mut args = Vec::new();
        if !self.a.args(sp, &mut args) {
            return Ok(None);
        }
        Ok(Some((c, args)))
    }

    /// The application `v` of a `casesOn` or matcher reduced to the chosen
    /// minor premise, applied, if its major premises are constructors.
    pub fn cases_direct(&mut self, v: V) -> R<Option<V>> {
        let Val::Const(n, ls, sp) = self.a.get(v) else {
            return Ok(None);
        };
        if sp == Sp::NIL {
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
        let mut args = Vec::new();
        if !self.a.args(sp, &mut args) {
            return Ok(None);
        }
        let dls = self.decl_ls(&d, ls);
        match s {
            CaseShape::Cases(ci) => self.cases_n(&ci, dls, &args),
            CaseShape::Tree(ti) => self.tree_n(&ti, dls, &args),
            _ => Ok(None),
        }
    }

    fn cases_n(&mut self, ci: &CasesInfo, dls: Ls, args: &[V]) -> R<Option<V>> {
        if args.len() < ci.arity {
            return Ok(None);
        }
        let Some((c, margs)) = self.ctor_of(args[ci.major])? else {
            return Ok(None);
        };
        let Some((_, nf, e, minor)) = ci.rules.iter().find(|r| r.0 == c) else {
            return Ok(None);
        };
        let (nf, e) = (*nf as usize, *e as usize);
        if nf > margs.len() || args.len() < ci.arity + e {
            return Ok(None);
        }
        let rest = &args[ci.arity..ci.arity + e];
        let tail = &args[ci.arity + e..];
        let (f, mut call) = match minor {
            Minor::Arg(l) => (args[*l], margs[margs.len() - nf..].to_vec()),
            Minor::Extra(j, ts) => {
                let ts = ts.iter().map(|&t| self.thunk(t, Env::NIL, dls)).collect();
                (rest[*j as usize], ts)
            }
            Minor::Closed(t) => (self.thunk(*t, Env::NIL, dls), Vec::new()),
            Minor::Var(l) => (args[*l], Vec::new()),
        };
        call.extend_from_slice(tail);
        Ok(Some(self.apply_all(f, &call)))
    }

    fn src(&mut self, s: Src, dls: Ls, args: &[V], levels: &[(V, Vec<V>)]) -> V {
        match s {
            Src::Arg(i) => args[i],
            Src::Field(l, f) => levels[l].1[f],
            Src::Major(l) => levels[l].0,
            Src::Closed(e) => self.thunk(e, Env::NIL, dls),
        }
    }

    fn tree_n(&mut self, ti: &TreeInfo, dls: Ls, args: &[V]) -> R<Option<V>> {
        if args.len() < ti.arity {
            return Ok(None);
        }
        let tail = &args[ti.arity..];
        let mut levels: Vec<(V, Vec<V>)> = Vec::new();
        let mut t = &ti.tree;
        loop {
            match t {
                Tree::Leaf(h, xs) => {
                    let f = self.src(*h, dls, args, &levels);
                    let mut call = Vec::with_capacity(xs.len() + tail.len());
                    for &x in xs.iter() {
                        call.push(self.src(x, dls, args, &levels));
                    }
                    call.extend_from_slice(tail);
                    return Ok(Some(self.apply_all(f, &call)));
                }
                Tree::Case(m, rules) => {
                    let mv = self.src(*m, dls, args, &levels);
                    let Some((c, margs)) = self.ctor_of(mv)? else {
                        return Ok(None);
                    };
                    let Some(r) = rules
                        .iter()
                        .find(|r| r.0 == c && r.1 as usize <= margs.len())
                    else {
                        return Ok(None);
                    };
                    let fields = margs[margs.len() - r.1 as usize..].to_vec();
                    levels.push((mv, fields));
                    t = &r.2;
                }
            }
        }
    }
}
