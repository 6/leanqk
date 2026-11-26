//! Where metadata changes the verdict of Lean's kernel.
//!
//! The interned terms leave metadata out: it never matters to typing or
//! reduction. But some checks of Lean's kernel on an inductive block, and its
//! check of `Eq` before the quotient declarations, compare terms
//! syntactically, and there an `mdata` node is not what it wraps. These
//! functions redo those checks on the terms as exported, for the records that
//! contain metadata (`State::mdata`), and record a failure in
//! `Env::mdata_errors` (or `Env::mdata_types`) for the checker to report.

use hashbrown::HashSet;

use super::{R, RawExpr, State};
use crate::env::DeclKind;
use crate::expr::{ExprId, ExprNode};
use crate::name::NameId;

/// A term as exported: an export id whose record contains metadata, or an
/// interned term (which has none).
#[derive(Clone, Copy)]
enum Ref {
    Raw(u64),
    Int(ExprId),
}

/// One node of a [`Ref`], with metadata nodes kept.
#[derive(Clone, Copy)]
enum Node {
    MData(Ref),
    App(Ref, Ref),
    Pi(Ref, Ref),
    Lam(Ref, Ref),
    Let(Ref, Ref, Ref),
    BVar(u64),
    Const(NameId),
    Other,
}

impl State {
    fn mdata_ref(&mut self, id: u64) -> R<Ref> {
        Ok(if self.mdata.contains_key(&id) {
            Ref::Raw(id)
        } else {
            Ref::Int(self.root(id)?)
        })
    }

    fn mdata_node(&mut self, r: Ref) -> R<Node> {
        let e = match r {
            Ref::Raw(id) => match self.mdata.get(&id).map(|m| m.1) {
                Some(raw) => {
                    return Ok(match raw {
                        RawExpr::MData(x) => Node::MData(self.mdata_ref(x)?),
                        RawExpr::App(f, a) => Node::App(self.mdata_ref(f)?, self.mdata_ref(a)?),
                        RawExpr::Binder { pi, ty, body, .. } => {
                            let (t, b) = (self.mdata_ref(ty)?, self.mdata_ref(body)?);
                            if pi { Node::Pi(t, b) } else { Node::Lam(t, b) }
                        }
                        RawExpr::Let {
                            ty, value, body, ..
                        } => Node::Let(
                            self.mdata_ref(ty)?,
                            self.mdata_ref(value)?,
                            self.mdata_ref(body)?,
                        ),
                        RawExpr::BVar(i) => Node::BVar(i),
                        _ => Node::Other,
                    });
                }
                None => self.root(id)?,
            },
            Ref::Int(e) => e,
        };
        Ok(match self.env.exprs.get(e) {
            ExprNode::App(f, a) => Node::App(Ref::Int(f), Ref::Int(a)),
            ExprNode::Pi(_, _, t, b) => Node::Pi(Ref::Int(t), Ref::Int(b)),
            ExprNode::Lam(_, _, t, b) => Node::Lam(Ref::Int(t), Ref::Int(b)),
            ExprNode::BVar(i) => Node::BVar(i as u64),
            ExprNode::Const(n, _) => Node::Const(n),
            _ => Node::Other,
        })
    }

    /// The term without its metadata, interned.
    fn mdata_stripped(&mut self, r: Ref) -> R<ExprId> {
        match r {
            Ref::Raw(id) => self.root(id),
            Ref::Int(e) => Ok(e),
        }
    }

    /// `r` as Lean's `get_app_args` sees it: the head and the arguments,
    /// stopping at a metadata node.
    fn mdata_spine(&mut self, mut r: Ref, args: &mut Vec<Ref>) -> R<Node> {
        args.clear();
        loop {
            match self.mdata_node(r)? {
                Node::App(f, a) => {
                    args.push(a);
                    r = f;
                }
                n => {
                    args.reverse();
                    return Ok(n);
                }
            }
        }
    }

    /// Whether the interned `e` mentions one of `names`.
    fn mentions(&self, e: ExprId, names: &[NameId], seen: &mut HashSet<ExprId>) -> bool {
        let mut stack = vec![e];
        while let Some(e) = stack.pop() {
            if !seen.insert(e) {
                continue;
            }
            match self.env.exprs.get(e) {
                ExprNode::Const(n, _) if names.contains(&n) => return true,
                ExprNode::App(f, a) => stack.extend([f, a]),
                ExprNode::Pi(_, _, t, b) | ExprNode::Lam(_, _, t, b) => stack.extend([t, b]),
                ExprNode::Let(l, b) => {
                    let l = self.env.exprs.let_binder(l);
                    stack.extend([l.ty, l.value, b]);
                }
                ExprNode::Proj(_, _, x) => stack.push(x),
                _ => {}
            }
        }
        false
    }

    /// Lean's `check_uniform_ind_occs` on the constructor type `ty`, with its
    /// metadata: an occurrence of a type of the block applied to at most
    /// `nparams` arguments must be applied to exactly the parameters, as bound
    /// variables. Only the occurrences metadata hides from the interned term
    /// are looked at; the checker checks the others. True if one fails.
    fn mdata_nonuniform(&mut self, ty: u64, names: &[NameId], nparams: u32) -> R<bool> {
        let np = nparams as usize;
        let mut args = Vec::new();
        let mut stack = vec![(Ref::Raw(ty), 0u64)];
        while let Some((r, off)) = stack.pop() {
            if let Node::Const(n) = self.mdata_spine(r, &mut args)?
                && names.contains(&n)
                && args.len() <= np
            {
                let mut ok = args.len() == np && off >= np as u64;
                for (i, &a) in args.iter().enumerate() {
                    ok = ok
                        && matches!(self.mdata_node(a)?, Node::BVar(j) if j + 1 + i as u64 == off);
                }
                if !ok {
                    return Ok(true);
                }
                continue;
            }
            // Below an interned term, the interned check sees what Lean sees.
            if let Ref::Raw(_) = r {
                match self.mdata_node(r)? {
                    Node::MData(x) => stack.push((x, off)),
                    Node::App(f, a) => stack.extend([(f, off), (a, off)]),
                    Node::Pi(t, b) | Node::Lam(t, b) => stack.extend([(t, off), (b, off + 1)]),
                    Node::Let(t, v, b) => stack.extend([(t, off), (v, off), (b, off + 1)]),
                    _ => {}
                }
            }
        }
        Ok(false)
    }

    /// Whether `t`, a type checked for positivity, is an application of an
    /// inductive type `J` declared earlier whose parameters mention `names`
    /// (a nested occurrence, for the interned term) with metadata in its
    /// head before the last parameter. Lean's kernel then does not see a
    /// nested occurrence, and its positivity check fails.
    fn mdata_hidden_nested(&mut self, t: Ref, names: &[NameId]) -> R<bool> {
        let mut args = Vec::new();
        let mut r = t;
        // The arguments outside the innermost metadata node of the head.
        let mut outside = 0;
        loop {
            match self.mdata_spine(r, &mut args)? {
                Node::MData(x) => {
                    outside += args.len();
                    r = x;
                }
                Node::Const(n) => {
                    let inner = args.len();
                    let total = inner + outside;
                    let Some(i) = self.env.by_name.get(&n) else {
                        return Ok(false);
                    };
                    let DeclKind::Inductive { num_params, .. } = self.env.decls[i as usize].kind
                    else {
                        return Ok(false);
                    };
                    let np = num_params as usize;
                    if outside == 0 || inner >= np || total < np {
                        return Ok(false);
                    }
                    // The interned parameters: those inside, then the first
                    // ones outside.
                    let whole = self.mdata_stripped(t)?;
                    let mut ps = Vec::new();
                    let mut e = whole;
                    while let ExprNode::App(f, a) = self.env.exprs.get(e) {
                        ps.push(a);
                        e = f;
                    }
                    ps.reverse();
                    let mut seen = HashSet::new();
                    return Ok(ps[..np].iter().any(|&p| self.mentions(p, names, &mut seen)));
                }
                _ => return Ok(false),
            }
        }
    }

    /// Whether the interned `e` mentions one of the type annotations Lean's
    /// `consume_type_annotations` takes off a binder's type.
    fn mentions_annotation(&self, e: ExprId) -> bool {
        let mut stack = vec![e];
        let mut seen = HashSet::new();
        while let Some(e) = stack.pop() {
            if !seen.insert(e) {
                continue;
            }
            match self.env.exprs.get(e) {
                ExprNode::Const(n, _) => {
                    let s = self.env.names.display(n).to_string();
                    if ["optParam", "autoParam", "outParam", "semiOutParam"].contains(&s.as_str()) {
                        return true;
                    }
                }
                ExprNode::App(f, a) => stack.extend([f, a]),
                ExprNode::Pi(_, _, t, b) | ExprNode::Lam(_, _, t, b) => stack.extend([t, b]),
                ExprNode::Let(l, b) => {
                    let l = self.env.exprs.let_binder(l);
                    stack.extend([l.ty, l.value, b]);
                }
                ExprNode::Proj(_, _, x) => stack.push(x),
                _ => {}
            }
        }
        false
    }

    /// Lean's checks that see metadata, on an inductive block whose types
    /// and constructors have these names and exported types. Returns whether
    /// a constructor type has metadata that Lean's kernel copies into the
    /// recursors it derives: in the type of a parameter or index of a type
    /// or of a constructor's field (unless it has a type annotation, which
    /// Lean takes off), or in an index of a constructor's result type.
    pub(super) fn check_block_mdata(
        &mut self,
        types: &[(NameId, u64)],
        ctors: &[(NameId, u64)],
        nparams: u32,
    ) -> R<bool> {
        let mut copied = false;
        let names: Vec<NameId> = types.iter().map(|t| t.0).collect();
        for &(n, ty) in types.iter().chain(ctors) {
            if self.mdata.contains_key(&ty) {
                self.env.mdata_types.insert(n);
            }
        }
        // `get_params` of Lean's `elim_nested_inductive`: the parameters of
        // the first type are taken from its binders without reducing it.
        if let Some(&(n, ty)) = types.first()
            && self.mdata.contains_key(&ty)
        {
            let mut r = Ref::Raw(ty);
            for _ in 0..nparams {
                match self.mdata_node(r)? {
                    Node::Pi(_, b) => r = b,
                    Node::MData(_) => {
                        self.env.mdata_errors.insert(
                            n,
                            "invalid inductive datatype declaration, incorrect number of parameters (metadata over a parameter's binder)",
                        );
                        break;
                    }
                    _ => break,
                }
            }
        }
        // The binder types of the parameters (of the first type) and of the
        // indices (of every type), past the metadata over the binders,
        // which Lean's kernel reduces away: they are the recursors'.
        for (k, &(_, ty)) in types.iter().enumerate() {
            let mut r = Ref::Raw(ty);
            let mut i = 0u32;
            loop {
                match self.mdata_node(r)? {
                    Node::MData(x) => r = x,
                    Node::Pi(d, b) => {
                        if (k == 0 || i >= nparams)
                            && let Ref::Raw(_) = d
                        {
                            let e = self.mdata_stripped(d)?;
                            copied |= !self.mentions_annotation(e);
                        }
                        r = b;
                        i += 1;
                    }
                    _ => break,
                }
            }
        }
        for &(n, ty) in ctors {
            if !self.mdata.contains_key(&ty) || self.env.mdata_errors.contains_key(&n) {
                continue;
            }
            if self.mdata_nonuniform(ty, &names, nparams)? {
                self.env.mdata_errors.insert(
                    n,
                    "invalid occurrence of a datatype being declared: it must be applied to the parameters and universe levels of the mutual declaration (metadata hides a parameter)",
                );
                continue;
            }
            // Positivity of the fields: each field's type, through its
            // metadata at the root and its codomains, as Lean's
            // `check_positivity` reduces it.
            let mut r = Ref::Raw(ty);
            let mut i = 0u32;
            while let Node::Pi(d, b) = self.mdata_node(r)? {
                if i >= nparams
                    && let Ref::Raw(_) = d
                {
                    let e = self.mdata_stripped(d)?;
                    copied |= !self.mentions_annotation(e);
                }
                if i >= nparams {
                    let mut t = d;
                    loop {
                        match self.mdata_node(t)? {
                            Node::MData(x) => t = x,
                            Node::Pi(_, b) => t = b,
                            _ => break,
                        }
                    }
                    if let Ref::Raw(_) = t
                        && self.mdata_hidden_nested(t, &names)?
                    {
                        self.env.mdata_errors.insert(
                            n,
                            "a field contains a non valid occurrence of the datatypes being declared (metadata hides a nested occurrence)",
                        );
                        break;
                    }
                }
                r = b;
                i += 1;
            }
            if i >= nparams {
                let mut args = Vec::new();
                self.mdata_spine(r, &mut args)?;
                copied |= args
                    .iter()
                    .skip(nparams as usize)
                    .any(|a| matches!(a, Ref::Raw(_)));
            }
        }
        Ok(copied)
    }
}
