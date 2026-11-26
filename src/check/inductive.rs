//! Inductive declarations: a port of `inductive.cpp` (Lean v4.36.0),
//! including the elimination of nested occurrences into auxiliary types
//! and their restoration, and the defensive checks of v4.36.0 (uniform
//! occurrences of the types being declared, type-preserving computation
//! rules, re-checking restored terms). lean4lean's `Inductive/Add.lean`
//! follows the same code and was a useful second reading.
//!
//! An export carries each mutual block whole: its types, constructors and
//! recursors. Only the types and the constructor types are taken from it.
//! Everything else (the inductive types' flags, the constructors' fields,
//! and the recursors with their rules) is derived here, as Lean does, and
//! then compared with what the export says; any difference, including an
//! extra or missing declaration, rejects the block. Types are compared up
//! to binder names and binder annotations, which do not affect meaning.

use crate::env::{Decl, DeclKind, RecRule};
use crate::expr::{BinderInfo, ExprId, ExprNode};
use crate::level::{LevelId, LevelList, LevelNode};
use crate::name::{NameId, NameNode};

use super::store::{IdMap, IdSet, is_local};
use super::tc::{KErr, Mode, R, Tc, err};
use super::univ;

/// The rewriting callback of `replace`: given a subterm and the number of
/// binders above it, a replacement, or `None` to descend.
type ReplaceFn<'a, T> = dyn FnMut(&mut T, ExprId, u32) -> R<Option<ExprId>> + 'a;

#[derive(Clone, Debug)]
pub struct IndType {
    pub name: NameId,
    pub ty: ExprId,
    pub ctors: Vec<(NameId, ExprId)>,
}

#[derive(Clone, Debug)]
pub struct IndDecl {
    pub lparams: Vec<NameId>,
    pub nparams: u32,
    pub types: Vec<IndType>,
    pub is_unsafe: bool,
}

/// Root of the names given to auxiliary types: a numeric name no export
/// is likely to use, and checked for freshness anyway.
const AUX_ROOT: u64 = 0x6c71_6b5f_6e65_7374;

/// Names the derived recursors get.
pub struct RecNaming {
    /// The universe parameter of large elimination, as the export names it.
    pub elim_param: Option<NameId>,
}

impl Tc<'_> {
    pub fn rec_name_of(&mut self, ty: NameId) -> R<NameId> {
        if self.is_aux_name(ty) {
            return Ok(self.st.mk_name(NameNode::Num(ty, 0)));
        }
        let Some(s) = self.st.env.names.strings.find("rec") else {
            return err(format!("missing recursor '{}.rec'", self.show(ty)));
        };
        Ok(self.st.mk_name(NameNode::Str(ty, s)))
    }

    fn aux_root(&mut self) -> NameId {
        let a = self.st.mk_name(NameNode::Num(NameId::ANON, AUX_ROOT));
        self.st.mk_name(NameNode::Num(a, AUX_ROOT))
    }

    fn is_aux_name(&mut self, n: NameId) -> bool {
        let r = self.aux_root();
        n != r && self.st.is_prefix_of(r, n)
    }

    /// Whether `e` mentions a constant satisfying `pred`.
    fn find_const(&self, e: ExprId, pred: &dyn Fn(NameId) -> bool) -> bool {
        let mut seen = IdSet::<ExprId>::with_capacity_and_hasher(SEEN, Default::default());
        let mut stack = vec![e];
        while let Some(e) = stack.pop() {
            if !seen.insert(e) {
                continue;
            }
            match self.st.node(e) {
                ExprNode::Const(n, _) => {
                    if pred(n) {
                        return true;
                    }
                }
                ExprNode::App(f, a) => stack.extend([f, a]),
                ExprNode::Lam(_, _, t, b) | ExprNode::Pi(_, _, t, b) => stack.extend([t, b]),
                ExprNode::Let(h, b) => {
                    let lb = self.st.let_binder(h);
                    stack.extend([lb.ty, lb.value, b]);
                }
                ExprNode::Proj(_, _, x) => stack.push(x),
                _ => {}
            }
        }
        false
    }

    /// Lean's `consume_type_annotations`: strip `optParam`, `autoParam`,
    /// `outParam` and `semiOutParam` (by name, as Lean does).
    fn consume_type_annotations(&self, mut e: ExprId) -> ExprId {
        loop {
            let ExprNode::App(f, last) = self.st.node(e) else {
                return e;
            };
            let (head, domain, two_args) = match self.st.node(f) {
                ExprNode::App(head, first) => (head, first, true),
                _ => (f, last, false),
            };
            let ExprNode::Const(name, _) = self.st.node(head) else {
                return e;
            };
            if is_local(name.0) {
                return e;
            }
            let NameNode::Str(NameId::ANON, name) = self.st.env.names.get(name) else {
                return e;
            };
            match (two_args, self.st.str(name)) {
                (true, "optParam" | "autoParam") | (false, "outParam" | "semiOutParam") => {
                    e = domain;
                }
                _ => return e,
            }
        }
    }

    fn local_for(&mut self, pi: ExprId) -> (ExprId, ExprId) {
        let ExprNode::Pi(bi, n, d, b) = self.st.node(pi) else {
            unreachable!()
        };
        let fv = self.local_with_annotations(n, d, bi);
        (fv, self.st.instantiate1(b, fv))
    }

    fn local_with_annotations(&mut self, n: NameId, ty: ExprId, bi: BinderInfo) -> ExprId {
        let ty = self.consume_type_annotations(ty);
        self.push_local(n, ty, None, bi)
    }

    fn local_named(&mut self, n: NameId, ty: ExprId) -> ExprId {
        self.local_with_annotations(n, ty, BinderInfo::Default)
    }

    /// Generic top-down replacement with memo on (subterm, depth).
    fn replace(
        &mut self,
        e: ExprId,
        off: u32,
        f: &mut ReplaceFn<'_, Self>,
        memo: &mut IdMap<(ExprId, u32), ExprId>,
    ) -> R<ExprId> {
        if let Some(&r) = memo.get(&(e, off)) {
            return Ok(r);
        }
        if let Some(r) = f(self, e, off)? {
            memo.insert((e, off), r);
            return Ok(r);
        }
        let r = match self.st.node(e) {
            ExprNode::App(a, b) => {
                let a = self.replace(a, off, f, memo)?;
                let b = self.replace(b, off, f, memo)?;
                self.st.app(a, b)
            }
            ExprNode::Lam(bi, n, t, b) => {
                let t = self.replace(t, off, f, memo)?;
                let b = self.replace(b, off + 1, f, memo)?;
                self.st.lam(bi, n, t, b)
            }
            ExprNode::Pi(bi, n, t, b) => {
                let t = self.replace(t, off, f, memo)?;
                let b = self.replace(b, off + 1, f, memo)?;
                self.st.pi(bi, n, t, b)
            }
            ExprNode::Let(h, b) => {
                let lb = self.st.let_binder(h);
                let t = self.replace(lb.ty, off, f, memo)?;
                let v = self.replace(lb.value, off, f, memo)?;
                let b = self.replace(b, off + 1, f, memo)?;
                self.st.mk_let(lb.name, t, v, b)
            }
            ExprNode::Proj(s, i, x) => {
                let x = self.replace(x, off, f, memo)?;
                self.st.proj(s, i, x)
            }
            _ => e,
        };
        memo.insert((e, off), r);
        Ok(r)
    }

    fn param_levels(&mut self, lparams: &[NameId]) -> LevelList {
        let ls: Vec<LevelId> = lparams.iter().map(|&p| self.st.param(p)).collect();
        self.st.mk_list(&ls)
    }

    /// Lean's `check_uniform_ind_occs`.
    fn check_uniform_ind_occs(
        &mut self,
        d: &IndDecl,
        names: &[NameId],
        occs: &mut IndOccurrences,
    ) -> R<()> {
        let nparams = d.nparams;
        let lvls = self.param_levels(&d.lparams);
        let mut seen = IdSet::<(ExprId, u32)>::default();
        let mut stack = Vec::new();
        let mut args = Vec::new();
        for t in &d.types {
            for &(cn, ct) in &t.ctors {
                stack.push((ct, 0u32));
                while let Some((e, off)) = stack.pop() {
                    if !occs.contains(self, e, names) || !seen.insert((e, off)) {
                        continue;
                    }
                    let h = self.st.spine(e, &mut args);
                    if let ExprNode::Const(n, ls) = self.st.node(h)
                        && names.contains(&n)
                    {
                        let np = nparams as usize;
                        if args.len() < np
                            || off < nparams
                            || ls != lvls
                            || args[..np].iter().enumerate().any(|(i, &a)| {
                                self.st.node(a) != ExprNode::BVar(off - 1 - i as u32)
                            })
                        {
                            return err(format!(
                                "invalid occurrence of datatype '{}' being declared in '{}': it must be applied to the parameters and universe levels of the mutual declaration",
                                self.show(n),
                                self.show(cn)
                            ));
                        }
                        stack.extend(args[np..].iter().map(|&a| (a, off)));
                        continue;
                    }
                    stack.extend(args.iter().map(|&a| (a, off)));
                    match self.st.node(h) {
                        ExprNode::Lam(_, _, ty, b) | ExprNode::Pi(_, _, ty, b) => {
                            stack.push((ty, off));
                            stack.push((b, off + 1));
                        }
                        ExprNode::Let(h, b) => {
                            let lb = self.st.let_binder(h);
                            stack.push((lb.ty, off));
                            stack.push((lb.value, off));
                            stack.push((b, off + 1));
                        }
                        ExprNode::Proj(_, _, x) => stack.push((x, off)),
                        _ => {}
                    }
                }
            }
        }
        Ok(())
    }

    fn check_no_nested_aux(&self, e: ExprId, what: NameId) -> R<()> {
        let Some(s) = self.st.env.names.strings.find("_nested") else {
            return Ok(());
        };
        let Some(pre) = self.st.env.names.find(NameNode::Str(NameId::ANON, s)) else {
            return Ok(());
        };
        let mut seen = IdSet::<ExprId>::with_capacity_and_hasher(SEEN, Default::default());
        let mut stack = vec![e];
        while let Some(e) = stack.pop() {
            if !seen.insert(e) {
                continue;
            }
            let bad = match self.st.node(e) {
                ExprNode::Const(n, _) => self.st.is_prefix_of(pre, n),
                ExprNode::Proj(n, _, x) => {
                    stack.push(x);
                    self.st.is_prefix_of(pre, n)
                }
                ExprNode::App(f, a) => {
                    stack.extend([f, a]);
                    false
                }
                ExprNode::Lam(_, _, t, b) | ExprNode::Pi(_, _, t, b) => {
                    stack.extend([t, b]);
                    false
                }
                ExprNode::Let(h, b) => {
                    let lb = self.st.let_binder(h);
                    stack.extend([lb.ty, lb.value, b]);
                    false
                }
                _ => false,
            };
            if bad {
                return err(format!(
                    "invalid declaration '{}', it uses the reserved prefix '_nested'",
                    self.show(what)
                ));
            }
        }
        Ok(())
    }

    /// Check an inductive declaration and derive its declarations, in the
    /// order: types, constructors, recursors (the auxiliary recursors of
    /// nested occurrences last). On success the derived declarations are
    /// left in `pending`.
    /// `pre` checks a closed type of the environment's (a type of the
    /// block, or a constructor's, under the block's universe parameters)
    /// with the first `k` declarations of the block visible, if it can:
    /// what it accepts, `Tc` need not check (see `AddInd::check_closed`).
    pub fn add_inductive(
        &mut self,
        d: &IndDecl,
        naming: &RecNaming,
        pre: Option<&mut PreCheck<'_>>,
    ) -> R<Vec<Decl>> {
        if d.types.is_empty() {
            return err("invalid empty (mutual) inductive datatype declaration");
        }
        for t in &d.types {
            self.check_no_nested_aux(t.ty, t.name)?;
            for &(cn, ct) in &t.ctors {
                self.check_no_nested_aux(ct, cn)?;
            }
        }
        check_dup_lparams(self, &d.lparams)?;
        let names: Vec<NameId> = d.types.iter().map(|t| t.name).collect();
        let mut occs = IndOccurrences::default();
        self.check_uniform_ind_occs(d, &names, &mut occs)?;
        let nested = ElimNested::run(self, d, &names, &mut occs)?;
        let nnested = nested.aux.len() as u32;
        let mut add = AddInd::new(self, &nested.decl, nnested, naming);
        if nnested == 0 {
            add.occs = occs;
            add.pre = pre.map(|p| -> &mut PreCheck<'_> { p });
        }
        let aux_decls = add.run()?;
        if nnested == 0 {
            return Ok(aux_decls);
        }
        nested.restore_all(self, d, &aux_decls)
    }
}

fn check_dup_lparams(tc: &Tc<'_>, ps: &[NameId]) -> R<()> {
    for (i, p) in ps.iter().enumerate() {
        if ps[i + 1..].contains(p) {
            return err(format!(
                "failed to add declaration to environment, duplicate universe level parameter: '{}'",
                tc.show(*p)
            ));
        }
    }
    Ok(())
}

/// Syntactic constant occurrences for one fixed set of inductive names.
#[derive(Default)]
struct IndOccurrences(IdMap<ExprId, bool>);

impl IndOccurrences {
    fn contains(&mut self, tc: &Tc<'_>, e: ExprId, names: &[NameId]) -> bool {
        self.contains_at(tc, e, names, 0)
    }

    fn contains_at(&mut self, tc: &Tc<'_>, e: ExprId, names: &[NameId], depth: u32) -> bool {
        let node = tc.st.node(e);
        match node {
            ExprNode::Const(n, _) => return names.contains(&n),
            ExprNode::App(..)
            | ExprNode::Pi(..)
            | ExprNode::Lam(..)
            | ExprNode::Let(..)
            | ExprNode::Proj(..) => {}
            _ => return false,
        }
        if let Some(&found) = self.0.get(&e) {
            return found;
        }
        // Fall back to the iterative walk for deeply nested syntax.
        let found = if depth == 64 {
            tc.find_const(e, &|n| names.contains(&n))
        } else {
            let mut child = |c| self.contains_at(tc, c, names, depth + 1);
            match node {
                ExprNode::App(f, a) => child(f) || child(a),
                ExprNode::Lam(_, _, t, b) | ExprNode::Pi(_, _, t, b) => child(t) || child(b),
                ExprNode::Let(h, b) => {
                    let lb = tc.st.let_binder(h);
                    child(lb.ty) || child(lb.value) || child(b)
                }
                ExprNode::Proj(_, _, x) => child(x),
                _ => unreachable!(),
            }
        };
        self.0.insert(e, found);
        found
    }
}

struct RecInfo {
    c: ExprId,
    minors: Vec<ExprId>,
    indices: Vec<ExprId>,
    major: ExprId,
}

/// Parameters, motives and minors are bound in the same order in every
/// recursor type and rule of a mutual block.
struct RecTelescope {
    locals: Vec<ExprId>,
    domains: Vec<(BinderInfo, NameId, ExprId)>,
}

impl RecTelescope {
    fn new(tc: &mut Tc<'_>, locals: Vec<ExprId>) -> Self {
        let mut domains = Vec::with_capacity(locals.len());
        for (i, &var) in locals.iter().enumerate() {
            let local = tc.fvar_decl(var).expect("recursor parameter");
            let ty = tc.st.abstract_fvars(local.ty, &locals[..i]);
            domains.push((local.bi, local.name, ty));
        }
        Self { locals, domains }
    }

    fn bind(&mut self, tc: &mut Tc<'_>, suffix: &[ExprId], body: ExprId, lambda: bool) -> ExprId {
        self.locals.extend_from_slice(suffix);
        let mut body = tc.st.abstract_fvars(body, &self.locals);
        for (i, &var) in self.locals.iter().enumerate().rev() {
            let (bi, name, ty) = self.domains.get(i).copied().unwrap_or_else(|| {
                let local = tc.fvar_decl(var).expect("recursor binder");
                let ty = tc.st.abstract_fvars(local.ty, &self.locals[..i]);
                (local.bi, local.name, ty)
            });
            body = if lambda {
                tc.st.lam(bi, name, ty, body)
            } else {
                tc.st.pi(bi, name, ty, body)
            };
        }
        self.locals.truncate(self.domains.len());
        body
    }
}

/// A check of a closed type `e` under universe parameters `ps`, with the
/// first `k` declarations of the block visible: whether it passed.
pub type PreCheck<'p> = dyn FnMut(ExprId, &[NameId], u32) -> bool + 'p;

/// Whether the recursors made are type-checked, and their computation
/// rules checked to preserve types. Lean does neither: they are made
/// well-typed, and must be the export's own (`compare_decl`).
const CHECK_RECURSORS: bool = false;

/// Whether a constructor's fields (and a recursive field's telescope) are
/// made once for the recursors' types and rules: each binds them.
const FIELDS_ONCE: bool = true;

/// Room made at once in the visited sets of the traversals here: most
/// terms they walk are small, and a set grown from empty rehashes at
/// every doubling.
const SEEN: usize = 64;

/// Whether `ElimNested::run` first looks for what it would replace, and
/// leaves a block with nothing to replace as it is.
const NESTED_SCAN: bool = true;

/// Lean's `add_inductive_fn`.
struct AddInd<'a, 'e> {
    tc: &'a mut Tc<'e>,
    pre: Option<&'a mut PreCheck<'a>>,
    lparams: Vec<NameId>,
    levels: LevelList,
    nparams: usize,
    is_unsafe: bool,
    types: Vec<IndType>,
    nindices: Vec<u32>,
    result_level: LevelId,
    is_not_zero: bool,
    params: Vec<ExprId>,
    ind_consts: Vec<ExprId>,
    ind_names: Vec<NameId>,
    occs: IndOccurrences,
    elim_level: LevelId,
    elim_param: Option<NameId>,
    k_target: bool,
    nnested: u32,
    rec_infos: Vec<RecInfo>,
    rec_names: Vec<NameId>,
    out: Vec<Decl>,
    /// `ctor_fields` with recursive fields, by constructor type.
    fields: IdMap<ExprId, (Vec<ExprId>, Vec<ExprId>, ExprId)>,
    /// `rec_field_telescope`, by recursive field.
    teles: IdMap<ExprId, (Vec<ExprId>, ExprId)>,
}

impl<'a, 'e> AddInd<'a, 'e> {
    fn new(tc: &'a mut Tc<'e>, d: &IndDecl, nnested: u32, naming: &RecNaming) -> Self {
        let levels = tc.param_levels(&d.lparams);
        AddInd {
            tc,
            pre: None,
            lparams: d.lparams.clone(),
            levels,
            nparams: d.nparams as usize,
            is_unsafe: d.is_unsafe,
            types: d.types.clone(),
            nindices: Vec::new(),
            result_level: LevelId::ZERO,
            is_not_zero: false,
            params: Vec::new(),
            ind_consts: Vec::new(),
            ind_names: d.types.iter().map(|t| t.name).collect(),
            occs: IndOccurrences::default(),
            elim_level: LevelId::ZERO,
            elim_param: naming.elim_param,
            k_target: false,
            nnested,
            rec_infos: Vec::new(),
            rec_names: Vec::new(),
            out: Vec::new(),
            fields: IdMap::default(),
            teles: IdMap::default(),
        }
    }

    fn param_type(&self, i: usize) -> ExprId {
        self.tc.fvar_decl(self.params[i]).unwrap().ty
    }

    /// `Tc::check` of the closed type `e` of the block (with its first `k`
    /// declarations visible), unless `pre` passes it.
    fn check_closed(&mut self, e: ExprId, k: u32) -> R<()> {
        if !self.is_unsafe
            && !self.tc.st.is_local_expr(e)
            && let Some(pre) = self.pre.as_mut()
            && pre(e, &self.lparams, k)
        {
            return Ok(());
        }
        let lps = self.lparams.clone();
        self.tc.check(e, &lps)?;
        Ok(())
    }

    fn declare(&mut self, d: Decl) -> R<()> {
        if self.tc.pending.contains_key(&d.name) {
            return err(format!(
                "'{}' has already been declared",
                self.tc.show(d.name)
            ));
        }
        self.tc.pending.insert(d.name, d);
        self.out.push(d);
        Ok(())
    }

    fn check_inductive_types(&mut self) -> R<()> {
        let mut first = true;
        for idx in 0..self.types.len() {
            let name = self.types[idx].name;
            let mut ty = self.types[idx].ty;
            self.check_closed(ty, 0)?;
            self.nindices.push(0);
            let mut i = 0;
            ty = self.tc.whnf(ty)?;
            while let ExprNode::Pi(_, _, dom, body) = self.tc.st.node(ty) {
                if i < self.nparams {
                    if first {
                        let (p, b) = self.tc.local_for(ty);
                        self.params.push(p);
                        ty = b;
                    } else {
                        let pt = self.param_type(i);
                        if !self.tc.is_def_eq(dom, pt)? {
                            return err("parameters of all inductive datatypes must match");
                        }
                        ty = self.tc.st.instantiate1(body, self.params[i]);
                    }
                    i += 1;
                } else {
                    let (_, b) = self.tc.local_for(ty);
                    ty = b;
                    *self.nindices.last_mut().unwrap() += 1;
                }
                ty = self.tc.whnf(ty)?;
            }
            if i != self.nparams {
                return err("number of parameters mismatch in inductive datatype declaration");
            }
            let s = self.tc.ensure_sort(ty)?;
            let l = self.tc.sort_level(s).unwrap();
            if first {
                self.result_level = l;
                self.is_not_zero = univ::is_not_zero(&self.tc.st, l);
            } else if !univ::equiv(&mut self.tc.st, l, self.result_level) {
                return err("mutually inductive types must live in the same universe");
            }
            let c = self.tc.st.cnst(name, self.levels);
            self.ind_consts.push(c);
            first = false;
        }
        Ok(())
    }

    fn is_ind_name(&self, n: NameId) -> bool {
        self.ind_names.contains(&n)
    }

    fn has_ind_occ(&mut self, e: ExprId) -> bool {
        self.occs.contains(self.tc, e, &self.ind_names)
    }

    fn recursion_flags(&mut self) -> (bool, bool) {
        let mut recursive = false;
        for t in &self.types {
            for &(_, mut ct) in &t.ctors {
                // Opening the telescope only replaces bound variables with
                // free variables. Its shapes and constant occurrences are
                // already visible in the closed syntax.
                while let ExprNode::Pi(_, _, dom, body) = self.tc.st.node(ct) {
                    let is_pi = matches!(self.tc.st.node(dom), ExprNode::Pi(..));
                    if (is_pi || !recursive) && self.occs.contains(self.tc, dom, &self.ind_names) {
                        if is_pi {
                            return (true, true);
                        }
                        recursive = true;
                    }
                    ct = body;
                }
            }
        }
        (recursive, false)
    }

    fn all_names(&mut self) -> crate::env::NameList {
        let names = self.ind_names.clone();
        self.tc.st.push_names(&names)
    }

    fn declare_inductive_types(&mut self) -> R<()> {
        let (rec, reflexive) = self.recursion_flags();
        let all = self.all_names();
        let lps = self.tc.st.push_names(&self.lparams.clone());
        for idx in 0..self.types.len() {
            let t = &self.types[idx];
            let cnames: Vec<NameId> = t.ctors.iter().map(|c| c.0).collect();
            let (name, ty) = (t.name, t.ty);
            let ctors = self.tc.st.push_names(&cnames);
            self.declare(Decl {
                name,
                level_params: lps,
                ty,
                kind: DeclKind::Inductive {
                    num_params: self.nparams as u32,
                    num_indices: self.nindices[idx],
                    all,
                    ctors,
                    num_nested: self.nnested,
                    is_rec: rec,
                    is_reflexive: reflexive,
                    is_unsafe: self.is_unsafe,
                },
            })?;
        }
        Ok(())
    }

    fn is_valid_ind_app_at(&mut self, t: ExprId, i: usize) -> bool {
        let mut args = Vec::new();
        let h = self.tc.st.spine(t, &mut args);
        if h != self.ind_consts[i] || args.len() != self.nparams + self.nindices[i] as usize {
            return false;
        }
        if args[..self.nparams] != self.params[..] {
            return false;
        }
        args[self.nparams..].iter().all(|&a| !self.has_ind_occ(a))
    }

    fn is_valid_ind_app(&mut self, t: ExprId) -> Option<usize> {
        (0..self.types.len()).find(|&i| self.is_valid_ind_app_at(t, i))
    }

    fn is_rec_argument(&mut self, t: ExprId) -> R<Option<usize>> {
        let mut t = self.tc.whnf(t)?;
        while let ExprNode::Pi(..) = self.tc.st.node(t) {
            let (_, b) = self.tc.local_for(t);
            t = self.tc.whnf(b)?;
        }
        Ok(self.is_valid_ind_app(t))
    }

    fn check_positivity(&mut self, t: ExprId, cname: NameId, arg: usize) -> R<()> {
        let t = self.tc.whnf(t)?;
        if !self.has_ind_occ(t) {
            Ok(())
        } else if let ExprNode::Pi(_, _, d, _) = self.tc.st.node(t) {
            if self.has_ind_occ(d) {
                return err(format!(
                    "arg #{} of '{}' has a non positive occurrence of the datatypes being declared",
                    arg + 1,
                    self.tc.show(cname)
                ));
            }
            let (_, b) = self.tc.local_for(t);
            self.check_positivity(b, cname, arg)
        } else if self.is_valid_ind_app(t).is_some() {
            Ok(())
        } else {
            err(format!(
                "arg #{} of '{}' contains a non valid occurrence of the datatypes being declared",
                arg + 1,
                self.tc.show(cname)
            ))
        }
    }

    fn check_constructors(&mut self) -> R<()> {
        for idx in 0..self.types.len() {
            let mut found = Vec::new();
            for ci in 0..self.types[idx].ctors.len() {
                let (n, mut t) = self.types[idx].ctors[ci];
                if found.contains(&n) {
                    return err(format!("duplicate constructor name '{}'", self.tc.show(n)));
                }
                found.push(n);
                let k = self.types.len() as u32;
                self.check_closed(t, k)?;
                let mut locals = Vec::new();
                while let ExprNode::Pi(bi, name, dom, body) = self.tc.st.node(t) {
                    let i = locals.len();
                    let dom = self.tc.st.instantiate_rev(dom, &locals);
                    let local = if i < self.nparams {
                        let pt = self.param_type(i);
                        if !self.tc.is_def_eq(dom, pt)? {
                            return err(format!(
                                "arg #{} of '{}' does not match inductive datatypes parameters",
                                i + 1,
                                self.tc.show(n)
                            ));
                        }
                        self.params[i]
                    } else {
                        let s = self.tc.ensure_type(dom)?;
                        if !(univ::geq(&mut self.tc.st, self.result_level, s)
                            || univ::normalizes_to_zero(&self.tc.st, self.result_level))
                        {
                            return err(format!(
                                "universe level of type_of(arg #{}) of '{}' is too big for the corresponding inductive datatype",
                                i + 1,
                                self.tc.show(n)
                            ));
                        }
                        if !self.is_unsafe {
                            self.check_positivity(dom, n, i)?;
                        }
                        self.tc.local_with_annotations(name, dom, bi)
                    };
                    locals.push(local);
                    t = body;
                }
                let result = self.tc.st.instantiate_rev(t, &locals);
                if !self.is_valid_ind_app_at(result, idx) {
                    return err(format!("invalid return type for '{}'", self.tc.show(n)));
                }
            }
        }
        Ok(())
    }

    fn declare_constructors(&mut self) -> R<()> {
        let lps = self.tc.st.push_names(&self.lparams.clone());
        for idx in 0..self.types.len() {
            for ci in 0..self.types[idx].ctors.len() {
                let (n, t) = self.types[idx].ctors[ci];
                let mut arity = 0;
                let mut it = t;
                while let ExprNode::Pi(_, _, _, b) = self.tc.st.node(it) {
                    it = b;
                    arity += 1;
                }
                if arity < self.nparams {
                    return err(format!("invalid return type for '{}'", self.tc.show(n)));
                }
                let induct = self.types[idx].name;
                self.declare(Decl {
                    name: n,
                    level_params: lps,
                    ty: t,
                    kind: DeclKind::Constructor {
                        induct,
                        cidx: ci as u32,
                        num_params: self.nparams as u32,
                        num_fields: (arity - self.nparams) as u32,
                        is_unsafe: self.is_unsafe,
                    },
                })?;
            }
        }
        Ok(())
    }

    fn elim_only_at_universe_zero(&mut self) -> R<bool> {
        if self.is_not_zero {
            return Ok(false);
        }
        if self.types.len() > 1 {
            return Ok(true);
        }
        let n = self.types[0].ctors.len();
        if n > 1 {
            return Ok(true);
        }
        if n == 0 {
            return Ok(false);
        }
        let mut t = self.types[0].ctors[0].1;
        let mut i = 0;
        let mut to_check = Vec::new();
        while let ExprNode::Pi(_, _, dom, _) = self.tc.st.node(t) {
            let (fv, b) = self.tc.local_for(t);
            if i >= self.nparams {
                let s = self.tc.ensure_type(dom)?;
                if !univ::normalizes_to_zero(&self.tc.st, s) {
                    to_check.push(fv);
                }
            }
            t = b;
            i += 1;
        }
        let mut args = Vec::new();
        self.tc.st.spine(t, &mut args);
        Ok(to_check.iter().any(|a| !args.contains(a)))
    }

    fn init_elim_level(&mut self) -> R<()> {
        if self.elim_only_at_universe_zero()? {
            self.elim_level = LevelId::ZERO;
            self.elim_param = None;
        } else {
            // Lean picks a fresh `u`; the export tells us which name it
            // used. Any name not among the type's parameters means the same.
            let p = match self.elim_param {
                Some(p) if !self.lparams.contains(&p) => p,
                _ => {
                    return err(
                        "the recursor's universe parameters do not match the derived ones (large elimination)",
                    );
                }
            };
            self.elim_level = self.tc.st.param(p);
            self.elim_param = Some(p);
        }
        Ok(())
    }

    fn init_k_target(&mut self) {
        self.k_target = self.types.len() == 1
            && univ::normalizes_to_zero(&self.tc.st, self.result_level)
            && self.types[0].ctors.len() == 1;
        if !self.k_target {
            return;
        }
        let mut it = self.types[0].ctors[0].1;
        let mut i = 0;
        while let ExprNode::Pi(_, _, _, b) = self.tc.st.node(it) {
            if i < self.nparams {
                it = b;
            } else {
                self.k_target = false;
                break;
            }
            i += 1;
        }
    }

    fn get_i_indices(&mut self, t: ExprId) -> R<(usize, Vec<ExprId>)> {
        let Some(r) = self.is_valid_ind_app(t) else {
            return err("ill-formed inductive declaration: unexpected recursive occurrence");
        };
        let mut args = Vec::new();
        self.tc.st.spine(t, &mut args);
        Ok((r, args[self.nparams..].to_vec()))
    }

    /// Fields and recursive fields of a constructor, as locals: with
    /// `want_rec`, made once per constructor type (`FIELDS_ONCE`), as the
    /// terms they go into bind them.
    fn ctor_fields(&mut self, t: ExprId, want_rec: bool) -> R<(Vec<ExprId>, Vec<ExprId>, ExprId)> {
        if FIELDS_ONCE && want_rec {
            if let Some(r) = self.fields.get(&t) {
                return Ok(r.clone());
            }
            let r = self.ctor_fields_new(t, true)?;
            self.fields.insert(t, r.clone());
            return Ok(r);
        }
        self.ctor_fields_new(t, want_rec)
    }

    fn ctor_fields_new(
        &mut self,
        mut t: ExprId,
        want_rec: bool,
    ) -> R<(Vec<ExprId>, Vec<ExprId>, ExprId)> {
        let mut locals = Vec::new();
        let mut u = Vec::new();
        while let ExprNode::Pi(bi, name, dom, body) = self.tc.st.node(t) {
            let i = locals.len();
            let local = if i < self.nparams {
                self.params[i]
            } else {
                let dom = self.tc.st.instantiate_rev(dom, &locals);
                let local = self.tc.local_with_annotations(name, dom, bi);
                if want_rec && self.is_rec_argument(dom)?.is_some() {
                    u.push(local);
                }
                local
            };
            locals.push(local);
            t = body;
        }
        let result = self.tc.st.instantiate_rev(t, &locals);
        locals.drain(..self.nparams);
        Ok((locals, u, result))
    }

    /// The telescope of a recursive field's type: its arguments and result.
    fn rec_field_telescope(&mut self, u_i: ExprId) -> R<(Vec<ExprId>, ExprId)> {
        if FIELDS_ONCE {
            if let Some(r) = self.teles.get(&u_i) {
                return Ok(r.clone());
            }
            let r = self.rec_field_telescope_new(u_i)?;
            self.teles.insert(u_i, r.clone());
            return Ok(r);
        }
        self.rec_field_telescope_new(u_i)
    }

    fn rec_field_telescope_new(&mut self, u_i: ExprId) -> R<(Vec<ExprId>, ExprId)> {
        let ty = self.tc.infer(u_i)?;
        let mut t = self.tc.whnf(ty)?;
        let mut xs = Vec::new();
        while let ExprNode::Pi(..) = self.tc.st.node(t) {
            let (x, b) = self.tc.local_for(t);
            xs.push(x);
            t = self.tc.whnf(b)?;
        }
        Ok((xs, t))
    }

    fn mk_rec_infos(&mut self) -> R<()> {
        for d_idx in 0..self.types.len() {
            let mut t = self.types[d_idx].ty;
            let mut i = 0;
            let mut indices = Vec::new();
            t = self.tc.whnf(t)?;
            while let ExprNode::Pi(_, _, _, body) = self.tc.st.node(t) {
                if i < self.nparams {
                    t = self.tc.st.instantiate1(body, self.params[i]);
                } else {
                    let (x, b) = self.tc.local_for(t);
                    indices.push(x);
                    t = b;
                }
                i += 1;
                t = self.tc.whnf(t)?;
            }
            let ic = self.ind_consts[d_idx];
            let maj_ty = self.tc.st.apps(ic, &self.params.clone());
            let maj_ty = self.tc.st.apps(maj_ty, &indices);
            let major = self.tc.local_named(NameId::ANON, maj_ty);
            let sort = self.tc.st.sort(self.elim_level);
            let mut tele = indices.clone();
            tele.push(major);
            let c_ty = self.tc.mk_pi(&tele, sort);
            let c = self.tc.local_named(NameId::ANON, c_ty);
            self.rec_infos.push(RecInfo {
                c,
                minors: Vec::new(),
                indices,
                major,
            });
        }
        for d_idx in 0..self.types.len() {
            for ci in 0..self.types[d_idx].ctors.len() {
                let (cname, ct) = self.types[d_idx].ctors[ci];
                let (b_u, u, t) = self.ctor_fields(ct, true)?;
                let (it_idx, it_indices) = self.get_i_indices(t)?;
                let c = self.rec_infos[it_idx].c;
                let mut c_app = self.tc.st.apps(c, &it_indices);
                let ctor = self.tc.st.cnst(cname, self.levels);
                let intro = self.tc.st.apps(ctor, &self.params.clone());
                let intro = self.tc.st.apps(intro, &b_u);
                c_app = self.tc.st.app(c_app, intro);
                let mut v = Vec::new();
                for &u_i in &u {
                    let (xs, ut) = self.rec_field_telescope(u_i)?;
                    let (it_idx, it_indices) = self.get_i_indices(ut)?;
                    let c = self.rec_infos[it_idx].c;
                    let ca = self.tc.st.apps(c, &it_indices);
                    let ua = self.tc.st.apps(u_i, &xs);
                    let ca = self.tc.st.app(ca, ua);
                    let v_ty = self.tc.mk_pi(&xs, ca);
                    let name = self.tc.fvar_decl(u_i).unwrap().name;
                    let vi = self.tc.local_named(name, v_ty);
                    v.push(vi);
                }
                let mut tele = b_u.clone();
                tele.extend_from_slice(&v);
                let minor_ty = self.tc.mk_pi(&tele, c_app);
                let minor = self.tc.local_named(cname, minor_ty);
                self.rec_infos[d_idx].minors.push(minor);
            }
        }
        Ok(())
    }

    fn rec_levels(&mut self) -> LevelList {
        match self.elim_param {
            Some(_) => {
                let mut v = vec![self.elim_level];
                v.extend_from_slice(self.tc.st.list(self.levels));
                self.tc.st.mk_list(&v)
            }
            None => self.levels,
        }
    }

    fn rec_lparams(&self) -> Vec<NameId> {
        match self.elim_param {
            Some(p) => {
                let mut v = vec![p];
                v.extend_from_slice(&self.lparams);
                v
            }
            None => self.lparams.clone(),
        }
    }

    fn mk_rec_rules(
        &mut self,
        d_idx: usize,
        tele: &mut RecTelescope,
        minors: &[ExprId],
        minor_idx: &mut usize,
    ) -> R<Vec<RecRule>> {
        let lvls = self.rec_levels();
        let mut rules = Vec::new();
        for ci in 0..self.types[d_idx].ctors.len() {
            let (cname, ct) = self.types[d_idx].ctors[ci];
            let (b_u, u, _) = self.ctor_fields(ct, true)?;
            let mut v = Vec::new();
            for &u_i in &u {
                let (xs, ut) = self.rec_field_telescope(u_i)?;
                let (it_idx, it_indices) = self.get_i_indices(ut)?;
                let rn = self.rec_names[it_idx];
                let mut ra = self.tc.st.cnst(rn, lvls);
                ra = self.tc.st.apps(ra, &tele.locals);
                ra = self.tc.st.apps(ra, &it_indices);
                let ua = self.tc.st.apps(u_i, &xs);
                ra = self.tc.st.app(ra, ua);
                v.push(self.tc.mk_lambda(&xs, ra));
            }
            let mut e = self.tc.st.apps(minors[*minor_idx], &b_u);
            e = self.tc.st.apps(e, &v);
            let rhs = tele.bind(self.tc, &b_u, e, true);
            rules.push(RecRule {
                ctor: cname,
                nfields: b_u.len() as u32,
                rhs,
            });
            *minor_idx += 1;
        }
        Ok(rules)
    }

    fn cs_and_minors(&self) -> (Vec<ExprId>, Vec<ExprId>) {
        let cs = self.rec_infos.iter().map(|r| r.c).collect();
        let ms = self
            .rec_infos
            .iter()
            .flat_map(|r| r.minors.iter().copied())
            .collect();
        (cs, ms)
    }

    fn declare_recursors(&mut self) -> R<()> {
        let (cs, minors) = self.cs_and_minors();
        let all = self.all_names();
        let rlps = self.rec_lparams();
        let rlps = self.tc.st.push_names(&rlps);
        let mut locals = self.params.clone();
        locals.extend_from_slice(&cs);
        locals.extend_from_slice(&minors);
        let mut tele = RecTelescope::new(self.tc, locals);
        let mut minor_idx = 0;
        for d_idx in 0..self.types.len() {
            let info = &self.rec_infos[d_idx];
            let (c, mut suffix, major) = (info.c, info.indices.clone(), info.major);
            let c_app = self.tc.st.apps(c, &suffix);
            let c_app = self.tc.st.app(c_app, major);
            suffix.push(major);
            let ty = tele.bind(self.tc, &suffix, c_app, false);
            let rules = self.mk_rec_rules(d_idx, &mut tele, &minors, &mut minor_idx)?;
            let rules = self.tc.st.push_rules(&rules);
            let name = self.rec_names[d_idx];
            self.declare(Decl {
                name,
                level_params: rlps,
                ty,
                kind: DeclKind::Recursor {
                    all,
                    num_params: self.nparams as u32,
                    num_indices: self.nindices[d_idx],
                    num_motives: cs.len() as u32,
                    num_minors: minors.len() as u32,
                    rules,
                    k: self.k_target,
                    is_unsafe: self.is_unsafe,
                },
            })?;
        }
        Ok(())
    }

    fn check_recursors(&mut self) -> R<()> {
        let (cs, minors) = self.cs_and_minors();
        let rlps = self.rec_lparams();
        let lvls = self.rec_levels();
        for d_idx in 0..self.types.len() {
            let rn = self.rec_names[d_idx];
            let rd = self.tc.get(rn)?;
            self.tc.check(rd.ty, &rlps)?;
            let mut pre = self.tc.st.cnst(rn, lvls);
            pre = self.tc.st.apps(pre, &self.params.clone());
            pre = self.tc.st.apps(pre, &cs);
            pre = self.tc.st.apps(pre, &minors);
            for ci in 0..self.types[d_idx].ctors.len() {
                let (cname, ct) = self.types[d_idx].ctors[ci];
                let (b_u, _, t) = self.ctor_fields(ct, false)?;
                let (_, it_indices) = self.get_i_indices(t)?;
                let ctor = self.tc.st.cnst(cname, self.levels);
                let intro = self.tc.st.apps(ctor, &self.params.clone());
                let intro = self.tc.st.apps(intro, &b_u);
                let lhs = self.tc.st.apps(pre, &it_indices);
                let lhs = self.tc.st.app(lhs, intro);
                let expected = self.tc.infer(lhs)?;
                let reduct = self.tc.whnf(lhs)?;
                let actual = self.tc.infer(reduct)?;
                if !self.tc.is_def_eq(actual, expected)? {
                    return err(format!(
                        "generated recursor computation rule for '{}' is not type-preserving",
                        self.tc.show(cname)
                    ));
                }
            }
        }
        Ok(())
    }

    fn run(mut self) -> R<Vec<Decl>> {
        let saved_mode = self.tc.mode;
        self.tc.mode = if self.is_unsafe {
            Mode::Unsafe
        } else {
            Mode::Safe
        };
        let r = self.run_core();
        self.tc.mode = saved_mode;
        r?;
        Ok(self.out)
    }

    fn run_core(&mut self) -> R<()> {
        for i in 0..self.types.len() {
            let n = self.types[i].name;
            let rn = self.tc.rec_name_of(n)?;
            self.rec_names.push(rn);
        }
        self.check_inductive_types()?;
        self.declare_inductive_types()?;
        self.check_constructors()?;
        self.declare_constructors()?;
        self.init_elim_level()?;
        self.init_k_target();
        self.mk_rec_infos()?;
        self.declare_recursors()?;
        if CHECK_RECURSORS {
            self.check_recursors()?;
        }
        let _ = self.is_ind_name(NameId::ANON);
        Ok(())
    }
}

/// Lean's `elim_nested_inductive_fn` and `elim_nested_inductive_result`.
struct ElimNested {
    params: Vec<ExprId>,
    /// `(I Ds, auxiliary type name)`, `Ds` over `params`.
    aux: Vec<(ExprId, NameId)>,
    decl: IndDecl,
}

impl ElimNested {
    fn get_params(tc: &mut Tc<'_>, mut ty: ExprId, n: u32, out: &mut Vec<ExprId>) -> R<ExprId> {
        for _ in 0..n {
            let ExprNode::Pi(bi, nm, d, b) = tc.st.node(ty) else {
                return err(
                    "invalid inductive datatype declaration, incorrect number of parameters",
                );
            };
            let fv = tc.push_local(nm, d, None, bi);
            out.push(fv);
            ty = tc.st.instantiate1(b, fv);
        }
        Ok(ty)
    }

    fn fresh_aux_name(tc: &mut Tc<'_>, next: &mut u64) -> NameId {
        let root = tc.aux_root();
        loop {
            let n = tc.st.mk_name(NameNode::Num(root, *next));
            *next += 1;
            if !tc.st.env.by_name.contains_key(&n) && !tc.pending.contains_key(&n) {
                return n;
            }
        }
    }

    fn run(
        tc: &mut Tc<'_>,
        d: &IndDecl,
        names: &[NameId],
        occs: &mut IndOccurrences,
    ) -> R<ElimNested> {
        if NESTED_SCAN && !Self::may_nest(tc, d, names, occs) {
            // Nothing to replace: the types as they are (rebuilt, they
            // would be the same terms).
            return Ok(ElimNested {
                params: Vec::new(),
                aux: Vec::new(),
                decl: d.clone(),
            });
        }
        let mut params = Vec::new();
        Self::get_params(tc, d.types[0].ty, d.nparams, &mut params)?;
        let lvls = tc.param_levels(&d.lparams);
        let mut st = ElimNested {
            params,
            aux: Vec::new(),
            decl: d.clone(),
        };
        let mut next = 1u64;
        let mut q = 0;
        while q < st.decl.types.len() {
            let mut new_ctors = Vec::new();
            for ci in 0..st.decl.types[q].ctors.len() {
                let (cn, ct) = st.decl.types[q].ctors[ci];
                let mut as_ = Vec::new();
                let body = Self::get_params(tc, ct, d.nparams, &mut as_)?;
                let mut memo = IdMap::default();
                let new_body = tc.replace(
                    body,
                    0,
                    &mut |tc, e, _| st.replace_if_nested(tc, &as_, e, lvls, &mut next),
                    &mut memo,
                )?;
                let nt = tc.mk_pi(&as_, new_body);
                new_ctors.push((cn, nt));
            }
            st.decl.types[q].ctors = new_ctors;
            q += 1;
        }
        Ok(st)
    }

    /// Whether `run` may find a nested occurrence (`replace_if_nested`) or
    /// fail: a type or a constructor with fewer than the parameters, or an
    /// application of an inductive type (of the environment) to
    /// parameters that mention a type of the block.
    fn may_nest(tc: &Tc<'_>, d: &IndDecl, names: &[NameId], occs: &mut IndOccurrences) -> bool {
        let np = d.nparams as usize;
        let pis = |mut e: ExprId| {
            let mut k = 0;
            while k < np
                && let ExprNode::Pi(_, _, _, b) = tc.st.node(e)
            {
                e = b;
                k += 1;
            }
            k
        };
        if pis(d.types[0].ty) < np {
            return true;
        }
        let mut seen = IdSet::<ExprId>::with_capacity_and_hasher(SEEN, Default::default());
        let mut stack = Vec::new();
        let mut args = Vec::new();
        for t in &d.types {
            for &(_, ct) in &t.ctors {
                if pis(ct) < np {
                    return true;
                }
                stack.push(ct);
            }
        }
        while let Some(e) = stack.pop() {
            if !occs.contains(tc, e, names) || !seen.insert(e) {
                continue;
            }
            match tc.st.node(e) {
                ExprNode::App(..) => {
                    let h = tc.st.spine(e, &mut args);
                    if let ExprNode::Const(n, _) = tc.st.node(h)
                        && let Some(DeclKind::Inductive { num_params, .. }) =
                            tc.find(n).map(|c| c.kind)
                        && num_params != 0
                        && num_params as usize <= args.len()
                        && args[..num_params as usize]
                            .iter()
                            .any(|&a| occs.contains(tc, a, names))
                    {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                    stack.push(h);
                }
                ExprNode::Lam(_, _, t, b) | ExprNode::Pi(_, _, t, b) => stack.extend([t, b]),
                ExprNode::Let(h, b) => {
                    let lb = tc.st.let_binder(h);
                    stack.extend([lb.ty, lb.value, b]);
                }
                ExprNode::Proj(_, _, x) => stack.push(x),
                _ => {}
            }
        }
        false
    }

    /// `instantiate_rev(abstract(e, As), params)`.
    fn replace_params(&self, tc: &mut Tc<'_>, e: ExprId, as_: &[ExprId]) -> ExprId {
        let a = tc.st.abstract_fvars(e, as_);
        tc.st.instantiate_rev(a, &self.params)
    }

    fn replace_if_nested(
        &mut self,
        tc: &mut Tc<'_>,
        as_: &[ExprId],
        e: ExprId,
        lvls: LevelList,
        next: &mut u64,
    ) -> R<Option<ExprId>> {
        if !matches!(tc.st.node(e), ExprNode::App(..)) {
            return Ok(None);
        }
        let mut args = Vec::new();
        let f = tc.st.spine(e, &mut args);
        let ExprNode::Const(i_name, i_lvls) = tc.st.node(f) else {
            return Ok(None);
        };
        let Some(i_decl) = tc.find(i_name) else {
            return Ok(None);
        };
        let DeclKind::Inductive {
            num_params: inp,
            all,
            ..
        } = i_decl.kind
        else {
            return Ok(None);
        };
        let inp = inp as usize;
        if inp > args.len() {
            return Ok(None);
        }
        let new_names: Vec<NameId> = self.decl.types.iter().map(|t| t.name).collect();
        let mut is_nested = false;
        let mut loose = false;
        for &a in &args[..inp] {
            if tc.st.has_loose_bvars(a) {
                loose = true;
            }
            if tc.find_const(a, &|n| new_names.contains(&n)) {
                is_nested = true;
            }
        }
        if !is_nested {
            return Ok(None);
        }
        if loose {
            return err(format!(
                "invalid nested inductive datatype '{}', nested inductive datatypes parameters cannot contain local variables.",
                tc.show(i_name)
            ));
        }
        let ias = tc.st.apps(f, &args[..inp]);
        let iparams = self.replace_params(tc, ias, as_);
        if let Some(&(_, aux)) = self.aux.iter().find(|p| p.0 == iparams) {
            let c = tc.st.cnst(aux, lvls);
            let c = tc.st.apps(c, as_);
            return Ok(Some(tc.st.apps(c, &args[inp..])));
        }
        let mut result = None;
        let all: Vec<NameId> = tc.st.name_list(all).to_vec();
        let i_lvls_v: Vec<LevelId> = tc.st.list(i_lvls).to_vec();
        for j_name in all {
            let j = tc.get(j_name)?;
            let DeclKind::Inductive { ctors: jctors, .. } = j.kind else {
                return err("invalid nested inductive datatype, ill-formed declaration");
            };
            let jc = tc.st.cnst(j_name, i_lvls);
            let jas = tc.st.apps(jc, &args[..inp]);
            let aux_name = Self::fresh_aux_name(tc, next);
            let jlps: Vec<NameId> = tc.st.lparams(&j).to_vec();
            let mut aux_ty = tc.st.instantiate_lparams(j.ty, &jlps, &i_lvls_v);
            aux_ty = Self::instantiate_pi_params(tc, aux_ty, &args[..inp])?;
            aux_ty = tc.mk_pi(as_, aux_ty);
            let key = self.replace_params(tc, jas, as_);
            self.aux.push((key, aux_name));
            if j_name == i_name {
                let c = tc.st.cnst(aux_name, lvls);
                let c = tc.st.apps(c, as_);
                result = Some(tc.st.apps(c, &args[inp..]));
            }
            let mut new_ctors = Vec::new();
            for &jc_name in &tc.st.name_list(jctors).to_vec() {
                let jcd = tc.get(jc_name)?;
                let Some(aux_c) = tc.st.replace_prefix(jc_name, j_name, aux_name) else {
                    return err("invalid nested inductive datatype, ill-formed declaration");
                };
                let jclps: Vec<NameId> = tc.st.lparams(&jcd).to_vec();
                let mut ct = tc.st.instantiate_lparams(jcd.ty, &jclps, &i_lvls_v);
                ct = Self::instantiate_pi_params(tc, ct, &args[..inp])?;
                ct = tc.mk_pi(as_, ct);
                new_ctors.push((aux_c, ct));
            }
            self.decl.types.push(IndType {
                name: aux_name,
                ty: aux_ty,
                ctors: new_ctors,
            });
        }
        match result {
            Some(r) => Ok(Some(r)),
            None => err("invalid nested inductive datatype, ill-formed declaration"),
        }
    }

    fn instantiate_pi_params(tc: &mut Tc<'_>, mut e: ExprId, ps: &[ExprId]) -> R<ExprId> {
        for _ in 0..ps.len() {
            let ExprNode::Pi(_, _, _, b) = tc.st.node(e) else {
                return err("invalid nested inductive datatype, ill-formed declaration");
            };
            e = b;
        }
        Ok(tc.st.instantiate_rev(e, ps))
    }

    fn aux_nested(&self, n: NameId) -> Option<ExprId> {
        self.aux.iter().find(|p| p.1 == n).map(|p| p.0)
    }

    /// If `c` is a constructor of an auxiliary type: the nested occurrence
    /// and the auxiliary type's name.
    fn nested_if_aux_ctor(
        &self,
        aux_decls: &IdMap<NameId, Decl>,
        c: NameId,
    ) -> Option<(ExprId, NameId)> {
        let d = aux_decls.get(&c)?;
        let DeclKind::Constructor { induct, .. } = d.kind else {
            return None;
        };
        Some((self.aux_nested(induct)?, induct))
    }

    fn restore(
        &self,
        tc: &mut Tc<'_>,
        mut e: ExprId,
        aux_decls: &IdMap<NameId, Decl>,
        rec_map: &[(NameId, NameId)],
    ) -> R<ExprId> {
        let pi = matches!(tc.st.node(e), ExprNode::Pi(..));
        let mut as_ = Vec::new();
        for _ in 0..self.params.len() {
            let (ExprNode::Pi(bi, n, d, b) | ExprNode::Lam(bi, n, d, b)) = tc.st.node(e) else {
                return err(
                    "failed to restore nested inductive types, fewer binders than parameters",
                );
            };
            let fv = tc.push_local(n, d, None, bi);
            as_.push(fv);
            e = tc.st.instantiate1(b, fv);
        }
        let np = self.params.len();
        let mut memo = IdMap::default();
        let r = tc.replace(
            e,
            0,
            &mut |tc, t, _| {
                if let ExprNode::Const(n, ls) = tc.st.node(t)
                    && let Some(&(_, new)) = rec_map.iter().find(|p| p.0 == n)
                {
                    return Ok(Some(tc.st.cnst(new, ls)));
                }
                let mut args = Vec::new();
                let f = tc.st.spine(t, &mut args);
                let ExprNode::Const(fname, _) = tc.st.node(f) else {
                    return Ok(None);
                };
                if let Some(nested) = self.aux_nested(fname) {
                    if args.len() < np {
                        return err("failed to restore nested inductive types, auxiliary type is not applied to all parameters");
                    }
                    let a = tc.st.abstract_fvars(nested, &self.params);
                    let nt = tc.st.instantiate_rev(a, &as_);
                    return Ok(Some(tc.st.apps(nt, &args[np..])));
                }
                if let Some((nested, aux_i)) = self.nested_if_aux_ctor(aux_decls, fname) {
                    if args.len() < np {
                        return err("failed to restore nested inductive types, auxiliary constructor is not applied to all parameters");
                    }
                    let a = tc.st.abstract_fvars(nested, &self.params);
                    let nn = tc.st.instantiate_rev(a, &as_);
                    let mut iargs = Vec::new();
                    let i = tc.st.spine(nn, &mut iargs);
                    let ExprNode::Const(i_name, i_lvls) = tc.st.node(i) else {
                        return err("failed to restore nested inductive types, nested occurrence is not an inductive type application");
                    };
                    let Some(new_fn) = tc.st.replace_prefix(fname, aux_i, i_name) else {
                        return err("failed to restore nested inductive types");
                    };
                    let c = tc.st.cnst(new_fn, i_lvls);
                    let c = tc.st.apps(c, &iargs);
                    return Ok(Some(tc.st.apps(c, &args[np..])));
                }
                Ok(None)
            },
            &mut memo,
        )?;
        Ok(if pi {
            tc.mk_pi(&as_, r)
        } else {
            tc.mk_lambda(&as_, r)
        })
    }

    fn restore_all(&self, tc: &mut Tc<'_>, d: &IndDecl, aux_out: &[Decl]) -> R<Vec<Decl>> {
        let ntypes = d.types.len();
        let main = d.types[0].name;
        let aux_decls: IdMap<NameId, Decl> = aux_out.iter().map(|x| (x.name, *x)).collect();
        // Auxiliary recursors become `main.rec_1`, `main.rec_2`, ...
        let mut rec_map: Vec<(NameId, NameId)> = Vec::new();
        for (k, t) in self.decl.types[ntypes..].iter().enumerate() {
            let old = tc.rec_name_of(t.name)?;
            let s = format!("rec_{}", k + 1);
            let Some(sid) = tc.st.env.names.strings.find(&s) else {
                return err(format!("missing recursor '{}.{s}'", tc.show(main)));
            };
            let new = tc.st.mk_name(NameNode::Str(main, sid));
            rec_map.push((old, new));
        }
        let all_names: Vec<NameId> = d.types.iter().map(|t| t.name).collect();
        let all = tc.st.push_names(&all_names);
        let mut out = Vec::new();
        let mut new_recs = Vec::new();
        let process_rec = |tc: &mut Tc<'_>,
                           rec: NameId,
                           out: &mut Vec<Decl>,
                           new_recs: &mut Vec<NameId>|
         -> R<()> {
            let new_name = rec_map
                .iter()
                .find(|p| p.0 == rec)
                .map(|p| p.1)
                .unwrap_or(rec);
            let Some(rd) = aux_decls.get(&rec).copied() else {
                return err("failed to restore nested inductive types: missing recursor");
            };
            let ty = self.restore(tc, rd.ty, &aux_decls, &rec_map)?;
            let DeclKind::Recursor {
                num_params,
                num_indices,
                num_motives,
                num_minors,
                rules,
                k,
                is_unsafe,
                ..
            } = rd.kind
            else {
                unreachable!()
            };
            let mut new_rules = Vec::new();
            for r in tc.st.rec_rules(rules).to_vec() {
                let rhs = self.restore(tc, r.rhs, &aux_decls, &rec_map)?;
                let mut ctor = r.ctor;
                if new_name != rec {
                    let Some((nested, aux_i)) = self.nested_if_aux_ctor(&aux_decls, r.ctor) else {
                        return err(
                            "failed to restore nested inductive types: not a constructor of an auxiliary type",
                        );
                    };
                    let Some((i_name, _)) = tc.st.head_const(nested) else {
                        return err(
                            "failed to restore nested inductive types, nested occurrence is not an inductive type application",
                        );
                    };
                    let Some(c) = tc.st.replace_prefix(r.ctor, aux_i, i_name) else {
                        return err("failed to restore nested inductive types");
                    };
                    ctor = c;
                }
                new_rules.push(RecRule {
                    ctor,
                    nfields: r.nfields,
                    rhs,
                });
            }
            let rules = tc.st.push_rules(&new_rules);
            out.push(Decl {
                name: new_name,
                level_params: rd.level_params,
                ty,
                kind: DeclKind::Recursor {
                    all,
                    num_params,
                    num_indices,
                    num_motives,
                    num_minors,
                    rules,
                    k,
                    is_unsafe,
                },
            });
            new_recs.push(new_name);
            Ok(())
        };
        let mut recs = Vec::new();
        for t in &d.types {
            let id = aux_decls[&t.name];
            let DeclKind::Inductive {
                num_params,
                num_indices,
                ctors,
                num_nested,
                is_rec,
                is_reflexive,
                is_unsafe,
                ..
            } = id.kind
            else {
                unreachable!()
            };
            out.push(Decl {
                kind: DeclKind::Inductive {
                    num_params,
                    num_indices,
                    all,
                    ctors,
                    num_nested,
                    is_rec,
                    is_reflexive,
                    is_unsafe,
                },
                ..id
            });
            for c in tc.st.name_list(ctors).to_vec() {
                let cd = aux_decls[&c];
                let ty = self.restore(tc, cd.ty, &aux_decls, &[])?;
                out.push(Decl { ty, ..cd });
            }
            let rn = tc.rec_name_of(t.name)?;
            process_rec(tc, rn, &mut recs, &mut new_recs)?;
        }
        for t in &self.decl.types[ntypes..] {
            let rn = tc.rec_name_of(t.name)?;
            process_rec(tc, rn, &mut recs, &mut new_recs)?;
        }
        out.extend(recs);
        // The new environment: only the restored declarations.
        tc.pending.clear();
        for x in &out {
            tc.pending.insert(x.name, *x);
        }
        tc.clear_caches();
        let saved = tc.mode;
        tc.mode = if d.is_unsafe {
            Mode::Unsafe
        } else {
            Mode::Safe
        };
        let r = (|| {
            for &(nested, _) in &self.aux {
                tc.check(nested, &d.lparams)?;
            }
            for x in &out {
                match x.kind {
                    DeclKind::Constructor { .. } => {
                        tc.check(x.ty, &d.lparams)?;
                    }
                    DeclKind::Recursor { rules, .. } => {
                        let lps: Vec<NameId> = tc.st.lparams(x).to_vec();
                        tc.check(x.ty, &lps)?;
                        for r in tc.st.rec_rules(rules).to_vec() {
                            tc.check(r.rhs, &lps)?;
                        }
                    }
                    _ => {}
                }
            }
            Ok::<(), KErr>(())
        })();
        tc.mode = saved;
        r?;
        Ok(out)
    }
}

/// Whether `a` and `b` are equal up to binder names and binder annotations.
pub fn alpha_eq(tc: &Tc<'_>, a: ExprId, b: ExprId) -> bool {
    let mut seen = IdSet::<(ExprId, ExprId)>::default();
    alpha_rec(tc, a, b, &mut seen)
}

fn alpha_rec(tc: &Tc<'_>, a: ExprId, b: ExprId, seen: &mut IdSet<(ExprId, ExprId)>) -> bool {
    if a == b {
        return true;
    }
    if !seen.insert((a, b)) {
        return true;
    }
    match (tc.st.node(a), tc.st.node(b)) {
        (ExprNode::App(f1, a1), ExprNode::App(f2, a2)) => {
            alpha_rec(tc, f1, f2, seen) && alpha_rec(tc, a1, a2, seen)
        }
        (ExprNode::Lam(_, _, t1, b1), ExprNode::Lam(_, _, t2, b2))
        | (ExprNode::Pi(_, _, t1, b1), ExprNode::Pi(_, _, t2, b2)) => {
            alpha_rec(tc, t1, t2, seen) && alpha_rec(tc, b1, b2, seen)
        }
        (ExprNode::Let(h1, b1), ExprNode::Let(h2, b2)) => {
            let (l1, l2) = (tc.st.let_binder(h1), tc.st.let_binder(h2));
            alpha_rec(tc, l1.ty, l2.ty, seen)
                && alpha_rec(tc, l1.value, l2.value, seen)
                && alpha_rec(tc, b1, b2, seen)
        }
        (ExprNode::Proj(s1, i1, x1), ExprNode::Proj(s2, i2, x2)) => {
            s1 == s2 && i1 == i2 && alpha_rec(tc, x1, x2, seen)
        }
        // Leaves by their contents, so that nothing here needs equal terms
        // to have one id.
        (x, y) => x == y,
    }
}

#[allow(dead_code)]
fn level_is_param(tc: &Tc<'_>, l: LevelId) -> bool {
    matches!(tc.st.level(l), LevelNode::Param(_))
}
