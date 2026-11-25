//! The shapes of definitions that reduce like a `casesOn`: recognised once
//! per constant from its value, and used by the closed-term evaluator
//! (`eval/`) and the evaluating checker (`nbe/`) to go from the major
//! premise to the chosen minor premise without building the others.
//!
//! The detectors look at terms only. What a head constant is (a recursor,
//! a constructor, a definition already of one of these shapes) comes from
//! the caller (`Heads`), which keeps its own cache.

use std::rc::Rc;

use crate::expr::{ExprId, ExprNode};
use crate::name::NameId;

use super::store::Store;

/// What a head constant is, as far as the shapes are concerned.
#[derive(Clone)]
pub enum Head {
    /// A recursor.
    Rec(Rc<RecInfo>),
    /// A definition of the shape of a `casesOn`.
    Cases(Rc<CasesInfo>),
    /// A constructor, with its number of parameters.
    Ctor(u32),
    Other,
}

/// The caller's view of the environment.
pub trait Heads {
    fn st(&self) -> &Store<'_>;
    /// What the constant term `h` is.
    fn head(&mut self, h: ExprId) -> Head;
}

#[derive(Clone, Debug)]
pub struct RecInfo {
    pub major_idx: usize,
    /// `params + motives + minors`.
    pub pmm: usize,
    pub nparams: u32,
    /// One motive, and a minor premise per rule (not a mutual or nested
    /// block's recursor).
    pub single: bool,
    pub induct: NameId,
    pub k: bool,
    /// Per rule: constructor, fields, right-hand side with this constant's
    /// levels.
    pub rules: Vec<(NameId, u32, ExprId)>,
}

/// A definition `fun x₀ … xₖ₋₁ => I.rec … (fun fields ihs => x_m fields) …
/// x_major`: a `casesOn`, as Lean generates it for every inductive type
/// and as matchers use it.
#[derive(Debug)]
pub struct CasesInfo {
    pub arity: usize,
    /// The argument that is the major premise.
    pub major: usize,
    /// Per rule of the recursor: its constructor, fields, the number `e`
    /// of the minor premise's binders past the fields and inductive
    /// hypotheses (they take the first arguments past the `k`), and what
    /// the minor premise's body is.
    pub rules: Vec<(NameId, u32, u32, Minor)>,
}

#[derive(Debug)]
pub enum Minor {
    /// `x_l y₁ … y_f`: argument `l` applied to the fields.
    Arg(usize),
    /// `z_j t₁ … tₙ`: the `j`-th binder past the inductive hypotheses
    /// applied to closed terms.
    Extra(u32, Vec<ExprId>),
    /// A closed term, whatever the fields (only in `cases_compose`).
    Closed(ExprId),
    /// Argument `l` itself, whatever the fields (only in `cases_compose`).
    Var(usize),
}

/// Where a matcher's decision tree (`Tree`) takes a thunk from.
#[derive(Debug, Clone, Copy)]
pub enum Src {
    /// The definition's argument.
    Arg(usize),
    /// Field `f` of the constructor matched at level `l`.
    Field(usize, usize),
    /// The value matched at level `l` (where the term rebuilds it from its
    /// fields).
    Major(usize),
    /// A closed term.
    Closed(ExprId),
}

#[derive(Debug)]
pub enum Tree {
    /// `head args…`, then the arguments past the definition's binders.
    Leaf(Src, Box<[Src]>),
    /// The value of the source, a constructor: its rule's tree, one level
    /// down (constructor, fields, tree).
    Case(Src, Box<[(NameId, u32, Tree)]>),
}

/// A definition `fun x₀ … xₖ₋₁ => t` whose body is nested `casesOn`s with
/// a leaf at the end of each branch (see `tree_shape`).
#[derive(Debug)]
pub struct TreeInfo {
    pub arity: usize,
    pub tree: Tree,
}

/// `Some` if `v` is `fun x₀ … xₖ₋₁ => I.rec a₀ … aₙ` for a recursor
/// `I.rec` that is not `K`-like, taking exactly its arguments up to the
/// major premise, which is a variable `xⱼ`; and each minor premise is
/// `fun y₁ … yₘ => x_l y₁ … y_f`, applying a variable to the first `f`
/// binders, `f` the constructor's fields. The other arguments are not
/// looked at: the recursor's reduction does not use them on the way to
/// the minor premise.
#[inline(never)]
pub fn cases_shape<C: Heads + ?Sized>(cx: &mut C, v: ExprId) -> Option<CasesInfo> {
    let mut e = v;
    let mut k = 0usize;
    while let ExprNode::Lam(_, _, _, b) = cx.st().node(e) {
        k += 1;
        e = b;
    }
    if k == 0 {
        return None;
    }
    let mut a = Vec::new();
    let h = cx.st().spine(e, &mut a);
    if !matches!(cx.st().node(h), ExprNode::Const(..)) {
        return None;
    }
    let r = match cx.head(h) {
        Head::Rec(r) => r,
        Head::Cases(ci) => return cases_compose(cx, k, &a, &ci),
        _ => return None,
    };
    if r.k || !r.single || a.len() != r.major_idx + 1 {
        return None;
    }
    let outer = |st: &Store<'_>, x: ExprId, under: usize| -> Option<usize> {
        match st.node(x) {
            ExprNode::BVar(j) if (j as usize) >= under && (j as usize) - under < k => {
                Some(k - 1 - (j as usize - under))
            }
            _ => None,
        }
    };
    let major = outer(cx.st(), a[r.major_idx], 0)?;
    let first_minor = r.pmm.checked_sub(r.rules.len())?;
    let mut rules = Vec::with_capacity(r.rules.len());
    for (i, &(cn, nf, rhs)) in r.rules.iter().enumerate() {
        let nf = nf as usize;
        let nih = rule_ihs(cx, rhs, r.pmm + nf, nf)?;
        let mut m = a[first_minor + i];
        let mut nb = 0usize;
        while let ExprNode::Lam(_, _, _, b) = cx.st().node(m) {
            nb += 1;
            m = b;
        }
        let ne = nb.checked_sub(nf + nih)?;
        let mut ma = Vec::new();
        let mh = cx.st().spine(m, &mut ma);
        let minor = if let Some(l) = outer(cx.st(), mh, nb) {
            if ma.len() != nf {
                return None;
            }
            for (f, &x) in ma.iter().enumerate() {
                // Field `f` is binder `f`: the variable `#(nb - 1 - f)`.
                if !matches!(cx.st().node(x), ExprNode::BVar(j) if j as usize == nb - 1 - f) {
                    return None;
                }
            }
            Minor::Arg(l)
        } else {
            // `z_j t₁ … tₙ` with `z_j` an extra binder (`#(ne-1-j)`)
            // and closed `tᵢ`.
            let ExprNode::BVar(b) = cx.st().node(mh) else {
                return None;
            };
            let b = b as usize;
            if b >= ne || ma.iter().any(|&x| cx.st().has_loose_bvars(x)) {
                return None;
            }
            Minor::Extra((ne - 1 - b) as u32, ma)
        };
        rules.push((cn, nf as u32, ne as u32, minor));
    }
    Some(CasesInfo {
        arity: k,
        major,
        rules,
    })
}

/// `Some` if the body of `v = fun x₀ … xₖ₋₁ => C a₀ … aₙ` applies a
/// definition `C` of the shape of a `casesOn` (`ci`) to exactly its
/// arguments, the major premise is a variable `xⱼ`, and each minor
/// premise `C` selects is a variable `x_l` (applied to the fields), or
/// `fun y₁ … y_f => t` (`f` the fields) with `t` closed or a variable
/// `x_l`. Unfolding `v`, then `C`, then reducing gives that minor
/// premise applied to the fields, so `t` or `x_l`. `ite`, `dite` and
/// `decide` are of this shape (over `Decidable.casesOn`).
pub fn cases_compose<C: Heads + ?Sized>(
    cx: &mut C,
    k: usize,
    a: &[ExprId],
    ci: &CasesInfo,
) -> Option<CasesInfo> {
    if a.len() != ci.arity {
        return None;
    }
    let st = cx.st();
    let outer = |x: ExprId, under: usize| -> Option<usize> {
        match st.node(x) {
            ExprNode::BVar(j) if (j as usize) >= under && (j as usize) - under < k => {
                Some(k - 1 - (j as usize - under))
            }
            _ => None,
        }
    };
    let major = outer(a[ci.major], 0)?;
    let mut rules = Vec::with_capacity(ci.rules.len());
    for (cn, nf, e, m) in &ci.rules {
        let (Minor::Arg(l), 0) = (m, *e) else {
            return None;
        };
        let x = a[*l];
        let minor = if let Some(l) = outer(x, 0) {
            Minor::Arg(l)
        } else {
            let mut b = x;
            for _ in 0..*nf {
                let ExprNode::Lam(_, _, _, body) = st.node(b) else {
                    return None;
                };
                b = body;
            }
            if !st.has_loose_bvars(b) {
                Minor::Closed(b)
            } else {
                Minor::Var(outer(b, *nf as usize)?)
            }
        };
        rules.push((*cn, *nf, 0, minor));
    }
    Some(CasesInfo {
        arity: k,
        major,
        rules,
    })
}

/// `Some` if `v = fun x₀ … xₖ₋₁ => t` and `t` is an application of a
/// definition of the shape of a `casesOn` (`cases_shape`), whose minor
/// premises the reduction picks (applied to the fields, or the extra
/// arguments of a sparse `casesOn`'s `else`) are again such
/// applications or leaves: a variable, a field or a closed term applied
/// to variables, fields, closed terms or a constructor rebuilding a
/// matched value from its fields. That is what a matcher of several
/// discriminants or nested patterns compiles to. Unfolding `v` and the
/// `casesOn`s on the way to a leaf, and reducing them, gives the leaf
/// (`tree_n`); the rebuilt constructor is the matched value itself (up
/// to its parameters, which typing makes the same).
#[inline(never)]
pub fn tree_shape<C: Heads + ?Sized>(cx: &mut C, v: ExprId) -> Option<TreeInfo> {
    let mut e = v;
    let mut ctx = Vec::new();
    while let ExprNode::Lam(_, _, _, b) = cx.st().node(e) {
        ctx.push(Src::Arg(ctx.len()));
        e = b;
    }
    let arity = ctx.len();
    let mut budget = 64u32;
    let tree = tree_of(cx, e, &mut ctx, &mut Vec::new(), &mut budget)?;
    if !matches!(tree, Tree::Case(..)) {
        return None;
    }
    Some(TreeInfo { arity, tree })
}

/// The source of the term `x` in `ctx` (a source per bound variable,
/// the innermost last), at the matched `levels` (constructor, fields).
pub fn src_of<C: Heads + ?Sized>(
    cx: &mut C,
    x: ExprId,
    ctx: &[Src],
    levels: &[(NameId, usize)],
) -> Option<Src> {
    if !cx.st().has_loose_bvars(x) {
        return Some(Src::Closed(x));
    }
    if let ExprNode::BVar(i) = cx.st().node(x) {
        return ctx.len().checked_sub(1 + i as usize).map(|j| ctx[j]);
    }
    let mut a = Vec::new();
    let h = cx.st().spine(x, &mut a);
    let ExprNode::Const(n, _) = cx.st().node(h) else {
        return None;
    };
    let Head::Ctor(np) = cx.head(h) else {
        return None;
    };
    let (lv, &(_, nf)) = levels.iter().enumerate().rev().find(|(_, l)| l.0 == n)?;
    if nf == 0 || a.len() != np as usize + nf {
        return None;
    }
    for (f, &y) in a[a.len() - nf..].iter().enumerate() {
        match src_of(cx, y, ctx, levels)? {
            Src::Field(l, g) if l == lv && g == f => {}
            _ => return None,
        }
    }
    Some(Src::Major(lv))
}

fn tree_of<C: Heads + ?Sized>(
    cx: &mut C,
    t: ExprId,
    ctx: &mut Vec<Src>,
    levels: &mut Vec<(NameId, usize)>,
    budget: &mut u32,
) -> Option<Tree> {
    *budget = budget.checked_sub(1)?;
    let mut a = Vec::new();
    let h = cx.st().spine(t, &mut a);
    if let ExprNode::Const(..) = cx.st().node(h)
        && let Head::Cases(ci) = cx.head(h)
        && a.len() >= ci.arity
    {
        let major = src_of(cx, a[ci.major], ctx, levels)?;
        let mut rules = Vec::with_capacity(ci.rules.len());
        for (cn, nf, e, m) in &ci.rules {
            let (nf, e) = (*nf as usize, *e as usize);
            if a.len() < ci.arity + e {
                return None;
            }
            let tail = &a[ci.arity + e..];
            let lv = levels.len();
            levels.push((*cn, nf));
            let fields: Vec<Src> = (0..nf).map(|f| Src::Field(lv, f)).collect();
            let sub = match m {
                Minor::Arg(l) => apply_tree(cx, a[*l], &fields, tail, ctx, levels, budget),
                Minor::Extra(j, ts) => {
                    let ts: Vec<Src> = ts.iter().map(|&t| Src::Closed(t)).collect();
                    apply_tree(
                        cx,
                        a[ci.arity + *j as usize],
                        &ts,
                        tail,
                        ctx,
                        levels,
                        budget,
                    )
                }
                Minor::Closed(c) => apply_tree(cx, *c, &[], tail, ctx, levels, budget),
                Minor::Var(l) => apply_tree(cx, a[*l], &[], tail, ctx, levels, budget),
            };
            levels.pop();
            rules.push((*cn, nf as u32, sub?));
        }
        return Some(Tree::Case(major, rules.into_boxed_slice()));
    }
    let head = src_of(cx, h, ctx, levels)?;
    let mut xs = Vec::with_capacity(a.len());
    for &x in &a {
        xs.push(src_of(cx, x, ctx, levels)?);
    }
    Some(Tree::Leaf(head, xs.into_boxed_slice()))
}

/// The tree of `x xs… tail…`, `xs` sources and `tail` terms in `ctx`.
fn apply_tree<C: Heads + ?Sized>(
    cx: &mut C,
    x: ExprId,
    xs: &[Src],
    tail: &[ExprId],
    ctx: &mut Vec<Src>,
    levels: &mut Vec<(NameId, usize)>,
    budget: &mut u32,
) -> Option<Tree> {
    let mut ts = Vec::with_capacity(tail.len());
    for &t in tail {
        ts.push(src_of(cx, t, ctx, levels)?);
    }
    let n = ctx.len();
    let mut body = x;
    let mut used = 0;
    while used < xs.len()
        && let ExprNode::Lam(_, _, _, b) = cx.st().node(body)
    {
        ctx.push(xs[used]);
        used += 1;
        body = b;
    }
    let r = if used == xs.len() && ts.is_empty() {
        tree_of(cx, body, ctx, levels, budget)
    } else {
        src_of(cx, body, ctx, levels).map(|h| {
            let mut args = xs[used..].to_vec();
            args.extend(ts);
            Tree::Leaf(h, args.into_boxed_slice())
        })
    };
    ctx.truncate(n);
    r
}

/// The number of inductive hypotheses of a recursor rule `fun x₁ … xₙ
/// => m y₁ … y_f ih₁ … ihᵣ` (`n` binders, `f` fields): `r`.
pub fn rule_ihs<C: Heads + ?Sized>(cx: &mut C, rhs: ExprId, n: usize, nf: usize) -> Option<usize> {
    let mut e = rhs;
    for _ in 0..n {
        let ExprNode::Lam(_, _, _, b) = cx.st().node(e) else {
            return None;
        };
        e = b;
    }
    let mut a = Vec::new();
    cx.st().spine(e, &mut a);
    a.len().checked_sub(nf)
}
