//! Interning a module's [`Tape`] into the shared [`Env`], and putting its
//! declarations in an order the checker can use.
//!
//! A module's `constants` array is in hash-map order (`mkModuleData` in
//! `src/Lean/Environment.lean` folds the kernel's constant map), not in
//! dependency order. The checker only lets a declaration refer to those
//! before it, so the module's declarations are grouped the way `leanexport`
//! groups them (an inductive with its constructors and recursors; the four
//! quotient constants) and then sorted depth-first by the constants their
//! terms mention, the order `leanexport` writes. Modules are interned in
//! import order, so only references within the module need sorting.

use hashbrown::HashMap;

use super::Fail;
use super::decode::Tape;
use crate::env::{Block, BlockKind, Decl, DeclKind, Env, NameList, QuotKind, RecRule};
use crate::expr::{ExprId, ExprNode, LetBinder};
use crate::level::{LevelId, LevelList, LevelNode};
use crate::name::{NameId, NameNode};
use crate::reader::ErrorClass;
use crate::strings::StrId;

impl From<crate::strings::Overflow> for Fail {
    fn from(o: crate::strings::Overflow) -> Self {
        Fail::malformed(format!("capacity exceeded: {}", o.0))
    }
}

impl From<crate::expr::ExprError> for Fail {
    fn from(e: crate::expr::ExprError) -> Self {
        match e {
            crate::expr::ExprError::Overflow(o) => o.into(),
            crate::expr::ExprError::BVarTooLarge(i) => {
                Fail::malformed(format!("bvar index {i} is too large"))
            }
        }
    }
}

/// Local-to-global id maps of one tape.
struct Maps {
    names: Vec<NameId>,
    exprs: Vec<ExprId>,
}

pub static PROF: [std::sync::atomic::AtomicU64; 8] =
    [const { std::sync::atomic::AtomicU64::new(0) }; 8];
fn prof(i: usize, t: std::time::Instant) {
    PROF[i].fetch_add(
        t.elapsed().as_nanos() as u64,
        std::sync::atomic::Ordering::Relaxed,
    );
}

fn intern_tape(env: &mut Env, t: &Tape) -> Result<(Maps, Vec<Decl>), Fail> {
    let phase_start = std::time::Instant::now();
    let strs: Vec<StrId> = (0..t.strs.len() as u32)
        .map(|i| env.names.strings.intern(t.str(StrId(i))))
        .collect::<Result<_, _>>()?;
    let mut names = Vec::with_capacity(t.names.len());
    names.push(NameId::ANON);
    for n in &t.names[1..] {
        let node = match *n {
            NameNode::Str(p, s) => NameNode::Str(names[p.index()], strs[s.index()]),
            NameNode::Num(p, k) => NameNode::Num(names[p.index()], k),
            NameNode::Anon => NameNode::Anon,
        };
        names.push(env.names.intern(node)?.0);
    }
    let mut levels = Vec::with_capacity(t.levels.len());
    levels.push(LevelId::ZERO);
    for l in &t.levels[1..] {
        let m = |x: LevelId| levels[x.index()];
        let node = match *l {
            LevelNode::Zero => LevelNode::Zero,
            LevelNode::Succ(a) => LevelNode::Succ(m(a)),
            LevelNode::Max(a, b) => LevelNode::Max(m(a), m(b)),
            LevelNode::IMax(a, b) => LevelNode::IMax(m(a), m(b)),
            LevelNode::Param(n) => LevelNode::Param(names[n.index()]),
        };
        levels.push(env.levels.intern(node)?.0);
    }
    let mut lists = Vec::with_capacity(t.level_ends.len());
    let mut buf = Vec::new();
    for i in 0..t.level_ends.len() {
        buf.clear();
        buf.extend(
            t.level_list(LevelList(i as u32))
                .iter()
                .map(|l| levels[l.index()]),
        );
        lists.push(env.levels.intern_list(&buf)?);
    }
    prof(0, phase_start);
    let phase_start = std::time::Instant::now();
    PROF[5].fetch_add(t.exprs.len() as u64, std::sync::atomic::Ordering::Relaxed);
    let mut exprs: Vec<ExprId> = Vec::with_capacity(t.exprs.len());
    env.exprs.reserve(t.exprs.len());
    for e in &t.exprs {
        let m = |x: ExprId| exprs[x.index()];
        let node = match *e {
            ExprNode::BVar(i) => ExprNode::BVar(i),
            ExprNode::Sort(l) => ExprNode::Sort(levels[l.index()]),
            ExprNode::Const(n, ls) => ExprNode::Const(names[n.index()], lists[ls.0 as usize]),
            ExprNode::App(f, a) => ExprNode::App(m(f), m(a)),
            ExprNode::Lam(bi, n, ty, b) => ExprNode::Lam(bi, names[n.index()], m(ty), m(b)),
            ExprNode::Pi(bi, n, ty, b) => ExprNode::Pi(bi, names[n.index()], m(ty), m(b)),
            ExprNode::Let(l, b) => {
                let lb = t.lets[l.0 as usize];
                let lb = LetBinder {
                    name: names[lb.name.index()],
                    ty: m(lb.ty),
                    value: m(lb.value),
                    nondep: lb.nondep,
                };
                ExprNode::Let(env.exprs.intern_let(lb)?, m(b))
            }
            ExprNode::NatSmall(lo, hi) => ExprNode::NatSmall(lo, hi),
            ExprNode::NatBig(b) => env.exprs.nat_node(t.bigs[b.0 as usize].clone())?,
            ExprNode::Str(s) => ExprNode::Str(strs[s.index()]),
            ExprNode::Proj(n, i, x) => ExprNode::Proj(names[n.index()], i, m(x)),
            ExprNode::FVar(_) => return Err(Fail::malformed("free variable in a declaration")),
        };
        exprs.push(env.exprs.intern(node, &env.levels)?.0);
    }
    prof(1, phase_start);
    let phase_start = std::time::Instant::now();
    let mut decls = Vec::with_capacity(t.decls.len());
    let nl = |env: &mut Env, l: NameList| -> Result<NameList, Fail> {
        let ns: Vec<NameId> = t.name_pool[l.start as usize..(l.start + l.len) as usize]
            .iter()
            .map(|n| names[n.index()])
            .collect();
        env.push_names(&ns)
            .ok_or_else(|| Fail::malformed("too many names in declaration lists"))
    };
    for d in &t.decls {
        let e = |x: ExprId| exprs[x.index()];
        let kind = match d.kind {
            DeclKind::Axiom { is_unsafe } => DeclKind::Axiom { is_unsafe },
            DeclKind::Definition {
                value,
                hints,
                safety,
                all,
            } => DeclKind::Definition {
                value: e(value),
                hints,
                safety,
                all: nl(env, all)?,
            },
            DeclKind::Theorem { value, all } => DeclKind::Theorem {
                value: e(value),
                all: nl(env, all)?,
            },
            DeclKind::Opaque {
                value,
                all,
                is_unsafe,
            } => DeclKind::Opaque {
                value: e(value),
                all: nl(env, all)?,
                is_unsafe,
            },
            DeclKind::Quot { kind } => DeclKind::Quot { kind },
            DeclKind::Inductive {
                num_params,
                num_indices,
                all,
                ctors,
                num_nested,
                is_rec,
                is_reflexive,
                is_unsafe,
            } => DeclKind::Inductive {
                num_params,
                num_indices,
                all: nl(env, all)?,
                ctors: nl(env, ctors)?,
                num_nested,
                is_rec,
                is_reflexive,
                is_unsafe,
            },
            DeclKind::Constructor {
                induct,
                cidx,
                num_params,
                num_fields,
                is_unsafe,
            } => DeclKind::Constructor {
                induct: names[induct.index()],
                cidx,
                num_params,
                num_fields,
                is_unsafe,
            },
            DeclKind::Recursor {
                all,
                num_params,
                num_indices,
                num_motives,
                num_minors,
                rules,
                k,
                is_unsafe,
            } => {
                let rs: Vec<RecRule> = t.rules
                    [rules.start as usize..(rules.start + rules.len) as usize]
                    .iter()
                    .map(|r| RecRule {
                        ctor: names[r.ctor.index()],
                        nfields: r.nfields,
                        rhs: e(r.rhs),
                    })
                    .collect();
                DeclKind::Recursor {
                    all: nl(env, all)?,
                    num_params,
                    num_indices,
                    num_motives,
                    num_minors,
                    rules: env
                        .push_rules(&rs)
                        .ok_or_else(|| Fail::malformed("too many recursor rules"))?,
                    k,
                    is_unsafe,
                }
            }
        };
        decls.push(Decl {
            name: names[d.name.index()],
            level_params: nl(env, d.level_params)?,
            ty: e(d.ty),
            kind,
        });
    }
    prof(2, phase_start);
    Ok((Maps { names, exprs }, decls))
}

/// Intern a module's tape and append its declarations to `env`, grouped
/// into blocks and sorted by dependency. Returns the global ids of the
/// tape's names. `owners` holds the module index of each declaration of
/// `env`, `module` is this one's, and `names` the module names, for
/// messages.
pub fn add_module(
    env: &mut Env,
    t: &Tape,
    owners: &mut Vec<u32>,
    module: u32,
    names: &dyn Fn(u32) -> String,
) -> Result<Vec<NameId>, Fail> {
    let expr_start = env.exprs.len() as u32;
    let (maps, decls) = intern_tape(env, t)?;
    drop(maps.exprs);
    let phase_start = std::time::Instant::now();
    let units = group(env, &decls);
    prof(3, phase_start);
    let phase_start = std::time::Instant::now();
    let order = sort_units(env, &decls, &units, expr_start);
    prof(4, phase_start);
    for u in order {
        let unit = &units[u];
        match unit.kind {
            UnitKind::Singles => {
                for &i in &unit.decls {
                    let start = env.decls.len() as u32;
                    if push_decl(env, decls[i], true, owners, module, names)? {
                        env.blocks.push(Block {
                            start,
                            kind: BlockKind::Single,
                        });
                    }
                }
            }
            UnitKind::Inductive { types, ctors, recs } => {
                let start = env.decls.len() as u32;
                for &i in &unit.decls {
                    push_decl(env, decls[i], false, owners, module, names)?;
                }
                env.blocks.push(Block {
                    start,
                    kind: BlockKind::Inductive { types, ctors, recs },
                })
            }
        }
    }
    Ok(maps.names)
}

/// Append `d`, unless a declaration of that name is already there. Like
/// Lean's `importModules` (`subsumesInfo` in `src/Lean/Environment.lean`),
/// a theorem or axiom may come from several modules (realized constants
/// such as `congr_simp` lemmas are made wherever they are needed) if the
/// copies agree on type and universe parameters; the first copy is the one
/// found by name, a later theorem with a different proof is appended as a
/// shadow (see below), and other copies are dropped (returning `false`).
/// Any other duplicate is rejected.
fn push_decl(
    env: &mut Env,
    d: Decl,
    may_merge: bool,
    owners: &mut Vec<u32>,
    module: u32,
    names: &dyn Fn(u32) -> String,
) -> Result<bool, Fail> {
    let idx = match u32::try_from(env.decls.len()) {
        Ok(i) if i < u32::MAX => i,
        _ => return Err(Fail::malformed("too many declarations")),
    };
    if let Some(&prev) = env.by_name.get(&d.name) {
        let p = env.decls[prev as usize];
        if may_merge && subsumes(env, &p, &d) {
            // Lean keeps the later copy of a theorem. Its proof may differ
            // from the first one's and use later constants, so it cannot
            // replace the first copy, which earlier declarations may use.
            // It is kept as a shadow instead: checked in its own place,
            // but not found by name.
            let same = match (p.kind, d.kind) {
                (DeclKind::Theorem { value: v, .. }, DeclKind::Theorem { value: w, .. }) => v == w,
                (_, DeclKind::Theorem { .. }) => false,
                _ => true,
            };
            if same {
                return Ok(false);
            }
            env.decls.push(d);
            owners.push(module);
            return Ok(true);
        }
        return Err(Fail {
            class: ErrorClass::Rejected,
            msg: format!(
                "constant {} is declared twice, also in module {}",
                env.names.display(d.name),
                names(owners[prev as usize])
            ),
        });
    }
    env.by_name.insert(d.name, idx);
    env.decls.push(d);
    owners.push(module);
    Ok(true)
}

/// Whether Lean's import merges `a` and `b` into one constant (in either
/// direction of `subsumesInfo`).
fn subsumes(env: &Env, a: &Decl, b: &Decl) -> bool {
    if a.ty != b.ty || env.name_list(a.level_params) != env.name_list(b.level_params) {
        return false;
    }
    match (a.kind, b.kind) {
        (DeclKind::Theorem { all: x, .. }, DeclKind::Theorem { all: y, .. }) => {
            env.name_list(x) == env.name_list(y)
        }
        (DeclKind::Theorem { all, .. }, DeclKind::Axiom { is_unsafe: false })
        | (DeclKind::Axiom { is_unsafe: false }, DeclKind::Theorem { all, .. }) => {
            env.name_list(all) == [a.name]
        }
        (DeclKind::Axiom { is_unsafe: u }, DeclKind::Axiom { is_unsafe: v }) => {
            u == v && is_prop_cheap(env, a.ty)
        }
        _ => false,
    }
}

/// Lean's `isPropCheap`: `ty` is `∀ ..., p xs` with `p : ∀ args, Prop`,
/// as many `args` as `xs`.
fn is_prop_cheap(env: &Env, mut ty: ExprId) -> bool {
    while let ExprNode::Pi(_, _, _, b) = env.exprs.get(ty) {
        ty = b;
    }
    let mut nargs = 0usize;
    while let ExprNode::App(f, _) = env.exprs.get(ty) {
        ty = f;
        nargs += 1;
    }
    let ExprNode::Const(n, _) = env.exprs.get(ty) else {
        return false;
    };
    let Some(c) = env.find(n) else {
        return false;
    };
    let mut p = c.ty;
    for _ in 0..nargs {
        let ExprNode::Pi(_, _, _, b) = env.exprs.get(p) else {
            return false;
        };
        p = b;
    }
    matches!(env.exprs.get(p), ExprNode::Sort(l) if l == LevelId::ZERO)
}

enum UnitKind {
    /// Declarations checked one by one (one block each).
    Singles,
    Inductive {
        types: u32,
        ctors: u32,
        recs: u32,
    },
}

struct Unit {
    decls: Vec<usize>,
    kind: UnitKind,
}

/// Group a module's declarations into units: each inductive family with its
/// constructors and recursors, the quotient constants, and the rest one by
/// one.
fn group(env: &Env, decls: &[Decl]) -> Vec<Unit> {
    let by_name: HashMap<NameId, usize> =
        decls.iter().enumerate().map(|(i, d)| (d.name, i)).collect();
    let mut taken = vec![false; decls.len()];
    // Recursors by the first name of their `all` list.
    let mut recs_of: HashMap<NameId, Vec<usize>> = HashMap::new();
    for (i, d) in decls.iter().enumerate() {
        if let DeclKind::Recursor { all, .. } = d.kind
            && let Some(&first) = env.name_list(all).first()
        {
            recs_of.entry(first).or_default().push(i);
        }
    }
    let mut units = Vec::new();
    let mut quot = Vec::new();
    for (i, d) in decls.iter().enumerate() {
        if taken[i] {
            continue;
        }
        match d.kind {
            DeclKind::Inductive { all, .. } => {
                let mut types = Vec::new();
                let names = env.name_list(all);
                if !names.contains(&d.name) {
                    types.push(i);
                    taken[i] = true;
                }
                for n in names {
                    if let Some(&j) = by_name.get(n)
                        && !taken[j]
                        && matches!(decls[j].kind, DeclKind::Inductive { .. })
                    {
                        types.push(j);
                        taken[j] = true;
                    }
                }
                let mut ctors = Vec::new();
                for &ty in &types {
                    let DeclKind::Inductive { ctors: cs, .. } = decls[ty].kind else {
                        unreachable!()
                    };
                    for c in env.name_list(cs) {
                        if let Some(&j) = by_name.get(c)
                            && !taken[j]
                            && matches!(decls[j].kind, DeclKind::Constructor { .. })
                        {
                            ctors.push(j);
                            taken[j] = true;
                        }
                    }
                }
                let mut recs = Vec::new();
                if let Some(rs) = names.first().and_then(|f| recs_of.get(f)) {
                    for &j in rs {
                        if !taken[j] {
                            recs.push(j);
                            taken[j] = true;
                        }
                    }
                }
                let kind = UnitKind::Inductive {
                    types: types.len() as u32,
                    ctors: ctors.len() as u32,
                    recs: recs.len() as u32,
                };
                types.extend(ctors);
                types.extend(recs);
                units.push(Unit { decls: types, kind });
            }
            DeclKind::Quot { kind } => {
                let rank = match kind {
                    QuotKind::Type => 0,
                    QuotKind::Ctor => 1,
                    QuotKind::Lift => 2,
                    QuotKind::Ind => 3,
                };
                quot.push((rank, i));
                taken[i] = true;
            }
            _ => {}
        }
    }
    // Constructors and recursors left over (not in any family here) and
    // everything else: one by one. The checker rejects strays.
    for (i, _) in decls.iter().enumerate() {
        if !taken[i] {
            units.push(Unit {
                decls: vec![i],
                kind: UnitKind::Singles,
            });
        }
    }
    if !quot.is_empty() {
        quot.sort();
        units.push(Unit {
            decls: quot.into_iter().map(|(_, i)| i).collect(),
            kind: UnitKind::Singles,
        });
    }
    units
}

/// Depth-first order of the units: each after the units its terms mention
/// (cycles, which the checker rejects anyway, are broken arbitrarily).
fn sort_units(env: &Env, decls: &[Decl], units: &[Unit], expr_start: u32) -> Vec<usize> {
    let mut unit_of: HashMap<NameId, usize> = HashMap::new();
    for (u, unit) in units.iter().enumerate() {
        for &i in &unit.decls {
            unit_of.insert(decls[i].name, u);
        }
    }
    // Literals refer to these constants implicitly.
    let lit_nat: Vec<usize> = ["Nat"]
        .iter()
        .filter_map(|s| unit_of.get(&env.names.find_dotted(s)?).copied())
        .collect();
    let lit_str: Vec<usize> = ["String", "Char.ofNat", "String.ofList"]
        .iter()
        .filter_map(|s| unit_of.get(&env.names.find_dotted(s)?).copied())
        .collect();
    let n_new = env.exprs.len() - expr_start as usize;
    let mut seen = vec![u32::MAX; n_new];
    let mut work: Vec<ExprId> = Vec::new();
    let mut deps_of = |u: usize, out: &mut Vec<usize>| {
        out.clear();
        work.clear();
        for &i in &units[u].decls {
            let d = &decls[i];
            work.push(d.ty);
            match d.kind {
                DeclKind::Definition { value, .. }
                | DeclKind::Theorem { value, .. }
                | DeclKind::Opaque { value, .. } => work.push(value),
                DeclKind::Recursor { rules, .. } => {
                    work.extend(env.rec_rules(rules).iter().map(|r| r.rhs))
                }
                _ => {}
            }
        }
        while let Some(e) = work.pop() {
            let Some(k) = e.0.checked_sub(expr_start) else {
                continue;
            };
            if seen[k as usize] == u as u32 {
                continue;
            }
            seen[k as usize] = u as u32;
            match env.exprs.get(e) {
                ExprNode::Const(n, _) => {
                    if let Some(&v) = unit_of.get(&n) {
                        out.push(v);
                    }
                }
                ExprNode::App(f, a) => {
                    work.push(f);
                    work.push(a);
                }
                ExprNode::Lam(_, _, t, b) | ExprNode::Pi(_, _, t, b) => {
                    work.push(t);
                    work.push(b);
                }
                ExprNode::Let(l, b) => {
                    let l = env.exprs.let_binder(l);
                    work.push(l.ty);
                    work.push(l.value);
                    work.push(b);
                }
                ExprNode::Proj(n, _, x) => {
                    if let Some(&v) = unit_of.get(&n) {
                        out.push(v);
                    }
                    work.push(x);
                }
                ExprNode::NatSmall(..) | ExprNode::NatBig(_) => out.extend(&lit_nat),
                ExprNode::Str(_) => out.extend(&lit_str),
                ExprNode::BVar(_) | ExprNode::Sort(_) | ExprNode::FVar(_) => {}
            }
        }
        // Quotients need `Eq`; inductives in a unit may also name others.
        out.sort_unstable();
        out.dedup();
        out.retain(|&v| v != u);
    };
    // 0: not visited, 1: on the stack, 2: done.
    let mut state = vec![0u8; units.len()];
    let mut order = Vec::with_capacity(units.len());
    let mut stack: Vec<(usize, Vec<usize>, usize)> = Vec::new();
    let mut spare: Vec<Vec<usize>> = Vec::new();
    for root in 0..units.len() {
        if state[root] != 0 {
            continue;
        }
        let mut d = spare.pop().unwrap_or_default();
        deps_of(root, &mut d);
        state[root] = 1;
        stack.push((root, d, 0));
        while let Some((u, deps, i)) = stack.last_mut() {
            if *i < deps.len() {
                let v = deps[*i];
                *i += 1;
                if state[v] == 0 {
                    let mut d = spare.pop().unwrap_or_default();
                    deps_of(v, &mut d);
                    state[v] = 1;
                    stack.push((v, d, 0));
                }
            } else {
                let u = *u;
                let (_, d, _) = stack.pop().expect("nonempty");
                spare.push(d);
                state[u] = 2;
                order.push(u);
            }
        }
    }
    order
}
