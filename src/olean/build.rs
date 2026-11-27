//! Interning a module's [`Tape`] into the shared arenas ([`Par`]), and
//! putting its declarations in an order the checker can use.
//!
//! [`intern_module`] runs on worker threads, any number of modules at
//! once; [`Assembler::add`] then appends each module's declarations to the
//! environment, in import order, on one thread.
//!
//! A module's `constants` array is in hash-map order (`mkModuleData` in
//! `src/Lean/Environment.lean` folds the kernel's constant map), not in
//! dependency order. The checker only lets a declaration refer to those
//! before it, so the module's declarations are grouped the way `leanexport`
//! groups them (an inductive with its constructors and recursors; the four
//! quotient constants) and then sorted depth-first by the constants their
//! terms mention, the order `leanexport` writes. Modules come in import
//! order, so only references within the module need sorting.

use hashbrown::HashMap;

use super::Fail;
use super::decode::{LAZY, PRE_NAME, Tape};
use super::par::{Local, Par};
use crate::env::{
    Block, BlockKind, Decl, DeclKind, Env, LAZY_BASE, NameList, QuotKind, RecRule, is_lazy,
};
use crate::expr::{ExprData, ExprId, ExprNode, LetBinder};
use crate::level::{LevelId, LevelList, LevelNode};
use crate::name::{NameId, NameNode};
use crate::reader::ErrorClass;
use crate::strings::{Overflow, StrId};

impl From<Overflow> for Fail {
    fn from(o: Overflow) -> Self {
        Fail::malformed(format!("capacity exceeded: {}", o.0))
    }
}

/// A module, interned: its declarations in global ids (their name lists
/// and rules are ranges into `pool` and `rules`), and the order to add
/// them in.
pub struct ModOut {
    decls: Vec<Decl>,
    pool: Vec<NameId>,
    rules: Vec<RecRule>,
    units: Vec<Unit>,
    order: Vec<usize>,
    /// Where each lazily read value is: (declaration, address, holder).
    lazy: HashMap<usize, (u64, u64)>,
    /// The objects lazy values point to that were decoded: (memo slot,
    /// shared id), as in [`super::decode::Tape::frontier`].
    pub frontier: Vec<(u32, u32)>,
}

/// Intern a module's tape into `par`.
pub fn intern_module(par: &Par, loc: &mut Local, t: &Tape) -> Result<ModOut, Fail> {
    let units = group(t);
    let order = sort_units(t, &units);
    let strs: Vec<StrId> = (0..t.strs.len() as u32)
        .map(|i| par.str(t.str(StrId(i))))
        .collect::<Result<_, _>>()?;
    // Names depth by depth: a layer's names do not depend on each other.
    let mut names = vec![NameId::ANON; t.names.len()];
    let mut batch: Vec<(NameNode, u32)> = Vec::new();
    let mut ids: Vec<u32> = Vec::new();
    for d in 0..t.name_order.ends.len() {
        let is = layer(&t.name_order, d);
        batch.clear();
        batch.extend(is.iter().map(|&i| {
            let node = match t.names[i as usize] {
                NameNode::Str(p, s) => NameNode::Str(names[p.index()], strs[s.index()]),
                NameNode::Num(p, k) => NameNode::Num(names[p.index()], k),
                NameNode::Anon => NameNode::Anon,
            };
            (node, 0)
        }));
        ids.clear();
        par.names(loc, &batch, &mut ids)?;
        for (&i, &id) in is.iter().zip(&ids) {
            names[i as usize] = NameId(id);
        }
    }
    let mut levels = Vec::with_capacity(t.levels.len());
    let mut level_hp = Vec::with_capacity(t.levels.len());
    levels.push(LevelId::ZERO);
    level_hp.push(false);
    for l in &t.levels[1..] {
        let g = |x: LevelId| levels[x.index()];
        let node = match *l {
            LevelNode::Zero => LevelNode::Zero,
            LevelNode::Succ(a) => LevelNode::Succ(g(a)),
            LevelNode::Max(a, b) => LevelNode::Max(g(a), g(b)),
            LevelNode::IMax(a, b) => LevelNode::IMax(g(a), g(b)),
            LevelNode::Param(n) => LevelNode::Param(names[n.index()]),
        };
        let (id, hp) = par.level(node)?;
        levels.push(id);
        level_hp.push(hp);
    }
    let mut lists = Vec::with_capacity(t.level_ends.len());
    let mut list_hp = Vec::with_capacity(t.level_ends.len());
    let mut buf = Vec::new();
    for i in 0..t.level_ends.len() {
        buf.clear();
        buf.extend(
            t.level_list(LevelList(i as u32))
                .iter()
                .map(|l| levels[l.index()]),
        );
        let (id, hp) = par.list(&buf)?;
        lists.push(id);
        list_hp.push(hp);
    }
    // Leaves first, height by height: the probes of one height do not
    // wait on each other. Each node's data is computed here from its
    // children's, in the module's own arrays.
    let mut exprs = vec![ExprId(0); t.exprs.len()];
    let mut data = vec![ExprData::new(0, false); t.exprs.len()];
    let mut ebatch: Vec<(ExprNode, u32)> = Vec::new();
    for h in 0..t.expr_order.ends.len() {
        let is = layer(&t.expr_order, h);
        ebatch.clear();
        for &i in is {
            let e = |x: ExprId| exprs[x.index()];
            let dt = |x: ExprId| data[x.index()];
            let n = |x: NameId| names[x.index()];
            let (node, d) = match t.exprs[i as usize] {
                ExprNode::BVar(i) => (ExprNode::BVar(i), ExprData::new(i + 1, false)),
                ExprNode::Sort(l) => (
                    ExprNode::Sort(levels[l.index()]),
                    ExprData::new(0, level_hp[l.index()]),
                ),
                ExprNode::Const(c, ls) => (
                    ExprNode::Const(n(c), lists[ls.0 as usize]),
                    ExprData::new(0, list_hp[ls.0 as usize]),
                ),
                ExprNode::App(f, a) => (ExprNode::App(e(f), e(a)), dt(f).union(dt(a))),
                ExprNode::Lam(bi, x, ty, b) => (
                    ExprNode::Lam(bi, n(x), e(ty), e(b)),
                    dt(ty).union(dt(b).under_binder()),
                ),
                ExprNode::Pi(bi, x, ty, b) => (
                    ExprNode::Pi(bi, n(x), e(ty), e(b)),
                    dt(ty).union(dt(b).under_binder()),
                ),
                ExprNode::Let(l, b) => {
                    let lb = t.lets[l.0 as usize];
                    let d = dt(lb.ty).union(dt(lb.value)).union(dt(b).under_binder());
                    let lb = LetBinder {
                        name: n(lb.name),
                        ty: e(lb.ty),
                        value: e(lb.value),
                        nondep: lb.nondep,
                    };
                    (ExprNode::Let(par.let_binder(lb)?, e(b)), d)
                }
                ExprNode::NatSmall(lo, hi) => (ExprNode::NatSmall(lo, hi), ExprData::new(0, false)),
                ExprNode::NatBig(b) => (
                    ExprNode::NatBig(par.nat_big(&t.bigs[b.0 as usize])?),
                    ExprData::new(0, false),
                ),
                ExprNode::Str(s) => (ExprNode::Str(strs[s.index()]), ExprData::new(0, false)),
                ExprNode::Proj(c, k, x) => (ExprNode::Proj(n(c), k, e(x)), dt(x)),
                ExprNode::FVar(_) => return Err(Fail::malformed("free variable in a declaration")),
            };
            data[i as usize] = d;
            ebatch.push((node, d.bits()));
        }
        ids.clear();
        par.exprs(loc, &ebatch, &mut ids)?;
        for (&i, &id) in is.iter().zip(&ids) {
            exprs[i as usize] = ExprId(id);
        }
    }
    let pool: Vec<NameId> = t.name_pool.iter().map(|n| names[n.index()]).collect();
    let rules: Vec<RecRule> = t
        .rules
        .iter()
        .map(|r| RecRule {
            ctor: names[r.ctor.index()],
            nfields: r.nfields,
            rhs: exprs[r.rhs.index()],
        })
        .collect();
    let e = |x: ExprId| exprs[x.index()];
    let decls = t
        .decls
        .iter()
        .map(|d| {
            let kind = match d.kind {
                DeclKind::Definition {
                    value,
                    hints,
                    safety,
                    all,
                } => DeclKind::Definition {
                    value: e(value),
                    hints,
                    safety,
                    all,
                },
                DeclKind::Theorem { value, all } => DeclKind::Theorem {
                    value: if value == LAZY { LAZY } else { e(value) },
                    all,
                },
                DeclKind::Opaque {
                    value,
                    all,
                    is_unsafe,
                } => DeclKind::Opaque {
                    value: e(value),
                    all,
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
                k => k,
            };
            Decl {
                name: names[d.name.index()],
                level_params: d.level_params,
                ty: e(d.ty),
                kind,
            }
        })
        .collect();
    let lazy = t
        .lazy
        .iter()
        .map(|l| (l.decl as usize, (l.ptr, l.holder)))
        .collect();
    let frontier = t
        .frontier
        .iter()
        .map(|&(a, id)| {
            let g = if id & PRE_NAME != 0 {
                names[(id & !PRE_NAME) as usize].0 | PRE_NAME
            } else {
                exprs[id as usize].0
            };
            (a, g)
        })
        .collect();
    Ok(ModOut {
        decls,
        pool,
        rules,
        units,
        order,
        lazy,
        frontier,
    })
}

/// Layer `d` of `l`.
fn layer(l: &super::decode::Layers, d: usize) -> &[u32] {
    let start = if d == 0 { 0 } else { l.ends[d - 1] as usize };
    &l.order[start..l.ends[d] as usize]
}

/// Appends modules' declarations to an environment, in import order.
pub struct Assembler<'p> {
    pub env: Env,
    par: &'p Par,
    /// The module index of each declaration of `env`.
    owners: Vec<u32>,
    /// The lazily read values: (module, address, holder).
    pub handles: Vec<(u32, u64, u64)>,
}

impl<'p> Assembler<'p> {
    pub fn new(env: Env, par: &'p Par) -> Self {
        Assembler {
            env,
            par,
            owners: Vec::new(),
            handles: Vec::new(),
        }
    }

    /// Add module `module`'s declarations. `names` gives module names, for
    /// messages.
    pub fn add(
        &mut self,
        m: &ModOut,
        module: u32,
        names: &dyn Fn(u32) -> String,
    ) -> Result<(), Fail> {
        for &u in &m.order {
            let unit = &m.units[u];
            match unit.kind {
                UnitKind::Singles => {
                    for &i in &unit.decls {
                        let start = self.env.decls.len() as u32;
                        if self.push(m, i, true, module, names)? {
                            self.env.blocks.push(Block {
                                start,
                                kind: BlockKind::Single,
                            });
                        }
                    }
                }
                UnitKind::Inductive { types, ctors, recs } => {
                    let start = self.env.decls.len() as u32;
                    for &i in &unit.decls {
                        self.push(m, i, false, module, names)?;
                    }
                    self.env.blocks.push(Block {
                        start,
                        kind: BlockKind::Inductive { types, ctors, recs },
                    })
                }
            }
        }
        Ok(())
    }

    fn list(&mut self, m: &ModOut, l: NameList) -> Result<NameList, Fail> {
        self.env
            .push_names(&m.pool[l.start as usize..(l.start + l.len) as usize])
            .ok_or_else(|| Fail::malformed("too many names in declaration lists"))
    }

    /// Module `m`'s declaration `i` with its lists moved into `env`'s pools
    /// (and a lazily read value given its handle).
    fn moved(&mut self, m: &ModOut, i: usize, module: u32) -> Result<Decl, Fail> {
        let mut d = m.decls[i];
        if let DeclKind::Theorem { value, .. } = &mut d.kind
            && *value == LAZY
        {
            let &(ptr, holder) = m
                .lazy
                .get(&i)
                .ok_or_else(|| Fail::malformed("internal: a lazy value without its place"))?;
            let k = self.handles.len();
            if k >= (u32::MAX - LAZY_BASE) as usize {
                return Err(Fail::malformed("too many lazily read values"));
            }
            self.handles.push((module, ptr, holder));
            *value = ExprId(LAZY_BASE + k as u32);
        }
        let kind = match d.kind {
            DeclKind::Definition {
                value,
                hints,
                safety,
                all,
            } => DeclKind::Definition {
                value,
                hints,
                safety,
                all: self.list(m, all)?,
            },
            DeclKind::Theorem { value, all } => DeclKind::Theorem {
                value,
                all: self.list(m, all)?,
            },
            DeclKind::Opaque {
                value,
                all,
                is_unsafe,
            } => DeclKind::Opaque {
                value,
                all: self.list(m, all)?,
                is_unsafe,
            },
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
                all: self.list(m, all)?,
                ctors: self.list(m, ctors)?,
                num_nested,
                is_rec,
                is_reflexive,
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
            } => DeclKind::Recursor {
                all: self.list(m, all)?,
                num_params,
                num_indices,
                num_motives,
                num_minors,
                rules: self
                    .env
                    .push_rules(&m.rules[rules.start as usize..(rules.start + rules.len) as usize])
                    .ok_or_else(|| Fail::malformed("too many recursor rules"))?,
                k,
                is_unsafe,
            },
            k => k,
        };
        Ok(Decl {
            name: d.name,
            level_params: self.list(m, d.level_params)?,
            ty: d.ty,
            kind,
        })
    }

    /// Append declaration `i` of `m`, unless one of that name is already
    /// there. Like Lean's `importModules` (`subsumesInfo` in
    /// `src/Lean/Environment.lean`), a theorem or axiom may come from
    /// several modules (realized constants such as `congr_simp` lemmas are
    /// made wherever they are needed) if the copies agree on type and
    /// universe parameters. The first copy is the one found by name; a
    /// later theorem with a different proof is appended as a shadow (see
    /// below), other copies are dropped (returning `false`). Any other
    /// duplicate is rejected.
    fn push(
        &mut self,
        m: &ModOut,
        i: usize,
        may_merge: bool,
        module: u32,
        names: &dyn Fn(u32) -> String,
    ) -> Result<bool, Fail> {
        let idx = match u32::try_from(self.env.decls.len()) {
            Ok(i) if i < u32::MAX => i,
            _ => return Err(Fail::malformed("too many declarations")),
        };
        let d = self.moved(m, i, module)?;
        if let Some(&prev) = self.env.by_name.get(&d.name) {
            let p = self.env.decls[prev as usize];
            if may_merge && self.subsumes(&p, &d) {
                // Lean keeps the later copy of a theorem. Its proof may
                // differ and use later constants, so it cannot replace the
                // first copy, which earlier declarations may use. It is
                // kept as a shadow: checked in its own place, but not found
                // by name.
                let same = match (p.kind, d.kind) {
                    (DeclKind::Theorem { value: v, .. }, DeclKind::Theorem { value: w, .. }) => {
                        // Values still in their files are not compared:
                        // the copy is kept (and checked).
                        v == w && !is_lazy(v)
                    }
                    (_, DeclKind::Theorem { .. }) => false,
                    _ => true,
                };
                if same {
                    return Ok(false);
                }
                self.env.decls.push(d);
                self.owners.push(module);
                return Ok(true);
            }
            return Err(Fail {
                class: ErrorClass::Rejected,
                msg: format!(
                    "constant {} is declared twice, also in module {}",
                    self.par.display(d.name),
                    names(self.owners[prev as usize])
                ),
            });
        }
        self.env.by_name.insert(d.name, idx);
        self.env.decls.push(d);
        self.owners.push(module);
        Ok(true)
    }

    /// Whether Lean's import merges `a` and `b` into one constant (in
    /// either direction of `subsumesInfo`).
    fn subsumes(&self, a: &Decl, b: &Decl) -> bool {
        let env = &self.env;
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
                u == v && self.is_prop_cheap(a.ty)
            }
            _ => false,
        }
    }

    /// Lean's `isPropCheap`: `ty` is `∀ ..., p xs` with `p : ∀ args, Prop`,
    /// as many `args` as `xs`.
    fn is_prop_cheap(&self, mut ty: ExprId) -> bool {
        let get = |e: ExprId| self.par.expr_node(e);
        while let ExprNode::Pi(_, _, _, b) = get(ty) {
            ty = b;
        }
        let mut nargs = 0usize;
        while let ExprNode::App(f, _) = get(ty) {
            ty = f;
            nargs += 1;
        }
        let ExprNode::Const(n, _) = get(ty) else {
            return false;
        };
        let Some(c) = self.env.find(n) else {
            return false;
        };
        let mut p = c.ty;
        for _ in 0..nargs {
            let ExprNode::Pi(_, _, _, b) = get(p) else {
                return false;
            };
            p = b;
        }
        matches!(get(p), ExprNode::Sort(l) if l == LevelId::ZERO)
    }
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

fn tape_list(t: &Tape, l: NameList) -> &[NameId] {
    &t.name_pool[l.start as usize..(l.start + l.len) as usize]
}

/// Group a module's declarations (in tape ids) into units: each inductive
/// family with its constructors and recursors, the quotient constants, and
/// the rest one by one.
fn group(t: &Tape) -> Vec<Unit> {
    let decls = &t.decls;
    let by_name: HashMap<NameId, usize> =
        decls.iter().enumerate().map(|(i, d)| (d.name, i)).collect();
    let mut taken = vec![false; decls.len()];
    // Recursors by the first name of their `all` list.
    let mut recs_of: HashMap<NameId, Vec<usize>> = HashMap::new();
    for (i, d) in decls.iter().enumerate() {
        if let DeclKind::Recursor { all, .. } = d.kind
            && let Some(&first) = tape_list(t, all).first()
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
                let names = tape_list(t, all);
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
                    for c in tape_list(t, cs) {
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

/// The tape name with the dotted form `s`, if the tape has it.
fn tape_find(t: &Tape, s: &str) -> Option<NameId> {
    let mut cur = NameId::ANON;
    for c in s.split('.') {
        let sid = t.strs.find(c)?;
        let i = t.names.iter().position(|&n| n == NameNode::Str(cur, sid))?;
        cur = NameId(i as u32);
    }
    Some(cur)
}

/// Depth-first order of the units: each after the units its terms mention
/// (cycles, which the checker rejects anyway, are broken arbitrarily).
/// Works on the tape, whose expressions are exactly the module's own terms.
fn sort_units(t: &Tape, units: &[Unit]) -> Vec<usize> {
    let decls = &t.decls;
    let mut unit_of: HashMap<NameId, usize> = HashMap::new();
    for (u, unit) in units.iter().enumerate() {
        for &i in &unit.decls {
            unit_of.insert(decls[i].name, u);
        }
    }
    // Literals refer to these constants implicitly.
    let local = |s: &str| tape_find(t, s).and_then(|n| unit_of.get(&n).copied());
    let lit_nat: Vec<usize> = ["Nat"].iter().filter_map(|s| local(s)).collect();
    let lit_str: Vec<usize> = ["String", "Char.ofNat", "String.ofList"]
        .iter()
        .filter_map(|s| local(s))
        .collect();
    // Which expressions mention a constant of this module at all: the walks
    // below skip the others (most shared subterms only mention imports).
    let mut mentions = Vec::with_capacity(t.exprs.len());
    for e in &t.exprs {
        let m = |x: ExprId| -> bool { mentions[x.index()] };
        let v = match *e {
            ExprNode::Const(n, _) => unit_of.contains_key(&n),
            ExprNode::App(a, b) | ExprNode::Lam(_, _, a, b) | ExprNode::Pi(_, _, a, b) => {
                m(a) || m(b)
            }
            ExprNode::Let(l, b) => {
                let l = t.lets[l.0 as usize];
                m(l.ty) || m(l.value) || m(b)
            }
            ExprNode::Proj(n, _, x) => unit_of.contains_key(&n) || m(x),
            ExprNode::NatSmall(..) | ExprNode::NatBig(_) => !lit_nat.is_empty(),
            ExprNode::Str(_) => !lit_str.is_empty(),
            ExprNode::BVar(_) | ExprNode::Sort(_) | ExprNode::FVar(_) => false,
        };
        mentions.push(v);
    }
    let mut seen = vec![u32::MAX; t.exprs.len()];
    let mut work: Vec<ExprId> = Vec::new();
    let mut lazy_of = vec![u32::MAX; decls.len()];
    for (j, lv) in t.lazy.iter().enumerate() {
        lazy_of[lv.decl as usize] = j as u32;
    }
    let mut deps_of = |u: usize, out: &mut Vec<usize>| {
        out.clear();
        work.clear();
        for &i in &units[u].decls {
            let d = &decls[i];
            work.push(d.ty);
            match d.kind {
                DeclKind::Theorem { value, .. } if value == LAZY => {
                    // Scanned at decode time instead.
                    let lv = &t.lazy[lazy_of[i] as usize];
                    let (start, len) = (lv.refs.0 as usize, lv.refs.1 as usize);
                    for n in &t.lazy_refs[start..start + len] {
                        out.extend(unit_of.get(n));
                    }
                    if lv.nat_lit {
                        out.extend(&lit_nat);
                    }
                    if lv.str_lit {
                        out.extend(&lit_str);
                    }
                }
                DeclKind::Definition { value, .. }
                | DeclKind::Theorem { value, .. }
                | DeclKind::Opaque { value, .. } => work.push(value),
                DeclKind::Recursor { rules, .. } => work.extend(
                    t.rules[rules.start as usize..(rules.start + rules.len) as usize]
                        .iter()
                        .map(|r| r.rhs),
                ),
                _ => {}
            }
        }
        while let Some(e) = work.pop() {
            let k = e.index();
            if !mentions[k] || seen[k] == u as u32 {
                continue;
            }
            seen[k] = u as u32;
            match t.exprs[k] {
                ExprNode::Const(n, _) => out.extend(unit_of.get(&n)),
                ExprNode::App(f, a) => {
                    work.push(f);
                    work.push(a);
                }
                ExprNode::Lam(_, _, ty, b) | ExprNode::Pi(_, _, ty, b) => {
                    work.push(ty);
                    work.push(b);
                }
                ExprNode::Let(l, b) => {
                    let l = t.lets[l.0 as usize];
                    work.push(l.ty);
                    work.push(l.value);
                    work.push(b);
                }
                ExprNode::Proj(n, _, x) => {
                    out.extend(unit_of.get(&n));
                    work.push(x);
                }
                ExprNode::NatSmall(..) | ExprNode::NatBig(_) => out.extend(&lit_nat),
                ExprNode::Str(_) => out.extend(&lit_str),
                ExprNode::BVar(_) | ExprNode::Sort(_) | ExprNode::FVar(_) => {}
            }
        }
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
        while let Some((_, deps, i)) = stack.last_mut() {
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
                let (u, d, _) = stack.pop().expect("nonempty");
                spare.push(d);
                state[u] = 2;
                order.push(u);
            }
        }
    }
    order
}
