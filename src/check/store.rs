//! The term store a type checker works in: the environment's arenas,
//! read-only and shared, plus a private overlay for the names, levels,
//! expressions and declarations built while checking.
//!
//! Names, levels, lets and big literals of the overlay have ids with the
//! top bit set. Expressions are different: the overlay's are in blocks of
//! ids the environment's arena lends above its own (see `crate::slab`), so
//! that a node or its data is read with one load, whoever made it
//! ([`Store::is_local_expr`] tells the two apart). A node is looked up in
//! the environment's arena before it is added to the overlay (only when
//! all its children are environment ids: otherwise it cannot be there), so
//! every term still has exactly one id and id equality stays structural
//! equality. The overlay is dropped between declarations, which bounds the
//! memory a check holds and keeps the shared environment immutable, so
//! independent declarations can be checked on several threads, each with
//! its own store. (nanoda_lib also keeps per-checker arenas on top of a
//! shared one.)

use hashbrown::HashTable;
use num_bigint::BigUint;

use crate::env::{Decl, Env, NameList, RecRule, RuleList};
use crate::expr::{BigId, BinderInfo, ExprData, ExprId, ExprNode, LetBinder, LetId, big_hash};
use crate::intern::{Interner, Node};
use crate::level::{LevelId, LevelList, LevelNode, LevelParams, list_at, list_hash};
use crate::name::{NameId, NameNode};
use crate::slab::{BLOCK, Block, Reader};
use crate::strings::StrId;

/// The bit that marks an overlay id.
pub const LOCAL: u32 = 1 << 31;

#[inline]
pub fn is_local(id: u32) -> bool {
    id & LOCAL != 0
}

/// Raised (as a panic, caught by the driver) when an overlay outgrows its
/// 31-bit ids. Checking a declaration that builds two billion terms is a
/// resource failure, not a verdict.
pub const OVERFLOW_MSG: &str =
    "nitrolean: resource limit: a declaration built more than 2^31 terms";

/// Raised when unary reduction of a literal exhausts its allocation budget.
pub(super) struct NatUnfoldLimit;

impl NatUnfoldLimit {
    pub(super) const MESSAGE: &str =
        "resource limit: too much unary reduction of large Nat literals";
}

/// Raised (likewise) when the stores checking at once have used up the
/// expression ids above the environment's: they share 2^31 ids.
pub const EXPR_IDS_MSG: &str =
    "nitrolean: resource limit: the declarations being checked built more than 2^31 terms in all";

fn local_id(i: u32) -> u32 {
    assert!(i < LOCAL, "{OVERFLOW_MSG}");
    i | LOCAL
}

pub struct Store<'e> {
    pub env: &'e Env,
    pub(super) decls: &'e [Decl],
    limit_nat_unfold: bool,
    nat_unfold_work: u64,
    names: Interner<NameNode>,
    levels: Interner<LevelNode>,
    level_params: Vec<LevelParams>,
    list_data: Vec<LevelId>,
    /// List `i` is from `list_offs[i]` to `list_offs[i + 1]`.
    list_offs: Vec<u32>,
    list_hp: Vec<bool>,
    list_table: HashTable<u32>,
    /// Expression nodes and their data, the environment's and this
    /// store's own alike: one array each (see `crate::slab`).
    nodes: Reader<'e, ExprNode>,
    edata: Reader<'e, ExprData>,
    /// The environment's expressions are the ids below this; the store's
    /// own are in its blocks, above.
    env_exprs: u32,
    exprs: LocalExprs<'e>,
    lets: Interner<LetBinder>,
    bigs: Vec<BigUint>,
    big_table: HashTable<u32>,
    decl_names: Vec<NameId>,
    decl_rules: Vec<RecRule>,
    /// Scratch memo for the traversals in `subst.rs`.
    pub(crate) memo: IdMap<(ExprId, u32), ExprId>,
    /// `univ::normalize`'s results (see `NORM_MEMO`).
    pub(crate) norm_memo: IdMap<LevelId, LevelId>,
}

/// The overlay's expressions: blocks of ids lent by the environment's
/// arena, filled in order, and a table of the ones hash-consed.
struct LocalExprs<'e> {
    blocks: Vec<Block<'e, ExprNode, ExprData>>,
    /// Slots used in the last block ([`BLOCK`] before the first block,
    /// so that the next push takes one).
    fill: u32,
    count: usize,
    table: HashTable<u32>,
}

impl Default for LocalExprs<'_> {
    fn default() -> Self {
        LocalExprs {
            blocks: Vec::new(),
            fill: BLOCK,
            count: 0,
            table: HashTable::new(),
        }
    }
}

impl<'e> Store<'e> {
    #[cfg(test)]
    pub fn new(env: &'e Env) -> Self {
        Self::with_decls(env, &env.decls, true)
    }

    pub(super) fn with_decls(env: &'e Env, decls: &'e [Decl], limit_nat_unfold: bool) -> Self {
        Store {
            env,
            decls,
            limit_nat_unfold,
            nat_unfold_work: 0,
            names: Interner::new("too many names"),
            levels: Interner::new("too many levels"),
            level_params: Vec::new(),
            list_data: Vec::new(),
            list_offs: vec![0],
            list_hp: Vec::new(),
            list_table: HashTable::new(),
            nodes: env.exprs.node_reader(),
            edata: env.exprs.data_reader(),
            env_exprs: env.exprs.len() as u32,
            exprs: LocalExprs::default(),
            lets: Interner::new("too many let binders"),
            bigs: Vec::new(),
            big_table: HashTable::new(),
            decl_names: Vec::new(),
            decl_rules: Vec::new(),
            memo: IdMap::default(),
            norm_memo: IdMap::default(),
        }
    }

    /// Drop the overlay. Every overlay id becomes invalid.
    pub fn clear(&mut self) {
        // The first block of expression ids is kept for the next
        // declaration.
        let mut blocks = std::mem::take(&mut self.exprs.blocks);
        blocks.truncate(1);
        *self = self.fresh();
        if !blocks.is_empty() {
            self.exprs.fill = 0;
        }
        self.exprs.blocks = blocks;
    }

    pub(super) fn fresh(&self) -> Self {
        Self::with_decls(self.env, self.decls, self.limit_nat_unfold)
    }

    pub(super) fn reset_nat_unfold_work(&mut self) {
        self.nat_unfold_work = 0;
    }

    /// One constructor view of a literal is cheap, but recursing on its
    /// predecessors can build huge stacks and retain every intermediate Nat.
    /// Without all the checked Nat shortcuts, charge for large literals,
    /// with a larger charge for larger integer copies.
    /// The store follows both evaluators, so a fallback shares the budget.
    pub(super) fn charge_nat_unfold(&mut self, bits: u64) {
        if bits > 16 && self.limit_nat_unfold {
            self.nat_unfold_work += bits.div_ceil(1 << 16);
            if self.nat_unfold_work > 1 << 15 {
                std::panic::resume_unwind(Box::new(NatUnfoldLimit));
            }
        }
    }

    /// Number of overlay expressions.
    pub fn local_exprs(&self) -> usize {
        self.exprs.count
    }

    /// Whether `e` is one of the overlay's expressions (the other ids of
    /// expressions are the environment's).
    #[inline]
    pub fn is_local_expr(&self, e: ExprId) -> bool {
        e.0 >= self.env_exprs
    }

    /// Whether `e` can be read: an environment id, or one of the overlay's
    /// (for debug assertions).
    fn readable(&self, e: ExprId) -> bool {
        let n = self.exprs.blocks.len();
        e.0 < self.env_exprs
            || self
                .exprs
                .blocks
                .iter()
                .enumerate()
                .any(|(k, b)| b.contains(e.0) && (k + 1 < n || e.0 - b.first() < self.exprs.fill))
    }

    // ---- names ----

    #[inline]
    pub fn name(&self, n: NameId) -> NameNode {
        if is_local(n.0) {
            *self.names.get(n.0 & !LOCAL)
        } else {
            self.env.names.get(n)
        }
    }

    pub fn mk_name(&mut self, node: NameNode) -> NameId {
        let global = match node {
            NameNode::Anon => return NameId::ANON,
            NameNode::Str(p, _) | NameNode::Num(p, _) => !is_local(p.0),
        };
        if global && let Some(n) = self.env.names.find(node) {
            return n;
        }
        let (i, _) = self.names.intern(node).expect("names");
        NameId(local_id(i))
    }

    pub fn str(&self, s: StrId) -> &str {
        self.env.names.strings.get(s)
    }

    /// `n` with its prefix `old` replaced by `new`, if `old` is a prefix.
    pub fn replace_prefix(&mut self, n: NameId, old: NameId, new: NameId) -> Option<NameId> {
        if n == old {
            return Some(new);
        }
        match self.name(n) {
            NameNode::Anon => None,
            NameNode::Str(p, s) => {
                let p = self.replace_prefix(p, old, new)?;
                Some(self.mk_name(NameNode::Str(p, s)))
            }
            NameNode::Num(p, k) => {
                let p = self.replace_prefix(p, old, new)?;
                Some(self.mk_name(NameNode::Num(p, k)))
            }
        }
    }

    pub fn is_prefix_of(&self, pre: NameId, mut n: NameId) -> bool {
        loop {
            if n == pre {
                return true;
            }
            match self.name(n) {
                NameNode::Anon => return false,
                NameNode::Str(p, _) | NameNode::Num(p, _) => n = p,
            }
        }
    }

    pub fn show(&self, n: NameId) -> String {
        let mut comps = Vec::new();
        let mut cur = n;
        loop {
            match self.name(cur) {
                NameNode::Anon => break,
                NameNode::Str(p, s) => {
                    comps.push(self.str(s).to_string());
                    cur = p;
                }
                NameNode::Num(p, k) => {
                    comps.push(k.to_string());
                    cur = p;
                }
            }
        }
        if comps.is_empty() {
            return "[anonymous]".into();
        }
        comps.reverse();
        comps.join(".")
    }

    // ---- levels ----

    #[inline]
    pub fn level(&self, l: LevelId) -> LevelNode {
        if is_local(l.0) {
            *self.levels.get(l.0 & !LOCAL)
        } else {
            self.env.levels.get(l)
        }
    }

    #[inline]
    pub fn level_has_param(&self, l: LevelId) -> bool {
        self.level_params(l) != LevelParams::None
    }

    #[inline]
    pub(crate) fn level_params(&self, l: LevelId) -> LevelParams {
        if is_local(l.0) {
            self.level_params[(l.0 & !LOCAL) as usize]
        } else {
            self.env.levels.params(l)
        }
    }

    pub fn mk_level(&mut self, node: LevelNode) -> LevelId {
        let global = match node {
            LevelNode::Zero => return LevelId::ZERO,
            LevelNode::Succ(a) => !is_local(a.0),
            LevelNode::Max(a, b) | LevelNode::IMax(a, b) => !is_local(a.0) && !is_local(b.0),
            LevelNode::Param(n) => !is_local(n.0),
        };
        if global && let Some(l) = self.env.levels.find(&node) {
            return l;
        }
        let (i, fresh) = self.levels.intern(node).expect("levels");
        if fresh {
            let params = LevelParams::of_node(node, |l| self.level_params(l));
            self.level_params.push(params);
        }
        LevelId(local_id(i))
    }

    pub fn succ(&mut self, l: LevelId) -> LevelId {
        self.mk_level(LevelNode::Succ(l))
    }

    pub fn max(&mut self, a: LevelId, b: LevelId) -> LevelId {
        self.mk_level(LevelNode::Max(a, b))
    }

    pub fn imax(&mut self, a: LevelId, b: LevelId) -> LevelId {
        self.mk_level(LevelNode::IMax(a, b))
    }

    pub fn param(&mut self, n: NameId) -> LevelId {
        self.mk_level(LevelNode::Param(n))
    }

    #[inline(always)]
    fn local_list(&self, i: usize) -> &[LevelId] {
        list_at(&self.list_data, &self.list_offs, i)
    }

    #[inline(always)]
    pub fn list(&self, l: LevelList) -> &[LevelId] {
        if is_local(l.0) {
            self.local_list((l.0 & !LOCAL) as usize)
        } else {
            self.env.levels.list(l)
        }
    }

    pub fn list_has_param(&self, l: LevelList) -> bool {
        if is_local(l.0) {
            self.list_hp[(l.0 & !LOCAL) as usize]
        } else {
            self.env.levels.list_has_param(l)
        }
    }

    pub fn mk_list(&mut self, ls: &[LevelId]) -> LevelList {
        if ls.is_empty() {
            return LevelList::EMPTY;
        }
        if ls.iter().all(|l| !is_local(l.0))
            && let Some(l) = self.env.levels.find_list(ls)
        {
            return l;
        }
        let h = list_hash(ls);
        let Self {
            list_data,
            list_offs,
            list_table,
            ..
        } = self;
        if let Some(&id) =
            list_table.find(h, |&id| list_at(list_data, list_offs, id as usize) == ls)
        {
            return LevelList(id | LOCAL);
        }
        let id = (list_offs.len() - 1) as u32;
        list_data.extend_from_slice(ls);
        list_offs.push(list_data.len() as u32);
        let (list_data, list_offs) = (&*list_data, &*list_offs);
        list_table.insert_unique(h, id, |&id| {
            list_hash(list_at(list_data, list_offs, id as usize))
        });
        let hp = ls.iter().any(|&l| self.level_has_param(l));
        self.list_hp.push(hp);
        LevelList(local_id(id))
    }

    // ---- expressions ----

    #[inline]
    pub fn node(&self, e: ExprId) -> ExprNode {
        debug_assert!(
            self.readable(e),
            "expression id {} is not this store's",
            e.0
        );
        self.nodes.get(e.0)
    }

    #[inline]
    pub fn data(&self, e: ExprId) -> ExprData {
        debug_assert!(
            self.readable(e),
            "expression id {} is not this store's",
            e.0
        );
        self.edata.get(e.0)
    }

    #[inline]
    pub fn has_loose_bvars(&self, e: ExprId) -> bool {
        self.data(e).has_loose_bvars()
    }

    #[inline]
    pub fn has_fvar(&self, e: ExprId) -> bool {
        self.data(e).has_fvar()
    }

    pub fn let_binder(&self, l: LetId) -> LetBinder {
        if is_local(l.0) {
            *self.lets.get(l.0 & !LOCAL)
        } else {
            self.env.exprs.let_binder(l)
        }
    }

    pub fn big(&self, b: BigId) -> &BigUint {
        if is_local(b.0) {
            &self.bigs[(b.0 & !LOCAL) as usize]
        } else {
            self.env.exprs.big(b)
        }
    }

    fn all_global(&self, node: &ExprNode) -> bool {
        let g = |x: u32| !is_local(x);
        let ge = |e: ExprId| e.0 < self.env_exprs;
        match *node {
            ExprNode::BVar(_) | ExprNode::NatSmall(..) | ExprNode::Str(_) => true,
            ExprNode::Sort(l) => g(l.0),
            ExprNode::Const(n, ls) => g(n.0) && g(ls.0),
            ExprNode::App(f, a) => ge(f) && ge(a),
            ExprNode::Lam(_, n, t, b) | ExprNode::Pi(_, n, t, b) => g(n.0) && ge(t) && ge(b),
            ExprNode::Let(h, b) => g(h.0) && ge(b),
            ExprNode::NatBig(b) => g(b.0),
            ExprNode::Proj(n, _, e) => g(n.0) && ge(e),
            ExprNode::FVar(_) => false,
        }
    }

    /// The id of `node`, adding it to the overlay if it is new.
    #[inline]
    pub fn mk(&mut self, node: ExprNode) -> ExprId {
        if self.all_global(&node)
            && let Some(e) = self.env.exprs.find(&node)
        {
            return e;
        }
        self.mk_local(node)
    }

    /// `node` with an id of its own, not looked up or indexed (see
    /// [`crate::env::TermSink::expr_owned`]).
    pub fn mk_owned(&mut self, node: ExprNode) -> ExprId {
        let d = self.data_of(node);
        self.push_local(node, d)
    }

    fn mk_local(&mut self, node: ExprNode) -> ExprId {
        let h = node.hash();
        let nodes = self.nodes;
        if let Some(&id) = self.exprs.table.find(h, |&id| nodes.get(id).same(&node)) {
            return ExprId(id);
        }
        let d = self.data_of(node);
        let e = self.push_local(node, d);
        self.exprs
            .table
            .insert_unique(h, e.0, |&id| nodes.get(id).hash());
        e
    }

    /// Add `node`, with data `d`, to the overlay's arrays (not its table).
    #[inline]
    fn push_local(&mut self, node: ExprNode, d: ExprData) -> ExprId {
        if self.exprs.fill == BLOCK {
            self.new_block();
        }
        let slot = self.exprs.fill;
        let Some(b) = self.exprs.blocks.last_mut() else {
            unreachable!("a block")
        };
        b.put(slot, node, d);
        self.exprs.fill = slot + 1;
        self.exprs.count += 1;
        ExprId(b.first() + slot)
    }

    #[cold]
    #[inline(never)]
    fn new_block(&mut self) {
        // Checked in every build: an id never wraps into another store's.
        let b = self.env.exprs.take_block().expect(EXPR_IDS_MSG);
        self.exprs.blocks.push(b);
        self.exprs.fill = 0;
    }

    /// The data of a node whose children are known.
    #[inline]
    fn data_of(&self, node: ExprNode) -> ExprData {
        match node {
            ExprNode::BVar(i) => ExprData::new((i + 1).min(ExprData::MAX_RANGE), false),
            ExprNode::Sort(l) => ExprData::new(0, self.level_has_param(l)),
            ExprNode::Const(_, ls) => ExprData::new(0, self.list_has_param(ls)),
            ExprNode::App(f, a) => self.data(f).union(self.data(a)),
            ExprNode::Lam(_, _, t, b) | ExprNode::Pi(_, _, t, b) => {
                self.data(t).union(self.data(b).under_binder())
            }
            ExprNode::Let(h, b) => {
                let h = self.let_binder(h);
                self.data(h.ty)
                    .union(self.data(h.value))
                    .union(self.data(b).under_binder())
            }
            ExprNode::NatSmall(..) | ExprNode::NatBig(_) | ExprNode::Str(_) => {
                ExprData::new(0, false)
            }
            ExprNode::Proj(_, _, e) => self.data(e),
            ExprNode::FVar(_) => ExprData::FVAR,
        }
    }

    pub fn bvar(&mut self, i: u32) -> ExprId {
        assert!(i < ExprData::MAX_RANGE, "{OVERFLOW_MSG}");
        self.mk(ExprNode::BVar(i))
    }

    pub fn sort(&mut self, l: LevelId) -> ExprId {
        self.mk(ExprNode::Sort(l))
    }

    pub fn cnst(&mut self, n: NameId, ls: LevelList) -> ExprId {
        self.mk(ExprNode::Const(n, ls))
    }

    pub fn app(&mut self, f: ExprId, a: ExprId) -> ExprId {
        self.mk(ExprNode::App(f, a))
    }

    pub fn apps(&mut self, mut f: ExprId, args: &[ExprId]) -> ExprId {
        for &a in args {
            f = self.app(f, a);
        }
        f
    }

    pub fn lam(&mut self, bi: BinderInfo, n: NameId, t: ExprId, b: ExprId) -> ExprId {
        self.mk(ExprNode::Lam(bi, n, t, b))
    }

    pub fn pi(&mut self, bi: BinderInfo, n: NameId, t: ExprId, b: ExprId) -> ExprId {
        self.mk(ExprNode::Pi(bi, n, t, b))
    }

    pub fn proj(&mut self, s: NameId, i: u32, e: ExprId) -> ExprId {
        self.mk(ExprNode::Proj(s, i, e))
    }

    pub fn fvar(&mut self, i: u32) -> ExprId {
        self.mk_local(ExprNode::FVar(i))
    }

    pub fn mk_let(&mut self, name: NameId, ty: ExprId, value: ExprId, body: ExprId) -> ExprId {
        let b = LetBinder {
            name,
            ty,
            value,
            nondep: false,
        };
        self.mk_let_binder(b, body)
    }

    fn mk_let_binder(&mut self, b: LetBinder, body: ExprId) -> ExprId {
        let LetBinder {
            name, ty, value, ..
        } = b;
        let h = if !is_local(name.0) && !self.is_local_expr(ty) && !self.is_local_expr(value) {
            self.env.exprs.find_let(&b)
        } else {
            None
        };
        let h = match h {
            Some(h) => h,
            None => LetId(local_id(self.lets.intern(b).expect("lets").0)),
        };
        self.mk(ExprNode::Let(h, body))
    }

    /// The literal `n`.
    pub fn nat(&mut self, n: BigUint) -> ExprId {
        if let Ok(v) = u64::try_from(&n) {
            return self.nat_u64(v);
        }
        if let Some(b) = self.env.exprs.find_big(&n) {
            return self.mk(ExprNode::NatBig(b));
        }
        let h = big_hash(&n);
        let Self {
            bigs, big_table, ..
        } = self;
        let id = if let Some(&id) = big_table.find(h, |&id| bigs[id as usize] == n) {
            id
        } else {
            let id = bigs.len() as u32;
            bigs.push(n);
            let bigs = &*bigs;
            big_table.insert_unique(h, id, |&id| big_hash(&bigs[id as usize]));
            id
        };
        self.mk_local(ExprNode::NatBig(BigId(local_id(id))))
    }

    pub fn nat_u64(&mut self, v: u64) -> ExprId {
        self.mk(ExprNode::NatSmall(v as u32, (v >> 32) as u32))
    }

    // ---- application spines ----

    /// The head of an application spine.
    #[inline]
    pub fn head(&self, mut e: ExprId) -> ExprId {
        while let ExprNode::App(f, _) = self.node(e) {
            e = f;
        }
        e
    }

    /// The head and arguments (in order) of an application spine.
    pub fn spine(&self, mut e: ExprId, args: &mut Vec<ExprId>) -> ExprId {
        args.clear();
        while let ExprNode::App(f, a) = self.node(e) {
            args.push(a);
            e = f;
        }
        args.reverse();
        e
    }

    pub fn nargs(&self, mut e: ExprId) -> usize {
        let mut n = 0;
        while let ExprNode::App(f, _) = self.node(e) {
            n += 1;
            e = f;
        }
        n
    }

    /// The constant at the head of `e`, if any.
    pub fn head_const(&self, e: ExprId) -> Option<(NameId, LevelList)> {
        match self.node(self.head(e)) {
            ExprNode::Const(n, ls) => Some((n, ls)),
            _ => None,
        }
    }

    // ---- declaration pools ----

    /// Whether `ls` is the parameters `ps` themselves, in order: then
    /// substituting `ls` for `ps` changes nothing (see `OWN_LEVELS`).
    pub fn is_own_levels(&self, ps: &[NameId], ls: &[LevelId]) -> bool {
        ps.len() == ls.len()
            && ps
                .iter()
                .zip(ls)
                .all(|(&p, &l)| self.level(l) == LevelNode::Param(p))
    }

    pub fn name_list(&self, l: NameList) -> &[NameId] {
        if is_local(l.start) {
            let s = (l.start & !LOCAL) as usize;
            &self.decl_names[s..s + l.len as usize]
        } else {
            self.env.name_list(l)
        }
    }

    pub fn rec_rules(&self, l: RuleList) -> &[RecRule] {
        if is_local(l.start) {
            let s = (l.start & !LOCAL) as usize;
            &self.decl_rules[s..s + l.len as usize]
        } else {
            self.env.rec_rules(l)
        }
    }

    pub fn push_names(&mut self, ns: &[NameId]) -> NameList {
        let start = local_id(self.decl_names.len() as u32);
        self.decl_names.extend_from_slice(ns);
        NameList {
            start,
            len: ns.len() as u32,
        }
    }

    pub fn push_rules(&mut self, rs: &[RecRule]) -> RuleList {
        let start = local_id(self.decl_rules.len() as u32);
        self.decl_rules.extend_from_slice(rs);
        RuleList {
            start,
            len: rs.len() as u32,
        }
    }

    pub fn lparams(&self, d: &Decl) -> &[NameId] {
        self.name_list(d.level_params)
    }
}

/// A fast hasher for maps keyed by ids.
#[derive(Default, Clone, Copy)]
pub struct IdHasher(u64);

impl std::hash::Hasher for IdHasher {
    #[inline]
    fn finish(&self) -> u64 {
        crate::hash::hash2(self.0, 0x9e37_79b9_7f4a_7c15)
    }
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = (self.0.rotate_left(8) ^ b as u64).wrapping_mul(0x100_0000_01b3);
        }
    }
    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.0 = (self.0.rotate_left(32) ^ i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
    }
    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.0 = (self.0.rotate_left(32) ^ i).wrapping_mul(0x9e37_79b9_7f4a_7c15);
    }
    #[inline]
    fn write_u8(&mut self, i: u8) {
        self.write_u32(i as u32)
    }
    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.write_u64(i as u64)
    }
}

pub type IdBuild = std::hash::BuildHasherDefault<IdHasher>;
pub type IdMap<K, V> = hashbrown::HashMap<K, V, IdBuild>;
pub type IdSet<K> = hashbrown::HashSet<K, IdBuild>;

/// A value read lazily from an `.olean` file is built in the store, like
/// the checker's own terms (see [`Env::value_into`]).
impl crate::env::TermSink for Store<'_> {
    fn name(&mut self, node: NameNode) -> NameId {
        self.mk_name(node)
    }

    fn level(&mut self, node: LevelNode) -> LevelId {
        self.mk_level(node)
    }

    fn list(&mut self, levels: &[LevelId]) -> LevelList {
        self.mk_list(levels)
    }

    fn expr(&mut self, node: ExprNode) -> ExprId {
        self.mk(node)
    }

    fn expr_owned(&mut self, node: ExprNode) -> ExprId {
        self.mk_owned(node)
    }

    fn let_in(&mut self, binder: LetBinder, body: ExprId) -> ExprId {
        self.mk_let_binder(binder, body)
    }

    fn nat_big(&mut self, n: BigUint) -> ExprId {
        self.nat(n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Running out of expression ids is a clear error, in every build.
    #[test]
    fn out_of_expression_ids() {
        let env = Env::new();
        let mut held = Vec::new();
        while let Some(b) = env.exprs.take_block() {
            held.push(b);
        }
        assert!(!held.is_empty());
        let mut st = Store::new(&env);
        let err = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| st.bvar(0)))
            .expect_err("no ids left");
        let msg = err
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| err.downcast_ref::<&str>().copied());
        assert_eq!(msg, Some(EXPR_IDS_MSG));
        // Ids given back are lent again.
        drop(held.pop());
        let mut st = Store::new(&env);
        let e = st.bvar(0);
        assert!(st.is_local_expr(e));
        assert_eq!(st.node(e), ExprNode::BVar(0));
    }
}
