//! Expressions (`Lean.Expr`), hash-consed.
//!
//! Each node is a 16-byte enum (asserted in the tests) plus 4 bytes of cached
//! data, kept in a parallel array: the loose bound-variable range and a few
//! flags. That cached data follows Lean's own `Expr.Data` (see
//! `src/Lean/Expr.lean`), which also caps the loose bvar range at 2^20 - 1.
//! Children are canonical ids, so the hash-consing table compares nodes
//! shallowly. No node owns heap memory: `let` binders (four fields) live in a
//! side arena, big literals and strings in pools, and constant universe
//! instances in the interned level lists.
//!
//! `Expr.mdata` is not represented: it is kernel-transparent, and the reader
//! maps an `mdata` record to the id of its inner expression.

use num_bigint::BigUint;

use crate::hash::{hash_bytes, hash2};
use crate::intern::{Big, IdTable, Interner, Node};
use crate::level::{LevelId, LevelList, Levels};
use crate::name::NameId;
use crate::slab::{Block, Pool, Reader, Slab, atomic_u32};
use crate::strings::{Overflow, StrId};
use std::sync::atomic::Ordering;

/// Id of an interned expression.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct ExprId(pub(crate) u32);

impl ExprId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Id of an interned `let` binder (name, type, value, nondep).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct LetId(pub(crate) u32);

/// Id of an interned big natural literal (at least 2^64).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BigId(pub(crate) u32);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ExprNode {
    BVar(u32),
    Sort(LevelId),
    Const(NameId, LevelList),
    App(ExprId, ExprId),
    /// Binder name, binder type, body.
    Lam(BinderInfo, NameId, ExprId, ExprId),
    Pi(BinderInfo, NameId, ExprId, ExprId),
    Let(LetId, ExprId),
    /// A literal below 2^64, as (low, high) 32-bit halves. Literals below
    /// 2^64 are always stored this way, so equal values get equal ids.
    NatSmall(u32, u32),
    NatBig(BigId),
    Str(StrId),
    /// Structure name, field index, structure value.
    Proj(NameId, u32, ExprId),
    /// A free variable, an index into the type checker's local context.
    /// Exports never contain these; only the type checker makes them.
    FVar(u32),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct LetBinder {
    pub name: NameId,
    pub ty: ExprId,
    pub value: ExprId,
    pub nondep: bool,
}

// Binder names and annotations are not part of a term's identity: nodes
// that differ only in them are interned as one (keeping the first one's
// names, which only show in messages). The kernel never looks at them, and
// Lean's own expression equality ignores them too, so alpha-equivalent
// terms get equal ids and every cache and quick check sees them as equal.

impl Node for LetBinder {
    fn hash(&self) -> u64 {
        hash2(0x1e7, (self.ty.0 as u64) << 32 | self.value.0 as u64)
    }

    #[inline]
    fn same(&self, o: &Self) -> bool {
        self.ty == o.ty && self.value == o.value
    }
}

impl Node for ExprNode {
    #[inline]
    fn hash(&self) -> u64 {
        let (tag, a, b, c): (u64, u32, u32, u32) = match *self {
            ExprNode::BVar(i) => (0, i, 0, 0),
            ExprNode::Sort(l) => (1, l.0, 0, 0),
            ExprNode::Const(n, ls) => (2, n.0, ls.0, 0),
            ExprNode::App(f, a) => (3, f.0, a.0, 0),
            ExprNode::Lam(_, _, t, b) => (4, 0, t.0, b.0),
            ExprNode::Pi(_, _, t, b) => (5, 0, t.0, b.0),
            ExprNode::Let(h, b) => (6, h.0, b.0, 0),
            ExprNode::NatSmall(lo, hi) => (7, lo, hi, 0),
            ExprNode::NatBig(i) => (8, i.0, 0, 0),
            ExprNode::Str(s) => (9, s.index() as u32, 0, 0),
            ExprNode::Proj(n, i, e) => (10, n.0, i, e.0),
            ExprNode::FVar(i) => (11, i, 0, 0),
        };
        hash2(tag | (a as u64) << 32, (b as u64) << 32 | c as u64)
    }

    #[inline]
    fn same(&self, o: &Self) -> bool {
        match (*self, *o) {
            (ExprNode::Lam(_, _, ty_a, body_a), ExprNode::Lam(_, _, ty_b, body_b))
            | (ExprNode::Pi(_, _, ty_a, body_a), ExprNode::Pi(_, _, ty_b, body_b)) => {
                ty_a == ty_b && body_a == body_b
            }
            (a, b) => a == b,
        }
    }
}

/// The data of the compound nodes from `from` on, from their children's
/// (see [`Exprs::finish_data`]).
#[inline(never)]
fn fill_data(
    data: &mut Slab<ExprData>,
    lets: &Interner<LetBinder>,
    nodes: &[ExprNode],
    from: usize,
) {
    data.fill_range(from, nodes.len(), |data, j| {
        compound_data(data, lets, nodes[j])
    });
}

/// The data of a compound node (else `None`), from its children's.
#[inline(always)]
fn compound_data(
    data: &Slab<ExprData>,
    lets: &Interner<LetBinder>,
    node: ExprNode,
) -> Option<ExprData> {
    let d = |e: ExprId| *data.get(e.0);
    Some(match node {
        ExprNode::App(f, a) => d(f).union(d(a)),
        ExprNode::Lam(_, _, t, b) | ExprNode::Pi(_, _, t, b) => d(t).union(d(b).under_binder()),
        ExprNode::Let(h, b) => {
            let h = lets.get(h.0);
            d(h.ty).union(d(h.value)).union(d(b).under_binder())
        }
        ExprNode::Proj(_, _, e) => d(e),
        _ => return None,
    })
}

/// Cached per-node data, packed in a `u32`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ExprData(u32);

impl ExprData {
    /// Largest loose bvar range that fits; Lean has the same bound.
    pub const MAX_RANGE: u32 = (1 << 20) - 1;
    const HAS_LEVEL_PARAM: u32 = 1 << 20;
    const HAS_FVAR: u32 = 1 << 21;
    /// Bit `USED_SHIFT + i` is set if `#i` may occur loose, for `i` below
    /// `USED_LOW`: exactly, except that `#(USED_LOW - 1)` counts as
    /// occurring under a binder whose body has a larger range.
    const USED_SHIFT: u32 = 22;
    pub(crate) const USED_LOW: u32 = 10;
    const USED: u32 = ((1 << Self::USED_LOW) - 1) << Self::USED_SHIFT;

    /// The data of a constant, sort or literal (`range` 0), or of the
    /// bound variable `#(range - 1)`.
    pub(crate) fn new(range: u32, has_level_param: bool) -> Self {
        let used = if range > 0 && range - 1 < Self::USED_LOW {
            1 << (Self::USED_SHIFT + range - 1)
        } else {
            0
        };
        ExprData(
            range
                | used
                | if has_level_param {
                    Self::HAS_LEVEL_PARAM
                } else {
                    0
                },
        )
    }

    pub(crate) fn from_bits(b: u32) -> Self {
        ExprData(b)
    }

    pub(crate) fn bits(self) -> u32 {
        self.0
    }

    /// The data of a free variable.
    pub(crate) const FVAR: ExprData = ExprData(Self::HAS_FVAR);

    /// One more than the largest loose bound variable index, or 0 if closed.
    pub fn loose_bvar_range(self) -> u32 {
        self.0 & Self::MAX_RANGE
    }

    pub fn has_level_param(self) -> bool {
        self.0 & Self::HAS_LEVEL_PARAM != 0
    }

    pub fn has_fvar(self) -> bool {
        self.0 & Self::HAS_FVAR != 0
    }

    pub fn has_loose_bvars(self) -> bool {
        self.loose_bvar_range() != 0
    }

    /// Whether `#i` may occur loose (if not, it surely does not).
    #[inline]
    pub fn may_use_bvar(self, i: u32) -> bool {
        i < self.loose_bvar_range()
            && (i >= Self::USED_LOW || self.0 & 1 << (Self::USED_SHIFT + i) != 0)
    }

    /// Bit `i` is set if `#i`, below the range and below `USED_LOW`, does
    /// not occur loose.
    pub fn unused_low(self) -> u32 {
        let n = self.loose_bvar_range().min(Self::USED_LOW);
        !(self.0 >> Self::USED_SHIFT) & ((1 << n) - 1)
    }

    pub(crate) fn union(self, other: ExprData) -> ExprData {
        let r = self.loose_bvar_range().max(other.loose_bvar_range());
        ExprData((self.0 | other.0) & !Self::MAX_RANGE | r)
    }

    /// Data of a binder body seen from outside the binder.
    pub(crate) fn under_binder(self) -> ExprData {
        let r0 = self.loose_bvar_range();
        let r = r0.saturating_sub(1);
        let mut used = (self.0 & Self::USED) >> 1 & Self::USED;
        if r0 > Self::USED_LOW {
            used |= 1 << (Self::USED_SHIFT + Self::USED_LOW - 1);
        }
        ExprData(self.0 & !Self::MAX_RANGE & !Self::USED | used | r)
    }
}

/// Why an expression could not be built.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprError {
    Overflow(Overflow),
    /// A de Bruijn index at or above `ExprData::MAX_RANGE`.
    BVarTooLarge(u64),
}

impl From<Overflow> for ExprError {
    fn from(o: Overflow) -> Self {
        ExprError::Overflow(o)
    }
}

/// A scoped thread's result, its panic resumed.
fn join_scoped<T>(h: std::thread::ScopedJoinHandle<'_, T>) -> T {
    h.join().unwrap_or_else(|e| std::panic::resume_unwind(e))
}

/// Applications grouped by the larger of their two child IDs.
struct AppIndex {
    /// Zero for an empty group, a tagged App ID for one member, or an offset
    /// into pairs. Slab IDs leave the high bit free.
    heads: Vec<u32>,
    /// Each group starts with [length, write cursor], followed by its pairs
    /// of [smaller child with orientation bit, App ID].
    pairs: Vec<[u32; 2]>,
    has_dynamic_apps: bool,
}

impl AppIndex {
    const SINGLE: u32 = 1 << 31;
    const SCAN: usize = 8;

    #[inline]
    fn key(fun: ExprId, arg: ExprId) -> usize {
        fun.0.max(arg.0) as usize
    }

    #[inline]
    fn other(fun: ExprId, arg: ExprId) -> u32 {
        if fun >= arg {
            arg.0
        } else {
            fun.0 | Self::SINGLE
        }
    }

    #[inline(never)]
    fn prepare(nodes: &[ExprNode]) -> Option<(Self, usize)> {
        let mut heads = vec![0; nodes.len()];
        let mut pairs_len = 1;
        let mut non_apps = 0;
        for (id, node) in (0u32..).zip(nodes) {
            if let ExprNode::App(fun, arg) = *node {
                let head = heads.get_mut(Self::key(fun, arg))?;
                if *head == 0 {
                    *head = Self::SINGLE | id;
                } else if *head >= Self::SINGLE {
                    *head = 2;
                    pairs_len += 3;
                } else {
                    *head += 1;
                    pairs_len += 1;
                }
            } else {
                non_apps += 1;
            }
        }
        if pairs_len > Self::SINGLE as usize
            || heads.len() * size_of::<u32>()
                + pairs_len * size_of::<[u32; 2]>()
                + IdTable::bytes_for_capacity(non_apps)
                > IdTable::bytes_for_capacity(nodes.len())
        {
            return None;
        }
        let mut pairs = vec![[0; 2]; pairs_len];
        let mut offset = 1;
        for head in &mut heads {
            let count = *head;
            if count != 0 && count < Self::SINGLE {
                pairs[offset] = [count, 1];
                *head = offset as u32;
                offset += 1 + count as usize;
            }
        }
        Some((
            Self {
                heads,
                pairs,
                has_dynamic_apps: false,
            },
            non_apps,
        ))
    }

    /// [`AppIndex::prepare`], the scatter and [`AppIndex::finish`] at
    /// once, on `parts` threads: the counts and the scatter split the
    /// nodes between them (with atomic counts and cursors), the layout and
    /// the checks split the keys. Each group is then sorted by ID, as the
    /// serial scatter leaves it, so it is the same index. `None` as
    /// `prepare` gives it.
    fn build(nodes: &[ExprNode], parts: usize) -> Option<Result<Self, (u32, u32)>> {
        let n = nodes.len();
        let parts = parts.max(1);
        let per_node = n.div_ceil(parts).max(1);
        let per_key = n.div_ceil(parts).max(1);
        let mut heads = vec![0u32; n];
        // The groups' sizes, and the other nodes; `None` for a bad key.
        let non_apps: Option<usize> = {
            let hs = atomic_u32(&mut heads);
            std::thread::scope(|s| {
                let handles: Vec<_> = nodes
                    .chunks(per_node)
                    .map(|chunk| {
                        s.spawn(move || {
                            let mut others = 0;
                            for node in chunk {
                                let ExprNode::App(fun, arg) = *node else {
                                    others += 1;
                                    continue;
                                };
                                hs.get(Self::key(fun, arg))?.fetch_add(1, Ordering::Relaxed);
                            }
                            Some(others)
                        })
                    })
                    .collect();
                handles.into_iter().map(join_scoped).sum()
            })
        };
        let non_apps = non_apps?;
        // Per key range, the pairs' words its groups take (headers
        // included).
        let words: Vec<usize> = std::thread::scope(|s| {
            let handles: Vec<_> = heads
                .chunks(per_key)
                .map(|hs| {
                    s.spawn(move || {
                        hs.iter()
                            .filter(|&&c| c >= 2)
                            .map(|&c| 1 + c as usize)
                            .sum::<usize>()
                    })
                })
                .collect();
            handles.into_iter().map(join_scoped).collect()
        });
        let pairs_len = 1 + words.iter().sum::<usize>();
        if pairs_len > Self::SINGLE as usize
            || heads.len() * size_of::<u32>()
                + pairs_len * size_of::<[u32; 2]>()
                + IdTable::bytes_for_capacity(non_apps)
                > IdTable::bytes_for_capacity(n)
        {
            return None;
        }
        let mut pairs = vec![[0u32; 2]; pairs_len];
        // The groups' places, in key order: a header [count, cursor] at
        // the group's offset, or `SINGLE` for a group of one.
        std::thread::scope(|s| {
            let mut rest = &mut pairs[1..];
            let mut base = 1;
            for (hs, &w) in heads.chunks_mut(per_key).zip(&words) {
                let (ps, tail) = std::mem::take(&mut rest).split_at_mut(w);
                rest = tail;
                s.spawn(move || {
                    let mut offset = 0;
                    for head in hs {
                        let count = *head;
                        if count == 1 {
                            *head = Self::SINGLE;
                        } else if count != 0 {
                            ps[offset] = [count, 1];
                            *head = (base + offset) as u32;
                            offset += 1 + count as usize;
                        }
                    }
                });
                base += w;
            }
        });
        {
            let hs = atomic_u32(&mut heads);
            let ps = atomic_u32(pairs.as_flattened_mut());
            std::thread::scope(|s| {
                for (c, chunk) in nodes.chunks(per_node).enumerate() {
                    s.spawn(move || {
                        for (id, node) in ((c * per_node) as u32..).zip(chunk) {
                            let ExprNode::App(fun, arg) = *node else {
                                continue;
                            };
                            let head = &hs[Self::key(fun, arg)];
                            let at = head.load(Ordering::Relaxed);
                            if at == Self::SINGLE {
                                head.store(Self::SINGLE | id, Ordering::Relaxed);
                            } else {
                                let at = at as usize;
                                let cursor =
                                    ps[2 * at + 1].fetch_add(1, Ordering::Relaxed) as usize;
                                ps[2 * (at + cursor)]
                                    .store(Self::other(fun, arg), Ordering::Relaxed);
                                ps[2 * (at + cursor) + 1].store(id, Ordering::Relaxed);
                            }
                        }
                    });
                }
            });
        }
        let res: Result<(), (u32, u32)> = std::thread::scope(|s| {
            let mut rest = &mut pairs[1..];
            let handles: Vec<_> = words
                .iter()
                .map(|&w| {
                    let (ps, tail) = std::mem::take(&mut rest).split_at_mut(w);
                    rest = tail;
                    s.spawn(move || {
                        let mut groups = &mut *ps;
                        while let Some((header, after)) = groups.split_first_mut() {
                            let (group, next) = after.split_at_mut(header[0] as usize);
                            if group.len() <= Self::SCAN {
                                group.sort_unstable_by_key(|pair| pair[1]);
                            }
                            groups = next;
                        }
                        Self::check_groups(ps)
                    })
                })
                .collect();
            handles.into_iter().try_for_each(join_scoped)
        });
        Some(res.map(|()| Self {
            heads,
            pairs,
            has_dynamic_apps: false,
        }))
    }

    /// Scatter an App during the scan that hashes the other expressions.
    #[inline]
    fn scatter_or_keep(&mut self, id: u32, node: ExprNode) -> bool {
        let ExprNode::App(fun, arg) = node else {
            return true;
        };
        let head = self.heads[Self::key(fun, arg)];
        if head < Self::SINGLE {
            let offset = head as usize;
            let cursor = self.pairs[offset][1] as usize;
            self.pairs[offset + cursor] = [Self::other(fun, arg), id];
            self.pairs[offset][1] += 1;
        }
        false
    }

    #[inline(never)]
    fn finish(&mut self) -> Result<(), (u32, u32)> {
        Self::check_groups(&mut self.pairs[1..])
    }

    /// Sort the groups laid out in `rest` (each a header, then its pairs)
    /// as lookups need; if two applications are equal, a pair of their
    /// ids.
    fn check_groups(mut rest: &mut [[u32; 2]]) -> Result<(), (u32, u32)> {
        while let Some((header, after)) = rest.split_first_mut() {
            let (group, next) = after.split_at_mut(header[0] as usize);
            if group.len() <= Self::SCAN {
                for (i, &[arg, id]) in group.iter().enumerate() {
                    if let Some(&[_, other]) = group[..i].iter().find(|pair| pair[0] == arg) {
                        return Err((id, other));
                    }
                }
            } else {
                group.sort_unstable_by_key(|pair| pair[0]);
                for chunk in group.windows(2) {
                    if chunk[0][0] == chunk[1][0] {
                        let [a, b] = [chunk[0][1], chunk[1][1]];
                        return Err((a.max(b), a.min(b)));
                    }
                }
            }
            rest = next;
        }
        Ok(())
    }

    #[inline]
    fn find(&self, nodes: &Slab<ExprNode>, fun: ExprId, arg: ExprId) -> Option<u32> {
        let head = *self.heads.get(Self::key(fun, arg))?;
        if head == 0 {
            return None;
        }
        if head >= Self::SINGLE {
            let id = head & !Self::SINGLE;
            return (*nodes.get(id) == ExprNode::App(fun, arg)).then_some(id);
        }
        let offset = head as usize;
        let count = self.pairs[offset][0] as usize;
        let group = &self.pairs[offset + 1..][..count];
        let other = Self::other(fun, arg);
        if count <= Self::SCAN {
            group
                .iter()
                .find(|pair| pair[0] == other)
                .map(|pair| pair[1])
        } else {
            let at = group.binary_search_by_key(&other, |pair| pair[0]).ok()?;
            Some(group[at][1])
        }
    }

    fn heap_bytes(&self) -> usize {
        self.heads.capacity() * size_of::<u32>() + self.pairs.capacity() * size_of::<[u32; 2]>()
    }
}

pub struct Exprs {
    arena: Big<ExprNode>,
    app_index: Option<AppIndex>,
    data: Slab<ExprData>,
    /// Lends the checker's stores blocks of ids above the nodes, for their
    /// own terms (see `crate::slab`); shared with the views of the arena
    /// (see [`Exprs::view`]).
    pool: std::sync::Arc<Pool>,
    /// Compound nodes appended without hash-consing ([`Exprs::append`])
    /// get their data at [`Exprs::index`]. Until then the data stops
    /// short of them, or (where a node with data came after them) holds
    /// placeholders: this is the first of those (`u32::MAX`: none). See
    /// [`Exprs::data_start`].
    data_from: u32,
    lets: Interner<LetBinder>,
    bigs: Vec<BigUint>,
    big_table: hashbrown::HashTable<u32>,
}

impl Default for Exprs {
    fn default() -> Self {
        Self::new()
    }
}

pub(crate) fn big_hash(n: &BigUint) -> u64 {
    hash_bytes(&n.to_bytes_le())
}

impl Exprs {
    pub fn new() -> Self {
        Exprs {
            arena: Big::new("too many expressions"),
            app_index: None,
            data: Slab::new(),
            pool: Default::default(),
            data_from: u32::MAX,
            lets: Interner::new("too many let binders"),
            bigs: Vec::new(),
            big_table: hashbrown::HashTable::new(),
        }
    }

    /// An arena made of the parts the `.olean` loader builds: nodes in id
    /// order, the table indexing them (see [`Big::from_parts`]), each node's
    /// data, the let binders and the big literals.
    pub(crate) fn from_parts(
        nodes: Slab<ExprNode>,
        table: IdTable,
        data: Slab<ExprData>,
        lets: Interner<LetBinder>,
        bigs: Vec<BigUint>,
    ) -> Self {
        assert_eq!(nodes.len(), data.len());
        let mut big_table = hashbrown::HashTable::new();
        for (i, b) in bigs.iter().enumerate() {
            big_table.insert_unique(big_hash(b), i as u32, |&id| big_hash(&bigs[id as usize]));
        }
        Exprs {
            arena: Big::from_parts(nodes, table, "too many expressions"),
            app_index: None,
            data,
            pool: Default::default(),
            data_from: u32::MAX,
            lets,
            bigs,
            big_table,
        }
    }

    pub fn len(&self) -> usize {
        self.arena.len()
    }

    pub fn is_empty(&self) -> bool {
        self.arena.is_empty()
    }

    /// Make room for `extra` more nodes.
    pub fn reserve(&mut self, extra: usize) {
        self.arena.reserve(extra);
    }

    pub fn let_count(&self) -> usize {
        self.lets.len()
    }

    pub fn big_count(&self) -> usize {
        self.bigs.len()
    }

    #[inline]
    pub fn get(&self, e: ExprId) -> ExprNode {
        *self.arena.get(e.0)
    }

    #[inline]
    pub fn data(&self, e: ExprId) -> ExprData {
        debug_assert!(e.0 < self.data_start(), "data not set yet");
        *self.data.get(e.0)
    }

    pub fn let_binder(&self, l: LetId) -> LetBinder {
        *self.lets.get(l.0)
    }

    pub fn big(&self, b: BigId) -> &BigUint {
        &self.bigs[b.0 as usize]
    }

    /// Reads any expression's node: the environment's, or one of a
    /// store's own (see `crate::slab`).
    pub(crate) fn node_reader(&self) -> Reader<'_, ExprNode> {
        self.arena.nodes().reader()
    }

    /// Likewise for the data.
    pub(crate) fn data_reader(&self) -> Reader<'_, ExprData> {
        self.data.reader()
    }

    /// A block of ids above the arena's, for a store's own expressions.
    pub(crate) fn take_block(&self) -> Option<Block<'_, ExprNode, ExprData>> {
        self.pool.take(self.arena.nodes(), &self.data)
    }

    /// Intern a node. Its children must already be interned here, and its
    /// levels in `levels`.
    pub fn intern(&mut self, node: ExprNode, levels: &Levels) -> Result<(ExprId, bool), ExprError> {
        self.add(node, levels, false)
    }

    /// Add a node without hash-consing it: lookups do not see it until
    /// [`Exprs::index`]. For a reader that knows its input lists each
    /// term once (and checks that when indexing).
    pub fn append(&mut self, node: ExprNode, levels: &Levels) -> Result<ExprId, ExprError> {
        Ok(self.add(node, levels, true)?.0)
    }

    /// [`Exprs::append`] for an application, binder, `let` or projection
    /// (the nodes that need no levels).
    #[inline]
    pub(crate) fn append_compound(&mut self, node: ExprNode) -> Result<ExprId, ExprError> {
        debug_assert!(matches!(
            node,
            ExprNode::App(..)
                | ExprNode::Lam(..)
                | ExprNode::Pi(..)
                | ExprNode::Let(..)
                | ExprNode::Proj(..)
        ));
        // Its data is set at `index`, from the children's (until then,
        // the data stops short of it: see `data_from`).
        Ok(ExprId(self.arena.push_unindexed(node)?))
    }

    fn compound(&self, node: ExprNode) -> bool {
        matches!(
            node,
            ExprNode::App(..)
                | ExprNode::Lam(..)
                | ExprNode::Pi(..)
                | ExprNode::Let(..)
                | ExprNode::Proj(..)
        )
    }

    /// The first node whose data may not be set yet.
    #[inline]
    fn data_start(&self) -> u32 {
        self.data_from.min(self.data.len() as u32)
    }

    /// Set the data [`Exprs::append`] left for later. Children come
    /// before their parents, so one pass in order does it (and, with
    /// little else in the loop, the processor can wait on several
    /// children's data at once).
    pub(crate) fn finish_data(&mut self) {
        let from = self.data_start() as usize;
        if from >= self.arena.len() {
            return;
        }
        self.data.fill_to(self.arena.len(), ExprData(0));
        fill_data(
            &mut self.data,
            &self.lets,
            self.arena.nodes().as_slice(),
            from,
        );
        self.data_from = u32::MAX;
    }

    /// Index every node, on `threads` threads; if two are equal, a pair
    /// of their ids (the later, the earlier).
    pub fn index(&mut self, threads: usize) -> Result<(), (ExprId, ExprId)> {
        if threads > 1 && self.arena.len() >= 1 << 16 {
            if self.index_apps_alongside(threads)? {
                return Ok(());
            }
        } else {
            self.finish_data();
            if threads == 1 && self.arena.len() >= 1 << 16 && self.index_apps()? {
                return Ok(());
            }
        }
        self.finish_data();
        self.arena
            .index(threads)
            .map_err(|(a, b)| (ExprId(a), ExprId(b)))?;
        self.app_index = None;
        Ok(())
    }

    /// [`Exprs::index_apps`] with [`Exprs::finish_data`], on `threads`
    /// threads (one being the names' in the reader): the data on one, the
    /// other expressions' table on one, and the applications' groups on
    /// the rest. The data are set even if it gives false.
    fn index_apps_alongside(&mut self, threads: usize) -> Result<bool, (ExprId, ExprId)> {
        let from = self.data_start() as usize;
        let len = self.arena.len();
        if from < len {
            self.data.fill_to(len, ExprData(0));
        }
        let (arena, data, lets) = (&self.arena, &mut self.data, &self.lets);
        let nodes = arena.nodes();
        let errors = |(a, b)| (ExprId(a), ExprId(b));
        let res: Result<_, (ExprId, ExprId)> = std::thread::scope(|s| {
            if from < len {
                s.spawn(move || fill_data(data, lets, nodes.as_slice(), from));
            }
            let table = s.spawn(move || {
                let is_app = |node: &ExprNode| matches!(node, ExprNode::App(..));
                let non_apps = nodes.as_slice().iter().filter(|n| !is_app(n)).count();
                arena.build_index_here(non_apps, |_, node| !is_app(node))
            });
            let apps = AppIndex::build(nodes.as_slice(), threads.saturating_sub(3).max(1));
            let table = table
                .join()
                .unwrap_or_else(|e| std::panic::resume_unwind(e));
            let Some(apps) = apps else {
                return Ok(None);
            };
            Ok(Some((table.map_err(errors)?, apps.map_err(errors)?)))
        });
        self.data_from = u32::MAX;
        let Some((table, apps)) = res? else {
            return Ok(false);
        };
        self.arena.replace_index(table);
        self.app_index = Some(apps);
        Ok(true)
    }

    fn index_apps(&mut self) -> Result<bool, (ExprId, ExprId)> {
        let Some((mut apps, non_apps)) = AppIndex::prepare(self.arena.nodes().as_slice()) else {
            return Ok(false);
        };
        let errors = |(a, b)| (ExprId(a), ExprId(b));
        let table = self
            .arena
            .build_index_here(non_apps, |id, node| apps.scatter_or_keep(id, *node))
            .map_err(errors)?;
        apps.finish().map_err(errors)?;
        self.arena.replace_index(table);
        self.app_index = Some(apps);
        Ok(true)
    }

    fn add(
        &mut self,
        node: ExprNode,
        levels: &Levels,
        unindexed: bool,
    ) -> Result<(ExprId, bool), ExprError> {
        if let ExprNode::BVar(i) = node
            && i >= ExprData::MAX_RANGE
        {
            return Err(ExprError::BVarTooLarge(i as u64));
        }
        let (id, fresh) = if unindexed {
            (self.arena.push_unindexed(node)?, true)
        } else if let ExprNode::App(fun, arg) = node
            && let Some(apps) = &mut self.app_index
        {
            if let Some(id) = apps.find(self.arena.nodes(), fun, arg) {
                return Ok((ExprId(id), false));
            }
            let added = self.arena.intern(node)?;
            apps.has_dynamic_apps |= added.1;
            added
        } else {
            self.arena.intern(node)?
        };
        if fresh && unindexed && self.compound(node) {
            // Set at `index` (see `append_compound`).
            self.data_from = self.data_from.min(id);
        } else if fresh {
            let d = match node {
                ExprNode::BVar(i) => ExprData::new(i + 1, false),
                ExprNode::Sort(l) => ExprData::new(0, levels.has_param(l)),
                ExprNode::Const(_, ls) => ExprData::new(0, levels.list_has_param(ls)),
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
            };
            // Placeholders for the compound nodes before it.
            if self.data.len() < id as usize {
                self.data_from = self.data_from.min(self.data.len() as u32);
            }
            self.data.fill_to(id as usize, ExprData(0));
            self.data.push(d);
        }
        Ok((ExprId(id), fresh))
    }

    /// Whether the nodes and their data are in memory that never moves
    /// (see [`Exprs::view`]).
    pub(crate) fn is_fixed(&self) -> bool {
        self.arena.is_fixed() && self.data.is_fixed()
    }

    /// The nodes so far, with their data (set now), the let binders and
    /// big literals, unindexed: for checkers on other threads while this
    /// arena goes on growing (see [`crate::slab::Slab::alias`]). Their
    /// stores take blocks of ids from this arena's pool, which lends none
    /// below `above` from now on: `above` must be more ids than the arena
    /// will ever hold.
    pub(crate) fn view(&mut self, above: usize) -> Exprs {
        self.finish_data();
        let len = self.arena.len();
        self.pool.lend_above(above);
        Exprs {
            arena: self.arena.view(len, IdTable::default()),
            app_index: None,
            data: self.data.alias(len),
            pool: self.pool.clone(),
            data_from: u32::MAX,
            lets: self.lets.clone(),
            bigs: self.bigs.clone(),
            big_table: self.big_table.clone(),
        }
    }

    /// The id of `node`, if it is interned here.
    #[inline]
    pub(crate) fn find(&self, node: &ExprNode) -> Option<ExprId> {
        if let ExprNode::App(fun, arg) = *node
            && let Some(apps) = &self.app_index
        {
            let found = apps.find(self.arena.nodes(), fun, arg);
            if found.is_some() || !apps.has_dynamic_apps {
                return found.map(ExprId);
            }
        }
        self.arena.find(node).map(ExprId)
    }

    pub(crate) fn find_let(&self, b: &LetBinder) -> Option<LetId> {
        self.lets.find(b).map(LetId)
    }

    /// The id of the big literal `n`, if it is interned here.
    pub(crate) fn find_big(&self, n: &BigUint) -> Option<BigId> {
        let h = big_hash(n);
        self.big_table
            .find(h, |&id| self.bigs[id as usize] == *n)
            .map(|&id| BigId(id))
    }

    pub fn intern_let(&mut self, b: LetBinder) -> Result<LetId, Overflow> {
        Ok(LetId(self.lets.intern(b)?.0))
    }

    /// The literal node for `n`: inline if below 2^64, else pooled.
    pub fn nat_node(&mut self, n: BigUint) -> Result<ExprNode, Overflow> {
        if let Ok(v) = u64::try_from(&n) {
            return Ok(ExprNode::NatSmall(v as u32, (v >> 32) as u32));
        }
        let h = big_hash(&n);
        let Self {
            bigs, big_table, ..
        } = self;
        if let Some(&id) = big_table.find(h, |&id| bigs[id as usize] == n) {
            return Ok(ExprNode::NatBig(BigId(id)));
        }
        if bigs.len() >= u32::MAX as usize {
            return Err(Overflow("too many big literals"));
        }
        let id = bigs.len() as u32;
        bigs.push(n);
        let bigs = &*bigs;
        big_table.insert_unique(h, id, |&id| big_hash(&bigs[id as usize]));
        Ok(ExprNode::NatBig(BigId(id)))
    }

    pub fn nat_small_value(lo: u32, hi: u32) -> u64 {
        (hi as u64) << 32 | lo as u64
    }

    pub fn heap_bytes(&self) -> usize {
        self.arena.heap_bytes()
            + self.app_index.as_ref().map_or(0, AppIndex::heap_bytes)
            + self.data.heap_bytes()
            + self.lets.heap_bytes()
            + self.bigs.capacity() * size_of::<BigUint>()
            + self
                .bigs
                .iter()
                .map(|b| b.bits().div_ceil(8) as usize)
                .sum::<usize>()
            + self.big_table.capacity() * 5
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn node_is_16_bytes() {
        assert_eq!(size_of::<ExprNode>(), 16);
    }

    #[test]
    fn sharing_and_data() {
        let levels = Levels::new();
        let mut es = Exprs::new();
        let (bvar0, _) = es.intern(ExprNode::BVar(0), &levels).unwrap();
        let (bvar1, _) = es.intern(ExprNode::BVar(1), &levels).unwrap();
        let (ty, _) = es.intern(ExprNode::Sort(LevelId::ZERO), &levels).unwrap();
        let (app, _) = es.intern(ExprNode::App(bvar1, bvar0), &levels).unwrap();
        let (app2, fresh) = es.intern(ExprNode::App(bvar1, bvar0), &levels).unwrap();
        assert_eq!(app, app2);
        assert!(!fresh);
        assert_eq!(es.data(app).loose_bvar_range(), 2);
        let lam = ExprNode::Lam(BinderInfo::Default, NameId::ANON, ty, app);
        let (lam, _) = es.intern(lam, &levels).unwrap();
        assert_eq!(es.data(lam).loose_bvar_range(), 1);
        let pi = ExprNode::Pi(BinderInfo::Implicit, NameId::ANON, ty, app);
        let (pi, _) = es.intern(pi, &levels).unwrap();
        assert_ne!(lam, pi);
        assert!(matches!(
            es.intern(ExprNode::BVar(ExprData::MAX_RANGE), &levels),
            Err(ExprError::BVarTooLarge(_))
        ));
    }

    #[test]
    fn application_groups_distinguish_orientation_and_detect_duplicates() {
        let levels = Levels::new();
        let mut es = Exprs::new();
        let f = es.intern(ExprNode::BVar(0), &levels).unwrap().0;
        let a = es.intern(ExprNode::BVar(1), &levels).unwrap().0;
        let b = es.intern(ExprNode::BVar(2), &levels).unwrap().0;
        let forward = ExprNode::App(f, a);
        let reverse = ExprNode::App(a, f);
        let single = ExprNode::App(a, b);
        let first = es.append(forward, &levels).unwrap();
        let second = es.append(reverse, &levels).unwrap();
        let mut last = es.append(single, &levels).unwrap();
        let single_id = last;
        for _ in 0..64 {
            last = es.append(ExprNode::App(last, f), &levels).unwrap();
        }
        let mut large_group = Vec::new();
        for id in 0..10 {
            let app = ExprNode::App(last, ExprId(id));
            large_group.push((app, es.append(app, &levels).unwrap()));
        }
        es.finish_data();
        assert!(es.index_apps().unwrap());
        assert_eq!(es.find(&forward), Some(first));
        assert_eq!(es.find(&reverse), Some(second));
        assert_eq!(es.find(&single), Some(single_id));
        assert_eq!(es.intern(single, &levels).unwrap(), (single_id, false));
        for (app, id) in large_group {
            assert_eq!(es.find(&app), Some(id));
        }
        let fresh = ExprNode::App(f, b);
        assert_eq!(es.find(&fresh), None);
        let (new, added) = es.intern(fresh, &levels).unwrap();
        assert!(added);
        assert_eq!(es.find(&fresh), Some(new));
        let duplicate = es.append(reverse, &levels).unwrap();
        assert_eq!(es.index_apps(), Err((duplicate, second)));
    }

    #[test]
    fn parallel_application_groups_match_the_serial_ones() {
        let mut nodes: Vec<ExprNode> = (0..64).map(ExprNode::BVar).collect();
        let mut seen = std::collections::HashSet::new();
        let mut x = 12345u64;
        while nodes.len() < 50_000 {
            x = x
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let n = nodes.len() as u64;
            // Most applications take the last node (groups of one), some
            // a recent one (larger groups).
            let back = if x.is_multiple_of(10) {
                (x >> 13) % 64
            } else {
                0
            };
            let (a, b) = ((x >> 33) % n, n - 1 - back);
            let (fun, arg) = if x & 1 == 0 { (a, b) } else { (b, a) };
            if seen.insert((fun, arg)) {
                nodes.push(ExprNode::App(ExprId(fun as u32), ExprId(arg as u32)));
            }
            if nodes.len().is_multiple_of(10_000) {
                // A group to sort.
                for i in 0..200 {
                    if seen.insert((i, 30_000)) {
                        nodes.push(ExprNode::App(ExprId(i as u32), ExprId(30_000)));
                    }
                }
            }
        }
        let large = nodes
            .iter()
            .filter(|n| matches!(n, ExprNode::App(_, ExprId(30_000))));
        assert!(large.count() > AppIndex::SCAN);
        let serial = |nodes: &[ExprNode]| {
            let (mut apps, _) = AppIndex::prepare(nodes).unwrap();
            for (id, node) in (0u32..).zip(nodes) {
                apps.scatter_or_keep(id, *node);
            }
            apps.finish().map(|()| apps)
        };
        let want = serial(&nodes).unwrap();
        for parts in [1, 3, 8] {
            let got = AppIndex::build(&nodes, parts).unwrap().unwrap();
            assert_eq!(got.heads, want.heads);
            assert_eq!(got.pairs, want.pairs);
        }
        let ExprNode::App(fun, arg) = nodes[40_000] else {
            unreachable!()
        };
        nodes.push(ExprNode::App(fun, arg));
        assert!(serial(&nodes).is_err());
        assert!(AppIndex::build(&nodes, 3).unwrap().is_err());
    }

    #[test]
    fn used_bound_variables() {
        let levels = Levels::new();
        let mut es = Exprs::new();
        let bv = |es: &mut Exprs, i| es.intern(ExprNode::BVar(i), &levels).unwrap().0;
        let (b0, b2, b12) = (bv(&mut es, 0), bv(&mut es, 2), bv(&mut es, 12));
        let (ty, _) = es.intern(ExprNode::Sort(LevelId::ZERO), &levels).unwrap();
        let (app, _) = es.intern(ExprNode::App(b2, b0), &levels).unwrap();
        let d = es.data(app);
        assert!(d.may_use_bvar(0) && !d.may_use_bvar(1) && d.may_use_bvar(2));
        assert!(!d.may_use_bvar(3));
        // Under a binder #2 becomes #1, and #0 is bound.
        let lam = ExprNode::Lam(BinderInfo::Default, NameId::ANON, ty, app);
        let (lam, _) = es.intern(lam, &levels).unwrap();
        let d = es.data(lam);
        assert!(!d.may_use_bvar(0) && d.may_use_bvar(1) && !d.may_use_bvar(2));
        // Past the exact bits, an occurrence is assumed.
        let (wide, _) = es.intern(ExprNode::App(b12, b0), &levels).unwrap();
        let pi = ExprNode::Pi(BinderInfo::Default, NameId::ANON, ty, wide);
        let (pi, _) = es.intern(pi, &levels).unwrap();
        let d = es.data(pi);
        assert!(!d.may_use_bvar(0) && d.may_use_bvar(9) && d.may_use_bvar(11));
        assert!(!d.may_use_bvar(12));
    }

    #[test]
    fn nat_literals_are_canonical() {
        let mut es = Exprs::new();
        let small = es.nat_node(BigUint::from(u64::MAX)).unwrap();
        assert_eq!(small, ExprNode::NatSmall(u32::MAX, u32::MAX));
        let big = BigUint::from(u64::MAX) + 1u32;
        let a = es.nat_node(big.clone()).unwrap();
        let b = es.nat_node(big.clone()).unwrap();
        assert_eq!(a, b);
        let ExprNode::NatBig(i) = a else { panic!() };
        assert_eq!(es.big(i), &big);
        assert_eq!(es.big_count(), 1);
    }
}
