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
use crate::intern::{Big, CHUNK, Chunked, IdTable, Interner, Node};
use crate::level::{LevelId, LevelList, Levels};
use crate::name::NameId;
use crate::strings::{Overflow, StrId};

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

/// The data of a compound node (else `None`), from its children's.
#[inline]
fn compound_data(
    data: &Chunked<ExprData>,
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
    const USED_LOW: u32 = 10;
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

pub struct Exprs {
    arena: Big<ExprNode>,
    data: Chunked<ExprData>,
    /// Compound nodes appended without hash-consing ([`Exprs::append`])
    /// get their data at [`Exprs::index`]: from this id on, theirs is not
    /// set yet (`u32::MAX`: all is).
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
            data: Chunked::default(),
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
        nodes: Chunked<ExprNode>,
        table: IdTable,
        data: Chunked<ExprData>,
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
            data,
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
        self.data.reserve(extra);
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
        debug_assert!(e.0 < self.data_from, "data not set yet");
        *self.data.get(e.0)
    }

    pub fn let_binder(&self, l: LetId) -> LetBinder {
        *self.lets.get(l.0)
    }

    pub fn big(&self, b: BigId) -> &BigUint {
        &self.bigs[b.0 as usize]
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
        let id = self.arena.push_unindexed(node)?;
        // Set at `index`, from the children's (until then, the data
        // stops short of it, or holds a placeholder).
        self.data_from = self.data_from.min(id);
        Ok(ExprId(id))
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

    /// Set the data [`Exprs::append`] left for later. Children come
    /// before their parents, so one pass in order does it (and, with
    /// little else in the loop, the processor can wait on several
    /// children's data at once).
    fn finish_data(&mut self) {
        let from = self.data_from as usize;
        if from == u32::MAX as usize {
            return;
        }
        self.data.fill_to(self.arena.len(), ExprData(0));
        let (lets, data) = (&self.lets, &mut self.data);
        for (c, chunk) in self.arena.nodes().chunks().iter().enumerate() {
            let start = c * CHUNK;
            let skip = from.saturating_sub(start).min(chunk.len());
            for (j, &node) in chunk.iter().enumerate().skip(skip) {
                if let Some(d) = compound_data(data, lets, node) {
                    data.chunks_mut()[c][j] = d;
                }
            }
        }
        self.data_from = u32::MAX;
    }

    /// Index every node, on `threads` threads; if two are equal, a pair
    /// of their ids (the later, the earlier).
    pub fn index(&mut self, threads: usize) -> Result<(), (ExprId, ExprId)> {
        self.finish_data();
        self.arena
            .index(threads)
            .map_err(|(a, b)| (ExprId(a), ExprId(b)))
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
            self.data.fill_to(id as usize, ExprData(0));
            self.data.push(d);
        }
        Ok((ExprId(id), fresh))
    }

    /// The id of `node`, if it is interned here.
    #[inline]
    pub(crate) fn find(&self, node: &ExprNode) -> Option<ExprId> {
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
