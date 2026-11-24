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
use crate::intern::{Interner, Node};
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
pub struct LetId(u32);

/// Id of an interned big natural literal (at least 2^64).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BigId(u32);

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
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct LetBinder {
    pub name: NameId,
    pub ty: ExprId,
    pub value: ExprId,
    pub nondep: bool,
}

impl Node for LetBinder {
    fn hash(&self) -> u64 {
        hash2(
            (self.name.0 as u64) << 1 | self.nondep as u64,
            (self.ty.0 as u64) << 32 | self.value.0 as u64,
        )
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
            ExprNode::Lam(bi, n, t, b) => (4 | (bi as u64) << 4, n.0, t.0, b.0),
            ExprNode::Pi(bi, n, t, b) => (5 | (bi as u64) << 4, n.0, t.0, b.0),
            ExprNode::Let(h, b) => (6, h.0, b.0, 0),
            ExprNode::NatSmall(lo, hi) => (7, lo, hi, 0),
            ExprNode::NatBig(i) => (8, i.0, 0, 0),
            ExprNode::Str(s) => (9, s.index() as u32, 0, 0),
            ExprNode::Proj(n, i, e) => (10, n.0, i, e.0),
        };
        hash2(tag | (a as u64) << 32, (b as u64) << 32 | c as u64)
    }
}

/// Cached per-node data, packed in a `u32`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ExprData(u32);

impl ExprData {
    /// Largest loose bvar range that fits; Lean has the same bound.
    pub const MAX_RANGE: u32 = (1 << 20) - 1;
    const HAS_LEVEL_PARAM: u32 = 1 << 20;

    fn new(range: u32, has_level_param: bool) -> Self {
        ExprData(
            range
                | if has_level_param {
                    Self::HAS_LEVEL_PARAM
                } else {
                    0
                },
        )
    }

    /// One more than the largest loose bound variable index, or 0 if closed.
    pub fn loose_bvar_range(self) -> u32 {
        self.0 & Self::MAX_RANGE
    }

    pub fn has_level_param(self) -> bool {
        self.0 & Self::HAS_LEVEL_PARAM != 0
    }

    fn union(self, other: ExprData) -> ExprData {
        let r = self.loose_bvar_range().max(other.loose_bvar_range());
        ExprData::new(r, self.has_level_param() || other.has_level_param())
    }

    /// Data of a binder body seen from outside the binder.
    fn under_binder(self) -> ExprData {
        ExprData::new(
            self.loose_bvar_range().saturating_sub(1),
            self.has_level_param(),
        )
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
    arena: Interner<ExprNode>,
    data: Vec<ExprData>,
    lets: Interner<LetBinder>,
    bigs: Vec<BigUint>,
    big_table: hashbrown::HashTable<u32>,
}

impl Default for Exprs {
    fn default() -> Self {
        Self::new()
    }
}

fn big_hash(n: &BigUint) -> u64 {
    hash_bytes(&n.to_bytes_le())
}

impl Exprs {
    pub fn new() -> Self {
        Exprs {
            arena: Interner::new("too many expressions"),
            data: Vec::new(),
            lets: Interner::new("too many let binders"),
            bigs: Vec::new(),
            big_table: hashbrown::HashTable::new(),
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
        self.data[e.index()]
    }

    pub fn let_binder(&self, l: LetId) -> LetBinder {
        *self.lets.get(l.0)
    }

    pub fn big(&self, b: BigId) -> &BigUint {
        &self.bigs[b.0 as usize]
    }

    /// Iterate over all nodes in id order.
    pub fn nodes(&self) -> &[ExprNode] {
        self.arena.nodes()
    }

    /// Intern a node. Its children must already be interned here, and its
    /// levels in `levels`.
    pub fn intern(&mut self, node: ExprNode, levels: &Levels) -> Result<(ExprId, bool), ExprError> {
        if let ExprNode::BVar(i) = node
            && i >= ExprData::MAX_RANGE
        {
            return Err(ExprError::BVarTooLarge(i as u64));
        }
        let (id, fresh) = self.arena.intern(node)?;
        if fresh {
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
            };
            self.data.push(d);
        }
        Ok((ExprId(id), fresh))
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
            + self.data.capacity() * 4
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
        let (b0, _) = es.intern(ExprNode::BVar(0), &levels).unwrap();
        let (b1, _) = es.intern(ExprNode::BVar(1), &levels).unwrap();
        let (ty, _) = es.intern(ExprNode::Sort(LevelId::ZERO), &levels).unwrap();
        let (app, _) = es.intern(ExprNode::App(b1, b0), &levels).unwrap();
        let (app2, fresh) = es.intern(ExprNode::App(b1, b0), &levels).unwrap();
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
