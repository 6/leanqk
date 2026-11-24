//! Concurrent hash-consing arenas, used while loading `.olean` files.
//!
//! Worker threads intern modules into these arenas at the same time; at the
//! end [`Par::finish`] turns them into the environment's [`Names`],
//! [`Levels`] and [`Exprs`], handing over the expression shard tables as
//! they are (no rehashing).
//!
//! Each arena is a set of shard tables (each behind its own mutex, chosen
//! by [`shard_of`]) of `u32` ids, and a store from id to node, written once
//! before the id is published in a table. Ids come from one atomic counter
//! while the shard is locked, so a node's id is greater than its
//! children's, as in the sequential arenas. Node equality is [`Node::same`],
//! and the hash is [`Node::hash`], so the tables are exactly the ones the
//! sequential arena would have, up to the order of ids.

use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};

use hashbrown::HashTable;
use num_bigint::BigUint;

use crate::expr::{BigId, ExprData, ExprId, ExprNode, Exprs, LetBinder, LetId};
use crate::hash::hash_bytes;
use crate::intern::{Interner, Node, SHARDS, shard_of};
use crate::level::{LevelId, LevelList, LevelNode, Levels};
use crate::name::{NameId, NameNode, Names};
use crate::strings::{Overflow, StrId, StrPool};

const CHUNK_BITS: u32 = 16;
const CHUNK: usize = 1 << CHUNK_BITS;
const MAX_CHUNKS: usize = 1 << (32 - CHUNK_BITS);

/// Write-once storage of `W` words per id, in lazily allocated chunks of
/// `2^B` ids. The expression store uses chunks above the allocator's mmap
/// threshold, so that each is returned to the system when freed.
struct Words<const W: usize, const B: u32> {
    chunks: Vec<OnceLock<Box<[AtomicU64]>>>,
    /// Ids per chunk: `2^B`, or fewer if all ids fit in one chunk.
    per: usize,
}

impl<const W: usize, const B: u32> Words<W, B> {
    /// Storage for ids below `max`.
    fn new(max: usize) -> Self {
        let n = (max >> B) + 1;
        Words {
            chunks: (0..n.min(1 << (32 - B))).map(|_| OnceLock::new()).collect(),
            per: max.min(1 << B).max(1),
        }
    }

    fn chunk(&self, id: u32) -> &[AtomicU64] {
        self.chunks[(id >> B) as usize]
            .get_or_init(|| (0..W * self.per).map(|_| AtomicU64::new(0)).collect())
    }

    #[inline]
    fn set(&self, id: u32, w: [u64; W]) {
        let c = self.chunk(id);
        let o = (id as usize & ((1 << B) - 1)) * W;
        for (i, x) in w.into_iter().enumerate() {
            c[o + i].store(x, Ordering::Relaxed);
        }
    }

    #[inline]
    fn get(&self, id: u32) -> [u64; W] {
        let c = self.chunk(id);
        let o = (id as usize & ((1 << B) - 1)) * W;
        std::array::from_fn(|i| c[o + i].load(Ordering::Relaxed))
    }
}

/// Write-once storage of values per id.
struct Cells<T> {
    chunks: Vec<OnceLock<Box<[OnceLock<T>]>>>,
}

impl<T> Cells<T> {
    /// Storage for ids below `max`.
    fn new(max: usize) -> Self {
        let n = (max >> CHUNK_BITS) + 1;
        Cells {
            chunks: (0..n.min(MAX_CHUNKS)).map(|_| OnceLock::new()).collect(),
        }
    }

    fn cell(&self, id: u32) -> &OnceLock<T> {
        let c = self.chunks[(id >> CHUNK_BITS) as usize]
            .get_or_init(|| (0..CHUNK).map(|_| OnceLock::new()).collect());
        &c[id as usize & (CHUNK - 1)]
    }

    fn set(&self, id: u32, v: T) {
        let _ = self.cell(id).set(v);
    }

    fn get(&self, id: u32) -> &T {
        self.cell(id).get().expect("published before use")
    }
}

/// A node that packs into two words, plus a word of side data.
pub(crate) trait Pack: Node {
    fn pack(&self) -> [u64; 2];
    fn unpack(w: [u64; 2]) -> Self;
}

fn lo(x: u64) -> u32 {
    x as u32
}

fn hi(x: u64) -> u32 {
    (x >> 32) as u32
}

impl Pack for ExprNode {
    fn pack(&self) -> [u64; 2] {
        let b = |tag: u64, x: u32| tag | (x as u64) << 8;
        let two = |a: u32, c: u32| a as u64 | (c as u64) << 32;
        match *self {
            ExprNode::BVar(i) => [b(0, i), 0],
            ExprNode::Sort(l) => [b(1, l.0), 0],
            ExprNode::Const(n, ls) => [b(2, n.0), ls.0 as u64],
            ExprNode::App(f, a) => [3, two(f.0, a.0)],
            ExprNode::Lam(bi, n, t, x) => {
                [4 | (bi as u64) << 8 | (n.0 as u64) << 16, two(t.0, x.0)]
            }
            ExprNode::Pi(bi, n, t, x) => [5 | (bi as u64) << 8 | (n.0 as u64) << 16, two(t.0, x.0)],
            ExprNode::Let(l, x) => [b(6, l.0), x.0 as u64],
            ExprNode::NatSmall(l, h) => [7, two(l, h)],
            ExprNode::NatBig(i) => [b(8, i.0), 0],
            ExprNode::Str(s) => [b(9, s.0), 0],
            ExprNode::Proj(n, i, e) => [b(10, n.0), two(i, e.0)],
            ExprNode::FVar(i) => [b(11, i), 0],
        }
    }

    fn unpack(w: [u64; 2]) -> Self {
        use crate::expr::BinderInfo as B;
        let a = (w[0] >> 8) as u32;
        let bi = |x: u64| match (x >> 8) as u8 {
            0 => B::Default,
            1 => B::Implicit,
            2 => B::StrictImplicit,
            _ => B::InstImplicit,
        };
        let binder_name = NameId((w[0] >> 16) as u32);
        match w[0] as u8 {
            0 => ExprNode::BVar(a),
            1 => ExprNode::Sort(LevelId(a)),
            2 => ExprNode::Const(NameId(a), LevelList(w[1] as u32)),
            3 => ExprNode::App(ExprId(lo(w[1])), ExprId(hi(w[1]))),
            4 => ExprNode::Lam(bi(w[0]), binder_name, ExprId(lo(w[1])), ExprId(hi(w[1]))),
            5 => ExprNode::Pi(bi(w[0]), binder_name, ExprId(lo(w[1])), ExprId(hi(w[1]))),
            6 => ExprNode::Let(LetId(a), ExprId(w[1] as u32)),
            7 => ExprNode::NatSmall(lo(w[1]), hi(w[1])),
            8 => ExprNode::NatBig(BigId(a)),
            9 => ExprNode::Str(StrId(a)),
            10 => ExprNode::Proj(NameId(a), lo(w[1]), ExprId(hi(w[1]))),
            _ => ExprNode::FVar(a),
        }
    }
}

impl Pack for NameNode {
    fn pack(&self) -> [u64; 2] {
        match *self {
            NameNode::Anon => [0, 0],
            NameNode::Str(p, s) => [1 | (p.0 as u64) << 8, s.0 as u64],
            NameNode::Num(p, k) => [2 | (p.0 as u64) << 8, k],
        }
    }

    fn unpack(w: [u64; 2]) -> Self {
        let p = NameId((w[0] >> 8) as u32);
        match w[0] as u8 {
            0 => NameNode::Anon,
            1 => NameNode::Str(p, StrId(w[1] as u32)),
            _ => NameNode::Num(p, w[1]),
        }
    }
}

impl Pack for LevelNode {
    fn pack(&self) -> [u64; 2] {
        let b = |tag: u64, x: LevelId| tag | (x.0 as u64) << 8;
        match *self {
            LevelNode::Zero => [0, 0],
            LevelNode::Succ(l) => [b(1, l), 0],
            LevelNode::Max(x, y) => [b(2, x), y.0 as u64],
            LevelNode::IMax(x, y) => [b(3, x), y.0 as u64],
            LevelNode::Param(n) => [4 | (n.0 as u64) << 8, 0],
        }
    }

    fn unpack(w: [u64; 2]) -> Self {
        let a = (w[0] >> 8) as u32;
        match w[0] as u8 {
            0 => LevelNode::Zero,
            1 => LevelNode::Succ(LevelId(a)),
            2 => LevelNode::Max(LevelId(a), LevelId(w[1] as u32)),
            3 => LevelNode::IMax(LevelId(a), LevelId(w[1] as u32)),
            _ => LevelNode::Param(NameId(a)),
        }
    }
}

impl Pack for LetBinder {
    fn pack(&self) -> [u64; 2] {
        [
            self.name.0 as u64 | (self.nondep as u64) << 32,
            self.ty.0 as u64 | (self.value.0 as u64) << 32,
        ]
    }

    fn unpack(w: [u64; 2]) -> Self {
        LetBinder {
            name: NameId(lo(w[0])),
            nondep: hi(w[0]) != 0,
            ty: ExprId(lo(w[1])),
            value: ExprId(hi(w[1])),
        }
    }
}

/// A concurrent arena of packable nodes, with one word of side data each.
pub(crate) struct Conc<T, const B: u32 = 16> {
    shards: Vec<Mutex<HashTable<u32>>>,
    /// Ids are below this (see [`Par::new`]).
    max: usize,
    words: Words<3, B>,
    next: AtomicU32,
    what: &'static str,
    _t: std::marker::PhantomData<T>,
}

impl<T: Pack, const B: u32> Conc<T, B> {
    /// An arena with room for about `n` nodes before any shard rehashes
    /// (rehashing reads every node of the shard back).
    fn new(what: &'static str, n: usize, max: usize) -> Self {
        let per = n / SHARDS + n / (8 * SHARDS);
        Conc {
            shards: (0..SHARDS)
                .map(|_| Mutex::new(HashTable::with_capacity(per)))
                .collect(),
            words: Words::new(max),
            max,
            next: AtomicU32::new(0),
            what,
            _t: std::marker::PhantomData,
        }
    }

    pub fn len(&self) -> usize {
        self.next.load(Ordering::Acquire) as usize
    }

    #[inline]
    pub fn get(&self, id: u32) -> T {
        let w = self.words.get(id);
        T::unpack([w[0], w[1]])
    }

    #[inline]
    pub fn side(&self, id: u32) -> u64 {
        self.words.get(id)[2]
    }

    /// The id of `node`, adding it (with side data `side()`) if new.
    #[inline]
    pub fn intern(&self, node: T, side: impl FnOnce() -> u64) -> Result<u32, Overflow> {
        let h = node.hash();
        let mut t = self.shards[shard_of(h)].lock().expect("shard lock");
        if let Some(&id) = t.find(h, |&id| self.get(id).same(&node)) {
            return Ok(id);
        }
        let id = self.next.fetch_add(1, Ordering::AcqRel);
        if id >= u32::MAX - 1 || id as usize >= self.max {
            self.next.store(id, Ordering::Release);
            return Err(Overflow(self.what));
        }
        let p = node.pack();
        self.words.set(id, [p[0], p[1], side()]);
        t.insert_unique(h, id, |&i| self.get(i).hash());
        Ok(id)
    }

    /// The shard tables, and the nodes and side words in id order.
    fn into_parts(self) -> (Vec<HashTable<u32>>, Words<3, B>, usize) {
        let n = self.len();
        let tables = self
            .shards
            .into_iter()
            .map(|m| m.into_inner().expect("shard lock"))
            .collect();
        (tables, self.words, n)
    }
}

/// A concurrent table of values identified by content (strings, level
/// lists, big numbers): rare enough that one table with a lock per shard
/// and boxed values is fine.
struct ConcVals<V: ?Sized> {
    max: usize,
    shards: Vec<Mutex<HashTable<u32>>>,
    cells: Cells<Box<V>>,
    next: AtomicU32,
    what: &'static str,
}

impl<V: ?Sized + PartialEq> ConcVals<V> {
    fn new(what: &'static str, max: usize) -> Self {
        ConcVals {
            max,
            shards: (0..SHARDS).map(|_| Mutex::new(HashTable::new())).collect(),
            cells: Cells::new(max),
            next: AtomicU32::new(0),
            what,
        }
    }

    fn len(&self) -> usize {
        self.next.load(Ordering::Acquire) as usize
    }

    fn intern(
        &self,
        v: &V,
        h: u64,
        mk: impl FnOnce() -> Box<V>,
        rehash: impl Fn(&V) -> u64,
    ) -> Result<u32, Overflow> {
        let mut t = self.shards[shard_of(h)].lock().expect("shard lock");
        if let Some(&id) = t.find(h, |&id| **self.cells.get(id) == *v) {
            return Ok(id);
        }
        let id = self.next.fetch_add(1, Ordering::AcqRel);
        if id >= u32::MAX - 1 || id as usize >= self.max {
            self.next.store(id, Ordering::Release);
            return Err(Overflow(self.what));
        }
        self.cells.set(id, mk());
        t.insert_unique(h, id, |&i| rehash(self.cells.get(i)));
        Ok(id)
    }

    fn get(&self, id: u32) -> &V {
        self.cells.get(id)
    }
}

/// All the arenas of an environment being loaded.
pub struct Par {
    strs: ConcVals<str>,
    pub(crate) names: Conc<NameNode>,
    /// Side data: whether the level has a parameter.
    levels: Conc<LevelNode>,
    lists: ConcVals<[LevelId]>,
    /// Side data: the `ExprData` bits. Chunks of 2^21 nodes (48 MiB).
    pub(crate) exprs: Conc<ExprNode, 21>,
    lets: Conc<LetBinder>,
    bigs: ConcVals<BigUint>,
}

impl Par {
    /// Arenas sized for `bytes` of `.olean` files. Lean's files hold about
    /// one distinct expression per 60 bytes and one name per 1300 (Init,
    /// Std and Mathlib); the tables grow past that if needed. Every node
    /// comes from an object of at least 16 bytes, so there are fewer than
    /// `bytes / 16` of each kind (plus the few made here).
    pub fn new(bytes: u64) -> Self {
        let b = usize::try_from(bytes).unwrap_or(usize::MAX);
        let max = b / 16 + 16;
        let p = Par {
            strs: ConcVals::new("string pool exceeds 4 GiB", max),
            names: Conc::new("too many names", b / 1300, max),
            levels: Conc::new("too many universe levels", 0, max),
            lists: ConcVals::new("too many universe level lists", max),
            exprs: Conc::new("too many expressions", b / 60, max),
            lets: Conc::new("too many let binders", b / 3000, max),
            bigs: ConcVals::new("too many big literals", max),
        };
        // Id 0 is the anonymous name, the zero level and the empty list,
        // as in the sequential arenas.
        let anon = p.names.intern(NameNode::Anon, || 0).expect("empty");
        let zero = p.levels.intern(LevelNode::Zero, || 0).expect("empty");
        let empty = p.list(&[]).expect("empty");
        debug_assert!(anon == 0 && zero == 0 && empty == LevelList::EMPTY);
        p
    }

    pub fn str(&self, s: &str) -> Result<StrId, Overflow> {
        let h = hash_bytes(s.as_bytes());
        let id = self
            .strs
            .intern(s, h, || s.into(), |v| hash_bytes(v.as_bytes()))?;
        Ok(StrId(id))
    }

    pub fn name(&self, n: NameNode) -> Result<NameId, Overflow> {
        Ok(NameId(self.names.intern(n, || 0)?))
    }

    pub fn level(&self, l: LevelNode) -> Result<LevelId, Overflow> {
        let hp = |x: LevelId| self.levels.side(x.0);
        let id = self.levels.intern(l, || match l {
            LevelNode::Zero => 0,
            LevelNode::Succ(a) => hp(a),
            LevelNode::Max(a, b) | LevelNode::IMax(a, b) => hp(a) | hp(b),
            LevelNode::Param(_) => 1,
        })?;
        Ok(LevelId(id))
    }

    pub fn list(&self, ls: &[LevelId]) -> Result<LevelList, Overflow> {
        let h = crate::level::list_hash(ls);
        let id = self
            .lists
            .intern(ls, h, || ls.into(), crate::level::list_hash)?;
        Ok(LevelList(id))
    }

    fn list_has_param(&self, l: LevelList) -> bool {
        self.lists
            .get(l.0)
            .iter()
            .any(|x| self.levels.side(x.0) != 0)
    }

    pub fn let_binder(&self, b: LetBinder) -> Result<LetId, Overflow> {
        Ok(LetId(self.lets.intern(b, || 0)?))
    }

    pub fn nat_big(&self, n: &BigUint) -> Result<BigId, Overflow> {
        let h = crate::expr::big_hash(n);
        let id = self
            .bigs
            .intern(n, h, || Box::new(n.clone()), crate::expr::big_hash)?;
        Ok(BigId(id))
    }

    fn data(&self, e: ExprId) -> ExprData {
        ExprData::from_bits(self.exprs.side(e.0) as u32)
    }

    pub fn expr(&self, node: ExprNode) -> Result<ExprId, Overflow> {
        let id = self.exprs.intern(node, || {
            let d = |x: ExprId| self.data(x);
            let data = match node {
                ExprNode::BVar(i) => ExprData::new(i + 1, false),
                ExprNode::Sort(l) => ExprData::new(0, self.levels.side(l.0) != 0),
                ExprNode::Const(_, ls) => ExprData::new(0, self.list_has_param(ls)),
                ExprNode::App(f, a) => d(f).union(d(a)),
                ExprNode::Lam(_, _, t, b) | ExprNode::Pi(_, _, t, b) => {
                    d(t).union(d(b).under_binder())
                }
                ExprNode::Let(h, b) => {
                    let h = self.lets.get(h.0);
                    d(h.ty).union(d(h.value)).union(d(b).under_binder())
                }
                ExprNode::NatSmall(..) | ExprNode::NatBig(_) | ExprNode::Str(_) => {
                    ExprData::new(0, false)
                }
                ExprNode::Proj(_, _, e) => d(e),
                ExprNode::FVar(_) => ExprData::FVAR,
            };
            data.bits() as u64
        })?;
        Ok(ExprId(id))
    }

    pub fn expr_node(&self, e: ExprId) -> ExprNode {
        self.exprs.get(e.0)
    }

    /// The dotted form of a name, for messages.
    pub fn display(&self, n: NameId) -> String {
        let mut parts = Vec::new();
        let mut cur = n;
        loop {
            match self.names.get(cur.0) {
                NameNode::Anon => break,
                NameNode::Str(p, s) => {
                    parts.push(self.strs.get(s.0).to_string());
                    cur = p;
                }
                NameNode::Num(p, k) => {
                    parts.push(k.to_string());
                    cur = p;
                }
            }
        }
        if parts.is_empty() {
            return "[anonymous]".into();
        }
        parts.reverse();
        parts.join(".")
    }

    /// The environment's arenas, with the same ids. `threads` copy the
    /// expression nodes out in parallel.
    pub fn finish(self, threads: usize) -> Result<(Names, Levels, Exprs), Overflow> {
        let Par {
            strs,
            names,
            levels,
            lists,
            exprs,
            lets,
            bigs,
        } = self;
        let mut pool = StrPool::new();
        for i in 0..strs.len() as u32 {
            let id = pool.intern(strs.get(i))?;
            debug_assert_eq!(id.0, i);
        }
        let mut ns = Names::new();
        ns.strings = pool;
        let (_, nw, nn) = names.into_parts();
        for i in 1..nn as u32 {
            let w = nw.get(i);
            let (id, _) = ns.intern(NameNode::unpack([w[0], w[1]]))?;
            debug_assert_eq!(id.0, i);
        }
        drop(nw);
        let mut ls = Levels::new();
        let (_, lw, ln) = levels.into_parts();
        for i in 1..ln as u32 {
            let w = lw.get(i);
            let (id, _) = ls.intern(LevelNode::unpack([w[0], w[1]]))?;
            debug_assert_eq!(id.0, i);
        }
        for i in 1..lists.len() as u32 {
            let id = ls.intern_list(lists.get(i))?;
            debug_assert_eq!(id.0, i);
        }
        let mut li = Interner::new("too many let binders");
        let (_, letw, letn) = lets.into_parts();
        for i in 0..letn as u32 {
            let w = letw.get(i);
            let (id, _) = li.intern(LetBinder::unpack([w[0], w[1]]))?;
            debug_assert_eq!(id, i);
        }
        let bigs: Vec<BigUint> = (0..bigs.len() as u32)
            .map(|i| bigs.get(i).clone())
            .collect();
        let (tables, ew, en) = exprs.into_parts();
        // Copy the nodes out chunk by chunk, freeing each chunk as it goes,
        // so the store and the arena are not both held whole.
        let _ = threads;
        let mut nodes = Vec::with_capacity(en);
        let mut data = Vec::with_capacity(en);
        for c in ew.chunks.into_iter() {
            if nodes.len() >= en {
                break;
            }
            let Some(c) = c.into_inner() else { break };
            let take = (en - nodes.len()).min(c.len() / 3);
            for w in c[..take * 3].as_chunks::<3>().0 {
                let w: [u64; 3] = std::array::from_fn(|i| w[i].load(Ordering::Relaxed));
                nodes.push(ExprNode::unpack([w[0], w[1]]));
                data.push(ExprData::from_bits(w[2] as u32));
            }
        }
        assert_eq!(nodes.len(), en, "expression store complete");
        let es = Exprs::from_parts(nodes, tables, data, li, bigs);
        Ok((ns, ls, es))
    }
}
