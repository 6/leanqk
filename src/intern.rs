//! A generic hash-consing arena: nodes live in one `Vec`, and a SwissTable
//! of `u32` ids (5 bytes per slot including the control byte) finds the
//! existing copy of a node. Nodes refer to children by id, so equality and
//! hashing are shallow, and two ids are equal iff their terms are.

use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

use hashbrown::HashTable;
use hashbrown::hash_table::Entry;

use crate::strings::Overflow;

/// A node that can be hash-consed. Children must be canonical ids.
pub trait Node: Copy + Eq {
    fn hash(&self) -> u64;

    /// The equality the table interns by; `hash` must agree with it.
    /// Defaults to `==`.
    #[inline]
    fn same(&self, other: &Self) -> bool {
        self == other
    }
}

pub struct Interner<T> {
    nodes: Vec<T>,
    table: HashTable<u32>,
    what: &'static str,
}

#[allow(dead_code)] // `is_empty`, `nodes` and `reserve` are kept for symmetry with `Sharded`.
impl<T: Node> Interner<T> {
    pub fn new(what: &'static str) -> Self {
        Interner {
            nodes: Vec::new(),
            table: HashTable::new(),
            what,
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    #[inline]
    pub fn get(&self, id: u32) -> &T {
        &self.nodes[id as usize]
    }

    #[inline]
    pub fn nodes(&self) -> &[T] {
        &self.nodes
    }

    /// The id of `node`, if present.
    pub fn find(&self, node: &T) -> Option<u32> {
        let nodes = &self.nodes;
        self.table
            .find(node.hash(), |&id| nodes[id as usize].same(node))
            .copied()
    }

    /// Return the id of `node`, adding it if new. The flag says whether it
    /// was added.
    #[inline]
    pub fn intern(&mut self, node: T) -> Result<(u32, bool), Overflow> {
        let h = node.hash();
        let Self { nodes, table, what } = self;
        let id = nodes.len() as u32;
        match table.entry(
            h,
            |&id| nodes[id as usize].same(&node),
            |&id| nodes[id as usize].hash(),
        ) {
            Entry::Occupied(e) => Ok((*e.get(), false)),
            Entry::Vacant(e) => {
                // u32::MAX is kept free as a sentinel.
                if id >= u32::MAX - 1 {
                    return Err(Overflow(what));
                }
                e.insert(id);
                nodes.push(node);
                Ok((id, true))
            }
        }
    }

    /// Make room for `extra` more nodes without rehashing.
    pub fn reserve(&mut self, extra: usize) {
        let Self { nodes, table, .. } = self;
        nodes.reserve(extra);
        let nodes = &*nodes;
        table.reserve(extra, |&id| nodes[id as usize].hash());
    }

    pub fn heap_bytes(&self) -> usize {
        self.nodes.capacity() * size_of::<T>() + self.table.capacity() * 5
    }
}

/// Ids per chunk of a [`Chunked`] store.
pub const CHUNK_BITS: u32 = 20;
pub const CHUNK: usize = 1 << CHUNK_BITS;
const CHUNK_MASK: u32 = CHUNK as u32 - 1;

/// A vector in chunks of [`CHUNK`] elements: growing it never moves (or
/// copies) what is already there, and the loader can build the chunks on
/// several threads and hand them over as they are. Indexing is two loads,
/// the chunk directory being small enough to stay in cache.
pub struct Chunked<T> {
    chunks: Vec<Vec<T>>,
    len: usize,
}

impl<T> Default for Chunked<T> {
    fn default() -> Self {
        Chunked {
            chunks: Vec::new(),
            len: 0,
        }
    }
}

impl<T> Chunked<T> {
    /// A store of full chunks (every chunk but the last has [`CHUNK`]
    /// elements).
    pub(crate) fn from_chunks(chunks: Vec<Vec<T>>) -> Self {
        let len = chunks.iter().map(|c| c.len()).sum();
        debug_assert!(chunks.iter().rev().skip(1).all(|c| c.len() == CHUNK));
        Chunked { chunks, len }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline]
    pub fn get(&self, i: u32) -> &T {
        &self.chunks[(i >> CHUNK_BITS) as usize][(i & CHUNK_MASK) as usize]
    }

    pub fn push(&mut self, v: T) {
        match self.chunks.last_mut() {
            Some(c) if c.len() < CHUNK => c.push(v),
            _ => {
                let mut c = Vec::with_capacity(if self.chunks.is_empty() { 0 } else { CHUNK });
                c.push(v);
                self.chunks.push(c);
            }
        }
        self.len += 1;
    }

    pub fn reserve(&mut self, extra: usize) {
        if let Some(c) = self.chunks.last_mut() {
            let room = CHUNK - c.len();
            c.reserve(extra.min(room));
        }
    }

    pub fn heap_bytes(&self) -> usize {
        self.chunks.iter().map(|c| c.capacity()).sum::<usize>() * size_of::<T>()
            + self.chunks.capacity() * size_of::<Vec<T>>()
    }
}

/// Slots per probe line: one 64-byte cache line.
const LINE: usize = 8;

/// An open-addressing table of `u32` ids, probed a cache line at a time.
/// A slot holds 32 bits of the key's hash (with the low bit set, so a
/// used slot is never 0) and the id, so a probe reads a node only when 32
/// hash bits agree. Slots are atomics so that the `.olean` loader can
/// insert from several threads at once ([`IdTable::insert_shared`]);
/// nothing is ever removed, so a probe may stop at the first empty slot.
pub struct IdTable {
    slots: Box<[AtomicU64]>,
    /// Number of lines minus one (the line count is a power of two).
    mask: usize,
    len: AtomicUsize,
}

impl Default for IdTable {
    fn default() -> Self {
        IdTable::with_capacity(0)
    }
}

#[inline]
fn tag_of(h: u64) -> u64 {
    ((h >> 32) | 1) << 32
}

impl IdTable {
    /// A table with room for about `n` ids before it must grow.
    pub fn with_capacity(n: usize) -> Self {
        let lines = (n.div_ceil(LINE) * 8 / 7).next_power_of_two().max(1);
        IdTable {
            slots: (0..lines * LINE).map(|_| AtomicU64::new(0)).collect(),
            mask: lines - 1,
            len: AtomicUsize::new(0),
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len.load(Ordering::Relaxed)
    }

    #[inline]
    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Whether `extra` more ids fit at a load factor of at most 7/8.
    #[inline]
    pub fn has_room(&self, extra: usize) -> bool {
        (self.len() + extra) * 8 <= self.slots.len() * 7
    }

    #[inline]
    fn line(&self, h: u64) -> usize {
        (h as usize) & self.mask
    }

    /// Touch the first line `h` probes, so that a batch of probes can
    /// overlap their cache misses.
    #[inline]
    pub fn touch(&self, h: u64) -> u64 {
        self.slots[self.line(h) * LINE].load(Ordering::Relaxed)
    }

    /// The id with hash `h` for which `eq` holds.
    #[inline]
    pub fn find(&self, h: u64, mut eq: impl FnMut(u32) -> bool) -> Option<u32> {
        let tag = tag_of(h);
        let mut line = self.line(h);
        loop {
            for s in &self.slots[line * LINE..line * LINE + LINE] {
                let v = s.load(Ordering::Acquire);
                if v == 0 {
                    return None;
                }
                if v & !0xffff_ffff == tag && eq(v as u32) {
                    return Some(v as u32);
                }
            }
            line = (line + 1) & self.mask;
        }
    }

    /// Add `id` with hash `h`; the caller knows no equal key is present
    /// and that there is room.
    pub fn insert_new(&mut self, h: u64, id: u32) {
        let tag = tag_of(h);
        let mut line = self.line(h);
        loop {
            for s in &mut self.slots[line * LINE..line * LINE + LINE] {
                let v = s.get_mut();
                if *v == 0 {
                    *v = tag | id as u64;
                    *self.len.get_mut() += 1;
                    return;
                }
            }
            line = (line + 1) & self.mask;
        }
    }

    /// The id with hash `h` for which `eq` holds, or else the id `make`
    /// returns, added; several threads may call this at once. `make` is
    /// called at most once, before the id is published, and the flag says
    /// whether its id was added. (If another thread adds an equal key
    /// first, the id `make` gave is not used, and the caller must forget
    /// it.) The count is not updated: callers add theirs in bulk with
    /// [`IdTable::add_len`].
    #[inline]
    pub fn insert_shared(
        &self,
        h: u64,
        mut eq: impl FnMut(u32) -> bool,
        make: impl FnOnce() -> u32,
    ) -> (u32, bool) {
        let tag = tag_of(h);
        let mut line = self.line(h);
        let mut make = Some(make);
        let mut mine: Option<u32> = None;
        loop {
            let mut i = 0;
            while i < LINE {
                let s = &self.slots[line * LINE + i];
                let v = s.load(Ordering::Acquire);
                if v == 0 {
                    let id = *mine.get_or_insert_with(|| (make.take().expect("once"))());
                    match s.compare_exchange(
                        0,
                        tag | id as u64,
                        Ordering::AcqRel,
                        Ordering::Acquire,
                    ) {
                        Ok(_) => return (id, true),
                        Err(_) => continue,
                    }
                }
                if v & !0xffff_ffff == tag && eq(v as u32) {
                    return (v as u32, false);
                }
                i += 1;
            }
            line = (line + 1) & self.mask;
        }
    }

    pub fn add_len(&self, n: usize) {
        self.len.fetch_add(n, Ordering::Relaxed);
    }

    /// The same ids in a table with room for `n`, rehashed by `hash`.
    pub fn grown(&self, n: usize, hash: impl Fn(u32) -> u64) -> IdTable {
        let mut t = IdTable::with_capacity(n.max(self.len()));
        for s in self.slots.iter() {
            let v = s.load(Ordering::Relaxed);
            if v != 0 {
                t.insert_new(hash(v as u32), v as u32);
            }
        }
        t
    }

    pub fn heap_bytes(&self) -> usize {
        self.slots.len() * 8
    }
}

/// The arena of the environment's big kinds (expressions, names): like
/// [`Interner`], but with chunked storage and an [`IdTable`], so that the
/// `.olean` loader can build both on several threads and hand them over
/// without copying. The checker's small overlay arenas stay [`Interner`]s.
pub struct Big<T> {
    nodes: Chunked<T>,
    table: IdTable,
    what: &'static str,
}

impl<T: Node> Big<T> {
    pub fn new(what: &'static str) -> Self {
        Big {
            nodes: Chunked::default(),
            table: IdTable::with_capacity(16),
            what,
        }
    }

    /// An arena of `nodes` with a table that indexes them. The caller
    /// guarantees that the table holds exactly the ids of the nodes that
    /// can be looked up, each under its [`Node::hash`], pairwise distinct
    /// under [`Node::same`]. (Ids not in the table are allowed: the
    /// loader's unused ids, which no term refers to.)
    pub(crate) fn from_parts(nodes: Chunked<T>, table: IdTable, what: &'static str) -> Self {
        Big { nodes, table, what }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    #[inline]
    pub fn get(&self, id: u32) -> &T {
        self.nodes.get(id)
    }

    /// The id of `node`, if present.
    #[inline]
    pub fn find(&self, node: &T) -> Option<u32> {
        let nodes = &self.nodes;
        self.table.find(node.hash(), |id| nodes.get(id).same(node))
    }

    /// Return the id of `node`, adding it if new. The flag says whether it
    /// was added.
    #[inline]
    pub fn intern(&mut self, node: T) -> Result<(u32, bool), Overflow> {
        let h = node.hash();
        let nodes = &self.nodes;
        if let Some(id) = self.table.find(h, |id| nodes.get(id).same(&node)) {
            return Ok((id, false));
        }
        let id = self.nodes.len();
        // u32::MAX is kept free as a sentinel.
        if id >= u32::MAX as usize - 1 {
            return Err(Overflow(self.what));
        }
        if !self.table.has_room(1) {
            self.grow(self.table.len() * 2);
        }
        self.table.insert_new(h, id as u32);
        self.nodes.push(node);
        Ok((id as u32, true))
    }

    fn grow(&mut self, n: usize) {
        let nodes = &self.nodes;
        self.table = self.table.grown(n, |id| nodes.get(id).hash());
    }

    /// Make room for `extra` more nodes without growing the table.
    pub fn reserve(&mut self, extra: usize) {
        self.nodes.reserve(extra);
        if !self.table.has_room(extra) {
            self.grow(self.table.len() + extra);
        }
    }

    pub fn heap_bytes(&self) -> usize {
        self.nodes.heap_bytes() + self.table.heap_bytes()
    }
}

/// Shards of the loader's locked tables (strings, level lists, big
/// literals).
pub const SHARDS: usize = 64;

/// The shard of a hash.
#[inline]
pub fn shard_of(h: u64) -> usize {
    (h >> 51) as usize & (SHARDS - 1)
}
