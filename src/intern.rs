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

    #[inline]
    pub fn push(&mut self, v: T) {
        match self.chunks.last_mut() {
            // No reallocation, and the chunk is not full.
            Some(c) if c.len() < c.capacity().min(CHUNK) => c.push(v),
            _ => self.push_chunk(v),
        }
        self.len += 1;
    }

    #[cold]
    #[inline(never)]
    fn push_chunk(&mut self, v: T) {
        if let Some(c) = self.chunks.last_mut()
            && c.len() < CHUNK
        {
            c.push(v);
            return;
        }
        let mut c = Vec::with_capacity(if self.chunks.is_empty() { 0 } else { CHUNK });
        c.push(v);
        self.chunks.push(c);
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
    /// Number of lines.
    lines: usize,
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
        // Any number of lines works (a probe maps the hash onto them by a
        // multiplication), so the table is no bigger than it must be.
        let lines = (n.div_ceil(LINE) * 4 / 3 + 1).min(u32::MAX as usize);
        IdTable {
            slots: (0..lines * LINE).map(|_| AtomicU64::new(0)).collect(),
            lines,
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
        ((h as u32 as u64 * self.lines as u64) >> 32) as usize
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
            line = if line + 1 == self.lines { 0 } else { line + 1 };
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
            line = if line + 1 == self.lines { 0 } else { line + 1 };
        }
    }

    /// Add `id` with hash `h` unless an id for which `eq` holds is
    /// present (then that id); there must be room. For a table only this
    /// thread sees.
    #[inline]
    pub fn insert_unique(
        &mut self,
        h: u64,
        mut eq: impl FnMut(u32) -> bool,
        id: u32,
    ) -> Option<u32> {
        let tag = tag_of(h);
        let mut line = self.line(h);
        loop {
            for s in &mut self.slots[line * LINE..line * LINE + LINE] {
                let v = s.get_mut();
                if *v == 0 {
                    *v = tag | id as u64;
                    *self.len.get_mut() += 1;
                    return None;
                }
                if *v & !0xffff_ffff == tag && eq(*v as u32) {
                    return Some(*v as u32);
                }
            }
            line = if line + 1 == self.lines { 0 } else { line + 1 };
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
            line = if line + 1 == self.lines { 0 } else { line + 1 };
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

    /// Add `node` without looking it up or indexing it: until
    /// [`Big::index`], lookups do not see it.
    pub fn push_unindexed(&mut self, node: T) -> Result<u32, Overflow> {
        let id = self.nodes.len();
        if id >= u32::MAX as usize - 1 {
            return Err(Overflow(self.what));
        }
        self.nodes.push(node);
        Ok(id as u32)
    }

    /// Index every node anew, on `threads` threads. If two nodes are
    /// equal, the first such pair found (the later id, the earlier one).
    pub fn index(&mut self, threads: usize) -> Result<(), (u32, u32)>
    where
        T: Sync,
    {
        let n = self.nodes.len();
        let threads = threads.clamp(1, n.div_ceil(1 << 16).max(1));
        if threads == 1 {
            return self.index_here();
        }
        let table = IdTable::with_capacity(n);
        let nodes = &self.nodes;
        let dup = std::sync::Mutex::new(None);
        let next = std::sync::atomic::AtomicUsize::new(0);
        const STEP: usize = 1 << 14;
        std::thread::scope(|s| {
            for _ in 0..threads {
                s.spawn(|| {
                    loop {
                        let lo = next.fetch_add(STEP, Ordering::Relaxed);
                        if lo >= n {
                            return;
                        }
                        let hi = (lo + STEP).min(n);
                        // Hash a group of nodes and touch their lines
                        // first, so that the cache misses overlap.
                        const GROUP: usize = 32;
                        let mut hs = [0u64; GROUP];
                        let mut acc = 0u64;
                        for g in (lo..hi).step_by(GROUP) {
                            let k = GROUP.min(hi - g);
                            for (i, h) in hs[..k].iter_mut().enumerate() {
                                *h = nodes.get((g + i) as u32).hash();
                                acc = acc.wrapping_add(table.touch(*h));
                            }
                            std::hint::black_box(acc);
                            for (i, &h) in hs[..k].iter().enumerate() {
                                let id = g + i;
                                let node = nodes.get(id as u32);
                                let (got, fresh) = table.insert_shared(
                                    h,
                                    |o| nodes.get(o).same(node),
                                    || id as u32,
                                );
                                if !fresh {
                                    let mut d = dup.lock().unwrap_or_else(|e| e.into_inner());
                                    let (a, b) = (got.max(id as u32), got.min(id as u32));
                                    if d.is_none_or(|(x, _)| a < x) {
                                        *d = Some((a, b));
                                    }
                                }
                            }
                        }
                    }
                });
            }
        });
        if let Some(d) = dup.into_inner().unwrap_or_else(|e| e.into_inner()) {
            return Err(d);
        }
        table.add_len(n);
        self.table = table;
        Ok(())
    }

    /// [`Big::index`] on this thread.
    fn index_here(&mut self) -> Result<(), (u32, u32)> {
        let n = self.nodes.len();
        let mut table = IdTable::with_capacity(n);
        let nodes = &self.nodes;
        // A table line is picked by the low half of the hash, scaled, so
        // its top bits pick a range of lines. Hash the nodes into buckets
        // by those bits, and then insert a bucket at a time: the lines a
        // bucket fills are few enough to stay in the cache. A round does a
        // part of the nodes, to bound the space the buckets take.
        const BITS: u32 = 10;
        const BUCKETS: usize = 1 << BITS;
        const ROUNDS: usize = 4;
        let round = n.div_ceil(ROUNDS).max(1);
        let cap = round / BUCKETS + round / BUCKETS / 4 + 64;
        let mut fill = vec![0usize; BUCKETS];
        let mut hs = vec![0u64; BUCKETS * cap];
        let mut ids = vec![0u32; BUCKETS * cap];
        // Entries of a bucket that is full, inserted last.
        let mut spill = Vec::new();
        for start in (0..n).step_by(round) {
            fill.fill(0);
            spill.clear();
            for id in start as u32..(start + round).min(n) as u32 {
                let h = nodes.get(id).hash();
                let b = (h as u32 >> (32 - BITS)) as usize;
                let k = fill[b];
                if k < cap {
                    let at = b * cap + k;
                    hs[at] = h;
                    ids[at] = id;
                    fill[b] = k + 1;
                } else {
                    spill.push((h, id));
                }
            }
            let bucketed = (0..BUCKETS).flat_map(|b| {
                let at = b * cap;
                let k = fill[b];
                hs[at..at + k].iter().copied().zip(ids[at..at + k].iter().copied())
            });
            for (h, id) in bucketed.chain(spill.iter().copied()) {
                let same = |o| nodes.get(o).same(nodes.get(id));
                if let Some(old) = table.insert_unique(h, same, id) {
                    return Err((id.max(old), id.min(old)));
                }
            }
        }
        self.table = table;
        Ok(())
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
