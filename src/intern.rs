//! A generic hash-consing arena: nodes live in one `Vec`, and a SwissTable
//! of `u32` ids (5 bytes per slot including the control byte) finds the
//! existing copy of a node. Nodes refer to children by id, so equality and
//! hashing are shallow, and two ids are equal iff their terms are.

use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

use hashbrown::HashTable;
use hashbrown::hash_table::Entry;

use crate::slab::Slab;
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

    /// Add `node` without looking it up or indexing it: [`Interner::find`]
    /// and [`Interner::intern`] never return its id (an equal node interned
    /// later gets an id of its own).
    #[inline]
    pub fn push_unindexed(&mut self, node: T) -> Result<u32, Overflow> {
        let id = self.nodes.len() as u32;
        if id >= u32::MAX - 1 {
            return Err(Overflow(self.what));
        }
        self.nodes.push(node);
        Ok(id)
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

/// Ids per chunk of the `.olean` loader's stores.
pub const CHUNK_BITS: u32 = 20;
pub const CHUNK: usize = 1 << CHUNK_BITS;

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
        let lines = Self::lines_for(n);
        IdTable {
            slots: (0..lines * LINE).map(|_| AtomicU64::new(0)).collect(),
            lines,
            len: AtomicUsize::new(0),
        }
    }

    /// The lines of a table for `n` ids. Any number of lines works (a
    /// probe maps the hash onto them by a multiplication), so the table is
    /// no bigger than it must be.
    fn lines_for(n: usize) -> usize {
        (n.div_ceil(LINE) * 4 / 3 + 1).min(u32::MAX as usize)
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
/// [`Interner`], but with its nodes in a [`Slab`] (one array that never
/// moves; the checker's stores add their own expressions above the
/// environment's) and an [`IdTable`], which the `.olean` loader can build
/// on several threads.
pub struct Big<T: Copy> {
    nodes: Slab<T>,
    table: IdTable,
    what: &'static str,
}

impl<T: Node> Big<T> {
    pub fn new(what: &'static str) -> Self {
        Big {
            nodes: Slab::new(),
            table: IdTable::with_capacity(16),
            what,
        }
    }

    /// An arena of `nodes` with a table that indexes them. The caller
    /// guarantees that the table holds exactly the ids of the nodes that
    /// can be looked up, each under its [`Node::hash`], pairwise distinct
    /// under [`Node::same`]. (Ids not in the table are allowed: the
    /// loader's unused ids, which no term refers to.)
    pub(crate) fn from_parts(nodes: Slab<T>, table: IdTable, what: &'static str) -> Self {
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

    pub fn nodes(&self) -> &Slab<T> {
        &self.nodes
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
        // Ids stay below 2^31 (the slab), u32::MAX free as a sentinel.
        if id >= crate::slab::CAP {
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
        let id = self.nodes.len() as u32;
        if !self.nodes.try_push(node) {
            return Err(Overflow(self.what));
        }
        Ok(id)
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
        let lines = IdTable::lines_for(n);
        let nodes = &self.nodes;
        // A table line is picked by the low half of the hash (scaled), so
        // in the order of that half, the ids fill the table from start to
        // end, each at the first free slot from its line on: no probing,
        // and equal keys (equal hashes) come one after the other. So hash
        // the nodes into buckets by the top bits of that half, and sort
        // each bucket by the rest (radix sort, as the table is filled a
        // bucket at a time).
        const BITS: u32 = 10;
        const BUCKETS: usize = 1 << BITS;
        // The rest, sorted on in two passes.
        const DIGIT: u32 = 11;
        const _: () = assert!(BITS + 2 * DIGIT == 32);
        // The buckets are kept in groups, each freed once its buckets are
        // in the table, and the table's slots are only written (zeroed)
        // as the buckets reach them: the two are not all in memory at
        // once.
        const GROUPS: usize = 8;
        const PER: usize = BUCKETS / GROUPS;
        let cap = n / BUCKETS + n / BUCKETS / 8 + 64;
        let mut fill = [0usize; BUCKETS];
        // The buckets' entries: hash (low and high halves) and id, in
        // little-endian bytes, in a map of their own, each group's pages
        // given back to the system once its buckets are in the table.
        let mut map = Entries::new(BUCKETS * cap);
        // Entries of a bucket that is full (and, below, those that would
        // go past the end of the table), inserted last.
        let mut spill = Vec::new();
        let ents = map.ents();
        for (id, node) in (0u32..).zip(nodes.as_slice()) {
            let h = node.hash();
            let b = (h as u32 >> (32 - BITS)) as usize;
            let k = fill[b];
            if k < cap {
                ents[b * cap + k] = entry(h, id);
                fill[b] = k + 1;
            } else {
                spill.push((h, id));
            }
        }
        let digit = |l: u32, d: u32| (l >> (d * DIGIT)) as usize & ((1 << DIGIT) - 1);
        // Each pass writes all of a bucket's entries, so these are never
        // cleared.
        let mut tmp: Vec<[u32; 3]> = vec![[0; 3]; cap];
        let mut sorted: Vec<[u32; 3]> = vec![[0; 3]; cap];
        let total = lines * LINE;
        let mut slots: Vec<AtomicU64> = Vec::with_capacity(total);
        let lines = lines as u64;
        // The slot after the last one filled.
        let mut next = 0usize;
        let mut added = 0usize;
        for (b, &k) in fill.iter().enumerate() {
            if b % PER == 0 && b > 0 {
                map.release((b - PER) * cap..b * cap);
            }
            let bucket = &map.ents()[b * cap..b * cap + k];
            // The slots this bucket can reach: from its last line on, `k`
            // at most.
            let end = ((((b as u64 + 1) << (32 - BITS)) * lines) >> 32) as usize + 1;
            let reach = (next.max(end * LINE) + k).min(total);
            if slots.len() < reach {
                slots.resize_with(reach, || AtomicU64::new(0));
            }
            let mut count = [[0u32; 1 << DIGIT]; 2];
            for e in bucket {
                let l = low(e);
                count[0][digit(l, 0)] += 1;
                count[1][digit(l, 1)] += 1;
            }
            for c in &mut count {
                let mut sum = 0;
                for x in c.iter_mut() {
                    (*x, sum) = (sum, sum + *x);
                }
            }
            let tmp = &mut tmp[..k];
            for e in bucket {
                let e = [low(e), u32_at(e, 4), u32_at(e, 8)];
                let c = &mut count[0][digit(e[0], 0)];
                tmp[*c as usize] = e;
                *c += 1;
            }
            let sorted = &mut sorted[..k];
            for e in tmp.iter() {
                let c = &mut count[1][digit(e[0], 1)];
                sorted[*c as usize] = *e;
                *c += 1;
            }
            // Unlike the first entry's.
            let mut last = sorted.first().map_or(0, |e| !e[0]);
            let spilled = spill.len();
            for (i, &[l, hi, id]) in sorted.iter().enumerate() {
                // An equal key has an equal hash, so it is among the ones
                // just before with the same low half.
                if l == last
                    && let Some(d) = equal_before(nodes, sorted, i)
                {
                    return Err(d);
                }
                last = l;
                // The first slot from its line on that is after the last
                // filled: the slots between are all in use, as a probe
                // needs.
                let at = next.max(((l as u64 * lines) >> 32) as usize * LINE);
                let tagged = tag_of((hi as u64) << 32) | id as u64;
                match slots.get_mut(at) {
                    Some(s) => {
                        *s.get_mut() = tagged;
                        next = at + 1;
                    }
                    None => spill.push(((hi as u64) << 32 | l as u64, id)),
                }
            }
            added += k - (spill.len() - spilled);
        }
        drop(map);
        slots.resize_with(total, || AtomicU64::new(0));
        let mut table = IdTable {
            slots: slots.into_boxed_slice(),
            lines: lines as usize,
            len: AtomicUsize::new(0),
        };
        table.add_len(added);
        for (h, id) in spill {
            let same = |o| nodes.get(o).same(nodes.get(id));
            if let Some(old) = table.insert_unique(h, same, id) {
                return Err((id.max(old), id.min(old)));
            }
        }
        self.table = table;
        Ok(())
    }

    /// Make room for `extra` more nodes without growing the table.
    pub fn reserve(&mut self, extra: usize) {
        if !self.table.has_room(extra) {
            self.grow(self.table.len() + extra);
        }
    }

    pub fn heap_bytes(&self) -> usize {
        self.nodes.heap_bytes() + self.table.heap_bytes()
    }
}

/// Whether entry `i` of `sorted` (hash halves and id, in hash order) is
/// a node equal to one before it: their ids (the later, the earlier).
#[cold]
#[inline(never)]
fn equal_before<T: Node>(nodes: &Slab<T>, sorted: &[[u32; 3]], i: usize) -> Option<(u32, u32)> {
    let [l, hi, id] = sorted[i];
    let node = nodes.get(id);
    for &[l2, hi2, other] in sorted[..i].iter().rev() {
        if l2 != l {
            break;
        }
        if hi2 == hi && nodes.get(other).same(node) {
            return Some((id.max(other), id.min(other)));
        }
    }
    None
}

/// The buckets of [`Big::index`]: entries of 12 bytes.
struct Entries(Option<memmap2::MmapMut>);

impl Entries {
    fn new(entries: usize) -> Entries {
        if entries == 0 {
            return Entries(None);
        }
        let m = memmap2::MmapMut::map_anon(12 * entries)
            .unwrap_or_else(|e| panic!("cannot map {} bytes: {e}", 12 * entries));
        // Fewer page faults (where the system has huge pages).
        #[cfg(target_os = "linux")]
        let _ = m.advise(memmap2::Advice::HugePage);
        Entries(Some(m))
    }

    fn ents(&mut self) -> &mut [[u8; 12]] {
        match &mut self.0 {
            Some(m) => m.as_chunks_mut::<12>().0,
            None => &mut [],
        }
    }

    /// Give back the pages of entries `r`, which are not read again.
    fn release(&mut self, r: std::ops::Range<usize>) {
        if let Some(m) = &mut self.0 {
            crate::slab::release_pages(&mut m[12 * r.start..12 * r.end]);
        }
    }
}

/// An entry of [`Entries`]: the hash's low and high halves, and the id.
#[inline(always)]
fn entry(h: u64, id: u32) -> [u8; 12] {
    let mut e = [0; 12];
    e[..8].copy_from_slice(&h.to_le_bytes());
    e[8..].copy_from_slice(&id.to_le_bytes());
    e
}

#[inline(always)]
fn u32_at(e: &[u8; 12], i: usize) -> u32 {
    u32::from_le_bytes(e[i..i + 4].try_into().expect("4 bytes"))
}

/// The low half of an entry's hash.
#[inline(always)]
fn low(e: &[u8; 12]) -> u32 {
    u32_at(e, 0)
}

/// Shards of the loader's locked tables (strings, level lists, big
/// literals).
pub const SHARDS: usize = 64;

/// The shard of a hash.
#[inline]
pub fn shard_of(h: u64) -> usize {
    (h >> 51) as usize & (SHARDS - 1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::name::{NameId, NameNode};

    fn names(n: u64) -> Big<NameNode> {
        let mut b = Big::new("names");
        for i in 0..n {
            b.push_unindexed(NameNode::Num(NameId(0), i)).expect("room");
        }
        b
    }

    /// Indexing on one thread (in hash order) and on several finds every
    /// node, and the same duplicate.
    #[test]
    fn index_finds_all_and_duplicates() {
        for threads in [1, 3] {
            let mut b = names(300_000);
            b.index(threads).expect("no duplicates");
            for i in (0..300_000).step_by(7) {
                assert_eq!(b.find(&NameNode::Num(NameId(0), i)), Some(i as u32));
            }
            assert_eq!(b.find(&NameNode::Num(NameId(1), 0)), None);
            // A node listed twice, far apart.
            let mut b = names(300_000);
            b.push_unindexed(NameNode::Num(NameId(0), 12_345))
                .expect("room");
            assert_eq!(b.index(threads), Err((300_000, 12_345)));
        }
    }
}
