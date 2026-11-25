//! Concurrent hash-consing arenas, used while loading `.olean` files.
//!
//! Worker threads intern modules into these arenas at the same time; at the
//! end [`Par::finish`] turns them into the environment's [`Names`],
//! [`Levels`] and [`Exprs`], handing the expression and name tables over as
//! they are (no rehashing) and converting the node stores chunk by chunk,
//! on all threads.
//!
//! An arena ([`Conc`]) is an [`IdTable`] (lock-free: a slot is claimed with
//! one compare-and-swap) and a store from id to node, written before the id
//! is published in the table. Each thread takes ids in blocks of
//! [`ID_BLOCK`] ([`Cursor`]), so threads do not contend on a counter; ids
//! left unused at the end of a block, or taken for a node another thread
//! added first, hold a placeholder that no term refers to. Inserts run in
//! batches of at most [`BATCH`] nodes under a read lock of the table; a
//! batch that might fill the table first grows it under the write lock.
//! Node equality is [`Node::same`] and the hash is [`Node::hash`], so a
//! table finds exactly what the sequential arena's would.

use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock, RwLock};

use hashbrown::HashTable;
use num_bigint::BigUint;

use crate::expr::{BigId, ExprData, ExprId, ExprNode, Exprs, LetBinder, LetId};
use crate::hash::hash_bytes;
use crate::intern::{Big, CHUNK, CHUNK_BITS, IdTable, Interner, Node, SHARDS, shard_of};
use crate::level::{LevelId, LevelList, LevelNode, Levels};
use crate::name::{NameId, NameNode, Names};
use crate::slab::Slab;
use crate::strings::{Overflow, StrId, StrPool};

const MAX_CHUNKS: usize = 1 << (32 - CHUNK_BITS);

/// Ids a thread takes at once.
pub const ID_BLOCK: u32 = 1024;

/// Most inserts per read lock of a table.
pub const BATCH: usize = 1 << 14;

/// Probes issued together, so that their cache misses overlap.
const GROUP: usize = 16;

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

/// A thread's current block of ids in one arena.
#[derive(Default)]
pub struct Cursor {
    next: u32,
    end: u32,
}

/// Write-once storage of a packed node and a side word per id, in lazily
/// allocated chunks of [`CHUNK`] ids.
struct Store {
    words: Vec<OnceLock<Box<[AtomicU64]>>>,
    side: Vec<OnceLock<Box<[AtomicU32]>>>,
}

impl Store {
    fn new() -> Self {
        Store {
            words: (0..MAX_CHUNKS).map(|_| OnceLock::new()).collect(),
            side: (0..MAX_CHUNKS).map(|_| OnceLock::new()).collect(),
        }
    }

    #[inline]
    fn words(&self, id: u32) -> &[AtomicU64] {
        let c = self.words[(id >> CHUNK_BITS) as usize]
            .get_or_init(|| (0..2 * CHUNK).map(|_| AtomicU64::new(0)).collect());
        let o = (id as usize & (CHUNK - 1)) * 2;
        &c[o..o + 2]
    }

    #[inline]
    fn side_cell(&self, id: u32) -> &AtomicU32 {
        let c = self.side[(id >> CHUNK_BITS) as usize]
            .get_or_init(|| (0..CHUNK).map(|_| AtomicU32::new(0)).collect());
        &c[id as usize & (CHUNK - 1)]
    }

    #[inline]
    fn set(&self, id: u32, w: [u64; 2], side: u32) {
        let c = self.words(id);
        c[0].store(w[0], Ordering::Relaxed);
        c[1].store(w[1], Ordering::Relaxed);
        if side != 0 {
            self.side_cell(id).store(side, Ordering::Relaxed);
        }
    }

    #[inline]
    fn get(&self, id: u32) -> [u64; 2] {
        let c = self.words(id);
        [c[0].load(Ordering::Relaxed), c[1].load(Ordering::Relaxed)]
    }
}

/// A concurrent arena of packable nodes, with a `u32` of side data each.
pub(crate) struct Conc<T> {
    table: RwLock<IdTable>,
    store: Store,
    /// The next unallocated block.
    next: AtomicU32,
    /// Room kept free in the table for the batches in flight.
    slack: usize,
    what: &'static str,
    _t: std::marker::PhantomData<T>,
}

impl<T: Pack> Conc<T> {
    /// An arena with room for about `n` nodes before the table grows, for
    /// `threads` inserting threads.
    fn new(what: &'static str, n: usize, threads: usize) -> Self {
        let slack = threads.max(1) * BATCH;
        Conc {
            table: RwLock::new(IdTable::with_capacity(n + slack)),
            store: Store::new(),
            next: AtomicU32::new(0),
            slack,
            what,
            _t: std::marker::PhantomData,
        }
    }

    /// Ids handed out so far (including unused ones).
    pub fn len(&self) -> usize {
        self.next.load(Ordering::Acquire) as usize
    }

    #[inline]
    pub fn get(&self, id: u32) -> T {
        T::unpack(self.store.get(id))
    }

    fn alloc(&self, cur: &mut Cursor) -> Result<u32, Overflow> {
        if cur.next == cur.end {
            let b = self.next.fetch_add(ID_BLOCK, Ordering::AcqRel);
            if b >= u32::MAX - 2 * ID_BLOCK {
                self.next.store(u32::MAX - 2 * ID_BLOCK, Ordering::Release);
                return Err(Overflow(self.what));
            }
            cur.next = b;
            cur.end = b + ID_BLOCK;
        }
        let id = cur.next;
        cur.next += 1;
        Ok(id)
    }

    /// Run `f` with the table, after making room for `n` (at most
    /// [`BATCH`]) inserts.
    fn batch<R>(&self, n: usize, f: impl FnOnce(&IdTable) -> R) -> R {
        debug_assert!(n <= BATCH);
        {
            let t = self.table.read().expect("table lock");
            if t.has_room(n + self.slack) {
                return f(&t);
            }
        }
        {
            let mut t = self.table.write().expect("table lock");
            if !t.has_room(n + self.slack) {
                let want = (t.len() + n + self.slack) * 2;
                let grown = t.grown(want, |id| self.get(id).hash());
                *t = grown;
            }
        }
        let t = self.table.read().expect("table lock");
        f(&t)
    }

    /// Intern one node in a batch.
    #[inline]
    fn put(
        &self,
        t: &IdTable,
        cur: &mut Cursor,
        node: T,
        h: u64,
        side: u32,
        added: &mut usize,
    ) -> Result<u32, Overflow> {
        let mut err = None;
        let mut made = None;
        let (id, fresh) = t.insert_shared(
            h,
            |id| self.get(id).same(&node),
            || match self.alloc(cur) {
                Ok(id) => {
                    self.store.set(id, node.pack(), side);
                    made = Some(id);
                    id
                }
                Err(e) => {
                    err = Some(e);
                    // Never published: the error is returned below.
                    u32::MAX
                }
            },
        );
        if let Some(e) = err {
            return Err(e);
        }
        if fresh {
            *added += 1;
        } else if let Some(m) = made {
            // Another thread added an equal node first: leave a
            // placeholder in the unused id.
            self.store.set(m, [0, 0], 0);
        }
        Ok(id)
    }

    /// Intern `nodes` with their side data, appending their ids to `out`.
    /// The nodes must not depend on each other.
    pub fn intern_all(
        &self,
        cur: &mut Cursor,
        nodes: &[(T, u32)],
        out: &mut Vec<u32>,
    ) -> Result<(), Overflow> {
        for part in nodes.chunks(BATCH) {
            let r = self.batch(part.len(), |t| {
                let mut added = 0;
                let mut res = Ok(());
                'groups: for g in part.chunks(GROUP) {
                    let mut hs = [0u64; GROUP];
                    let mut acc = 0u64;
                    for (i, (n, _)) in g.iter().enumerate() {
                        hs[i] = n.hash();
                        acc = acc.wrapping_add(t.touch(hs[i]));
                    }
                    std::hint::black_box(acc);
                    for (i, &(n, side)) in g.iter().enumerate() {
                        match self.put(t, cur, n, hs[i], side, &mut added) {
                            Ok(id) => out.push(id),
                            Err(e) => {
                                res = Err(e);
                                break 'groups;
                            }
                        }
                    }
                }
                t.add_len(added);
                res
            });
            r?;
        }
        Ok(())
    }

    /// Intern one node.
    pub fn intern(&self, cur: &mut Cursor, node: T, side: u32) -> Result<u32, Overflow> {
        self.batch(1, |t| {
            let mut added = 0;
            let r = self.put(t, cur, node, node.hash(), side, &mut added);
            t.add_len(added);
            r
        })
    }

    /// The table, and the nodes and side data in id order, converted on
    /// `threads` threads chunk by chunk (each chunk of the store is freed
    /// once converted).
    fn into_parts<N: Send, S: Send>(
        self,
        threads: usize,
        node: impl Fn([u64; 2]) -> N + Sync,
        side: impl Fn(u32) -> S + Sync,
    ) -> (IdTable, Vec<Vec<N>>, Vec<Vec<S>>, usize) {
        let n = self.len();
        let nchunks = n.div_ceil(CHUNK);
        let Conc { table, store, .. } = self;
        let table = table.into_inner().expect("table lock");
        let words: Vec<Mutex<Option<Box<[AtomicU64]>>>> = store
            .words
            .into_iter()
            .take(nchunks)
            .map(|c| Mutex::new(c.into_inner()))
            .collect();
        let sides: Vec<Mutex<Option<Box<[AtomicU32]>>>> = store
            .side
            .into_iter()
            .take(nchunks)
            .map(|c| Mutex::new(c.into_inner()))
            .collect();
        let out: Vec<Mutex<(Vec<N>, Vec<S>)>> = (0..nchunks)
            .map(|_| Mutex::new((Vec::new(), Vec::new())))
            .collect();
        let next = std::sync::atomic::AtomicUsize::new(0);
        let convert = || {
            loop {
                let c = next.fetch_add(1, Ordering::Relaxed);
                if c >= nchunks {
                    break;
                }
                let len = (n - c * CHUNK).min(CHUNK);
                let w = words[c].lock().expect("chunk").take();
                let ns: Vec<N> = match &w {
                    Some(w) => w[..2 * len]
                        .as_chunks::<2>()
                        .0
                        .iter()
                        .map(|p| node([p[0].load(Ordering::Relaxed), p[1].load(Ordering::Relaxed)]))
                        .collect(),
                    None => (0..len).map(|_| node([0, 0])).collect(),
                };
                drop(w);
                let sd = sides[c].lock().expect("chunk").take();
                let ss: Vec<S> = match &sd {
                    Some(s) => s[..len]
                        .iter()
                        .map(|x| side(x.load(Ordering::Relaxed)))
                        .collect(),
                    None => (0..len).map(|_| side(0)).collect(),
                };
                drop(sd);
                *out[c].lock().expect("chunk") = (ns, ss);
            }
        };
        if threads <= 1 || nchunks <= 1 {
            convert();
        } else {
            std::thread::scope(|s| {
                for _ in 0..threads.min(nchunks) {
                    s.spawn(convert);
                }
            });
        }
        let (nodes, sides): (Vec<Vec<N>>, Vec<Vec<S>>) = out
            .into_iter()
            .map(|m| m.into_inner().expect("chunk"))
            .unzip();
        (table, nodes, sides, n)
    }
}

/// A worker's cursors, one per arena.
#[derive(Default)]
pub struct Local {
    pub names: Cursor,
    pub exprs: Cursor,
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
    /// Levels and level lists are few: one lock is enough.
    levels: Mutex<Levels>,
    /// Side data: the `ExprData` bits.
    pub(crate) exprs: Conc<ExprNode>,
    lets: Mutex<Interner<LetBinder>>,
    bigs: ConcVals<BigUint>,
}

impl Par {
    /// Arenas sized for `bytes` of `.olean` files and `threads` threads.
    /// Lean's files hold about one distinct expression per 70 bytes and
    /// one name per 1300 (Init, Std and Mathlib); the tables grow past that
    /// if needed. Every node comes from an object of at least 16 bytes, so
    /// there are fewer than `bytes / 16` of each kind (plus the few made
    /// here).
    pub fn new(bytes: u64, threads: usize) -> Self {
        let b = usize::try_from(bytes).unwrap_or(usize::MAX);
        let max = b / 16 + 16;
        let p = Par {
            strs: ConcVals::new("string pool exceeds 4 GiB", max),
            names: Conc::new("too many names", b / 1300, threads),
            levels: Mutex::new(Levels::new()),
            exprs: Conc::new("too many expressions", b / 80, threads),
            lets: Mutex::new(Interner::new("too many let binders")),
            bigs: ConcVals::new("too many big literals", max),
        };
        // Id 0 is the anonymous name, the zero level and the empty list,
        // as in the sequential arenas.
        let mut loc = Local::default();
        let anon = p
            .names
            .intern(&mut loc.names, NameNode::Anon, 0)
            .expect("empty");
        debug_assert!(anon == 0);
        p
    }

    pub fn str(&self, s: &str) -> Result<StrId, Overflow> {
        let h = hash_bytes(s.as_bytes());
        let id = self
            .strs
            .intern(s, h, || s.into(), |v| hash_bytes(v.as_bytes()))?;
        Ok(StrId(id))
    }

    /// Intern independent names (none a prefix of another).
    pub fn names(
        &self,
        loc: &mut Local,
        ns: &[(NameNode, u32)],
        out: &mut Vec<u32>,
    ) -> Result<(), Overflow> {
        self.names.intern_all(&mut loc.names, ns, out)
    }

    /// Intern a level; also says whether it has a parameter.
    pub fn level(&self, l: LevelNode) -> Result<(LevelId, bool), Overflow> {
        let mut ls = self.levels.lock().expect("levels lock");
        let (id, _) = ls.intern(l)?;
        Ok((id, ls.has_param(id)))
    }

    /// Intern a level list; also says whether a level has a parameter.
    pub fn list(&self, l: &[LevelId]) -> Result<(LevelList, bool), Overflow> {
        let mut ls = self.levels.lock().expect("levels lock");
        let id = ls.intern_list(l)?;
        Ok((id, ls.list_has_param(id)))
    }

    pub fn let_binder(&self, b: LetBinder) -> Result<LetId, Overflow> {
        let (id, _) = self.lets.lock().expect("lets lock").intern(b)?;
        Ok(LetId(id))
    }

    pub fn nat_big(&self, n: &BigUint) -> Result<BigId, Overflow> {
        let h = crate::expr::big_hash(n);
        let id = self
            .bigs
            .intern(n, h, || Box::new(n.clone()), crate::expr::big_hash)?;
        Ok(BigId(id))
    }

    /// Intern independent expressions (none a subterm of another) with
    /// their data.
    pub fn exprs(
        &self,
        loc: &mut Local,
        es: &[(ExprNode, u32)],
        out: &mut Vec<u32>,
    ) -> Result<(), Overflow> {
        self.exprs.intern_all(&mut loc.exprs, es, out)
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

    /// The environment's arenas, with the same ids. The expression and
    /// name stores are converted on `threads` threads; their tables are
    /// handed over as they are.
    pub fn finish(self, threads: usize) -> Result<(Names, Levels, Exprs), Overflow> {
        let Par {
            strs,
            names,
            levels,
            exprs,
            lets,
            bigs,
        } = self;
        let mut pool = StrPool::new();
        for i in 0..strs.len() as u32 {
            let id = pool.intern(strs.get(i))?;
            debug_assert_eq!(id.0, i);
        }
        drop(strs);
        let (ntable, nnodes, _, _) = names.into_parts(threads, NameNode::unpack, |_| ());
        let ns = Names::from_parts(
            Big::from_parts(Slab::from_chunks(nnodes), ntable, "too many names"),
            pool,
        );
        let ls = levels.into_inner().expect("levels lock");
        let li = lets.into_inner().expect("lets lock");
        let bigs: Vec<BigUint> = (0..bigs.len() as u32)
            .map(|i| bigs.get(i).clone())
            .collect();
        let (etable, enodes, edata, _) =
            exprs.into_parts(threads, ExprNode::unpack, ExprData::from_bits);
        let es = Exprs::from_parts(
            Slab::from_chunks(enodes),
            etable,
            Slab::from_chunks(edata),
            li,
            bigs,
        );
        Ok((ns, ls, es))
    }
}
