//! Arrays that never move while read, in reserved address space, read with
//! one load and no bounds check.
//!
//! A [`Slab`] reserves room for [`CAP`] elements (`MAP_NORESERVE`: the
//! reservation costs no memory; a page is backed when first written) and
//! fills it from index 0 like a `Vec`, but it never reallocates, so its
//! base address stays fixed and an element is at `base + index`.
//!
//! Under a limit on address space (`ulimit -v`, or strict overcommit) that
//! reservation can fail. A slab then reserves less: a share of the limit,
//! and at least twice its elements, halving down to what it needs if even
//! that fails. It grows by remapping when pushed past half its mapping
//! (only through `&mut`, so nothing reads it while it may move), and a
//! [`Pool`] out of room tries to extend both mappings in place. Only the
//! cold paths change: reads are the same single load either way.
//!
//! Above a slab's elements, a [`Pool`] lends out blocks of [`BLOCK`]
//! indices to the checker's stores, one store per block at a time: a
//! store's own terms then live in the same array as the environment's,
//! and reading either is the same single load ([`Reader::get`]).
//!
//! All the `unsafe` code of the arenas is in this module. What makes it
//! sound:
//! - With the full reservation, the mapping is `CAP` elements long and
//!   every index is masked to `CAP - 1`, so no read or write leaves it.
//!   A reduced mapping holds the slab's elements and every block lent from
//!   it (pushing and lending check its size), and the rule below keeps
//!   reads inside those.
//! - Elements below `len` are only written through `&mut Slab`.
//! - A pool slot is only written through its [`Block`], and a block is
//!   lent to one holder at a time and cannot outlive the borrows of its
//!   slabs, so nothing can push onto them (or free or move them) while it
//!   exists. Its slots are above `len` when it is lent.
//! - The one rule the types do not enforce: an index read must be below
//!   `len`, or in a block that the reader holds (the ids a store makes
//!   come from its own blocks; debug builds check this at the store).
//!   and that its holder has written. Reading another holder's slot would
//!   race with its writes, and an index never written holds zero bytes,
//!   which need not be a value of the type.

#![allow(unsafe_code)]

use std::marker::PhantomData;
use std::ptr::NonNull;
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};

/// Index bits of a slab: ids are `u32`s below 2^31.
pub const CAP_BITS: u32 = 31;
/// Elements a slab has room for.
pub const CAP: usize = 1 << CAP_BITS;
const MASK: u32 = CAP as u32 - 1;

/// Index bits of a pool block.
pub const BLOCK_BITS: u32 = 16;
/// Indices per pool block.
pub const BLOCK: u32 = 1 << BLOCK_BITS;

/// Set once a full reservation has failed: later slabs go straight to the
/// reduced ones.
static FULL_FAILS: AtomicBool = AtomicBool::new(false);
/// Slab identities, for a pool's check that it lends from one pair.
static NEXT_ID: AtomicU32 = AtomicU32::new(1);

/// The address space a reduced slab first reserves, in bytes: a sixteenth
/// of the soft limit, or 2 GiB with no limit (strict overcommit).
fn reduced_share() -> usize {
    #[cfg(test)]
    if let Some(s) = tests::SHARE.get() {
        return s;
    }
    static SHARE: OnceLock<usize> = OnceLock::new();
    *SHARE.get_or_init(|| {
        let mut r = libc::rlimit {
            rlim_cur: 0,
            rlim_max: 0,
        };
        // SAFETY: plain syscall writing to `r`.
        let ok = unsafe { libc::getrlimit(libc::RLIMIT_AS, &mut r) } == 0;
        if ok && r.rlim_cur != libc::RLIM_INFINITY {
            usize::try_from(r.rlim_cur / 16).unwrap_or(usize::MAX)
        } else {
            2 << 30
        }
    })
}

/// A fresh anonymous mapping of `bytes`, if the system grants it.
fn map(bytes: usize) -> Option<NonNull<u8>> {
    // SAFETY: a new private anonymous mapping; touches no existing memory.
    let p = unsafe {
        libc::mmap(
            std::ptr::null_mut(),
            bytes,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_NORESERVE,
            -1,
            0,
        )
    };
    if p == libc::MAP_FAILED {
        return None;
    }
    // Fewer page faults and TLB misses; a hint only.
    // SAFETY: advice on the mapping just made.
    unsafe { libc::madvise(p, bytes, libc::MADV_HUGEPAGE) };
    NonNull::new(p.cast())
}

/// The mapping at `p` of `old` bytes, resized to `new` (moved if `may_move`).
///
/// # Safety
/// `p` and `old` must be a mapping this module made, and if `may_move`,
/// nothing may hold a pointer into it.
unsafe fn remap(p: NonNull<u8>, old: usize, new: usize, may_move: bool) -> Option<NonNull<u8>> {
    let flags = if may_move { libc::MREMAP_MAYMOVE } else { 0 };
    // SAFETY: by the caller's contract.
    let q = unsafe { libc::mremap(p.as_ptr().cast(), old, new, flags) };
    if q == libc::MAP_FAILED {
        return None;
    }
    // SAFETY: advice on the mapping just resized.
    unsafe { libc::madvise(q, new, libc::MADV_HUGEPAGE) };
    NonNull::new(q.cast())
}

/// An array of up to [`CAP`] elements that never moves while borrowed.
pub struct Slab<T: Copy> {
    base: NonNull<T>,
    len: usize,
    /// `push` takes its slow path at this length: `CAP` for the full
    /// reservation, else about half the mapping (room for blocks above).
    room: usize,
    /// Elements the mapping holds: 0 before reserving, `CAP` for the full
    /// reservation. Changed through `&mut`, or by the slab's pool under its
    /// lock (in place, in `Pool::take`).
    cap: AtomicUsize,
    /// Identity for the pool's check; 0 before reserving.
    id: u32,
    /// Whether a pool lends blocks of this slab.
    pooled: AtomicBool,
    _t: PhantomData<T>,
}

// SAFETY: a slab owns its elements like a `Vec`; shared access only reads
// them, except through a pool's blocks, which are exclusive (see the
// module comment).
unsafe impl<T: Copy + Send> Send for Slab<T> {}
// SAFETY: as above.
unsafe impl<T: Copy + Sync> Sync for Slab<T> {}

impl<T: Copy> Default for Slab<T> {
    fn default() -> Self {
        Slab {
            base: NonNull::dangling(),
            len: 0,
            room: 0,
            cap: AtomicUsize::new(0),
            id: 0,
            pooled: AtomicBool::new(false),
            _t: PhantomData,
        }
    }
}

impl<T: Copy> Drop for Slab<T> {
    fn drop(&mut self) {
        let cap = *self.cap.get_mut();
        if cap > 0 {
            // SAFETY: the slab's own mapping, which nothing borrows now.
            unsafe { libc::munmap(self.base.as_ptr().cast(), cap * size_of::<T>()) };
        }
    }
}

impl<T: Copy> Slab<T> {
    const SIZED: () = assert!(size_of::<T>() > 0, "a slab of a sized type");

    /// An empty slab with its range reserved.
    pub fn new() -> Self {
        let mut s = Self::default();
        s.grow(0);
        s
    }

    /// Make room for `need` elements: reserve the full range, or else a
    /// reduced mapping (see the module comment), or grow the reduced one.
    #[cold]
    #[inline(never)]
    fn grow(&mut self, need: usize) {
        let () = Self::SIZED;
        assert!(need <= CAP, "slab full");
        let size = size_of::<T>();
        let cap = *self.cap.get_mut();
        #[cfg(test)]
        let full = tests::SHARE.get().is_none();
        #[cfg(not(test))]
        let full = true;
        if cap == 0 && full && !FULL_FAILS.load(Ordering::Relaxed) {
            if let Some(p) = map(CAP * size) {
                self.reserved(p, CAP, CAP);
                return;
            }
            FULL_FAILS.store(true, Ordering::Relaxed);
        }
        let need = need.max(1);
        let share = (reduced_share() / size).max(BLOCK as usize);
        let want = (2 * need)
            .next_power_of_two()
            .max(1 << share.ilog2())
            .min(CAP);
        if want <= cap {
            self.room = (cap / 2).max(need);
            return;
        }
        let mut c = want;
        loop {
            let got = if cap == 0 {
                map(c * size)
            } else {
                // SAFETY: the slab's own mapping; `&mut self` excludes every
                // borrow (no reader, no block), so it may move.
                unsafe { remap(self.base.cast(), cap * size, c * size, true) }
            };
            if let Some(p) = got {
                self.reserved(p, c, (c / 2).max(need));
                return;
            }
            if c == need {
                panic!(
                    "nitrolean: resource limit: out of address space for {} MiB of terms",
                    (need * size) >> 20
                );
            }
            c = (c / 2).max(need);
        }
    }

    fn reserved(&mut self, p: NonNull<u8>, cap: usize, room: usize) {
        self.base = p.cast();
        *self.cap.get_mut() = cap;
        self.room = room;
        if self.id == 0 {
            self.id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
        }
    }

    /// Extend the mapping in place (it must not move: it may be read) to
    /// hold at least `need` elements, for a pool out of room. Called under
    /// the slab's pool's lock only.
    fn grow_in_place(&self, need: usize) -> bool {
        let cap = self.cap.load(Ordering::Relaxed);
        if need <= cap {
            return true;
        }
        if need > CAP {
            return false;
        }
        let size = size_of::<T>();
        let mut c = (2 * cap).max(need).min(CAP);
        loop {
            // SAFETY: the slab's own mapping, not moved; the pool's lock and
            // the slab's borrow exclude any other change to it.
            if unsafe { remap(self.base.cast(), cap * size, c * size, false) }.is_some() {
                self.cap.store(c, Ordering::Relaxed);
                return true;
            }
            if c == need {
                return false;
            }
            c = (cap + (c - cap) / 2).max(need);
        }
    }

    /// The elements of `chunks`, in order.
    pub fn from_chunks(chunks: Vec<Vec<T>>) -> Self {
        let mut s = Self::default();
        s.grow(chunks.iter().map(Vec::len).sum());
        for c in chunks {
            s.extend_from_slice(&c);
        }
        s
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Element `i`, which must be below `len`.
    #[inline]
    pub fn get(&self, i: u32) -> &T {
        debug_assert!((i as usize) < self.len, "slab index {i} out of bounds");
        // SAFETY: the masked index is inside the mapping (an empty slab
        // has no elements to ask for: see the assertion), the element is
        // below `len` and so only changes through `&mut self`.
        unsafe { &*self.base.as_ptr().add((i & MASK) as usize) }
    }

    /// A reader of this slab's elements and of the blocks lent from it.
    #[inline]
    pub fn reader(&self) -> Reader<'_, T> {
        Reader {
            base: self.base,
            _s: PhantomData,
        }
    }

    /// Push `v`, unless the slab is full (then false).
    #[inline]
    pub fn try_push(&mut self, v: T) -> bool {
        if self.len >= CAP {
            return false;
        }
        self.push(v);
        true
    }

    #[inline]
    pub fn push(&mut self, v: T) {
        if self.len >= self.room {
            self.grow(self.len + 1);
        }
        // SAFETY: `len < room <= cap` is inside the mapping, and `&mut self`
        // excludes every other access (no block is lent while it is
        // borrowed mutably).
        unsafe { self.base.as_ptr().add(self.len).write(v) };
        self.len += 1;
    }

    pub fn extend_from_slice(&mut self, vs: &[T]) {
        if vs.len() > self.room - self.len {
            self.grow(self.len.saturating_add(vs.len()));
        }
        // SAFETY: as in `push`; the source is a separate allocation.
        unsafe {
            std::ptr::copy_nonoverlapping(vs.as_ptr(), self.base.as_ptr().add(self.len), vs.len())
        };
        self.len += vs.len();
    }

    /// Set element `i`, which must be below `len`.
    #[inline]
    pub fn set(&mut self, i: u32, v: T) {
        debug_assert!((i as usize) < self.len, "slab index {i} out of bounds");
        // SAFETY: as in `get`, with `&mut self` exclusive.
        unsafe { self.base.as_ptr().add((i & MASK) as usize).write(v) };
    }

    /// Push copies of `v` until there are `n` elements.
    pub fn fill_to(&mut self, n: usize, v: T) {
        if self.len >= n {
            return;
        }
        if n > self.room {
            self.grow(n);
        }
        let base = self.base.as_ptr();
        for i in self.len..n {
            // SAFETY: as in `push`: `i < n <= room <= cap` is inside the
            // mapping.
            unsafe { base.add(i).write(v) };
        }
        self.len = n;
    }

    pub fn as_slice(&self) -> &[T] {
        if self.len == 0 {
            return &[];
        }
        // SAFETY: elements `0..len` are initialized and inside the mapping.
        unsafe { std::slice::from_raw_parts(self.base.as_ptr(), self.len) }
    }

    /// Memory the elements take (the reservation costs none).
    pub fn heap_bytes(&self) -> usize {
        self.len * size_of::<T>()
    }
}

/// Reads a slab's elements by index: one load, unchecked (see the module
/// comment for what the index must be).
#[derive(Clone, Copy)]
pub struct Reader<'s, T: Copy> {
    base: NonNull<T>,
    _s: PhantomData<&'s Slab<T>>,
}

impl<T: Copy> Reader<'_, T> {
    #[inline(always)]
    pub fn get(self, i: u32) -> T {
        // SAFETY: the masked index is inside the mapping, which the
        // borrow keeps alive. By the module's rule the element is below
        // the slab's `len` (immutable while borrowed) or in a block the
        // caller holds and has written (written only by the caller).
        // A reader of an empty, unreserved slab is never read from: it
        // has no elements and no blocks.
        unsafe { self.base.as_ptr().add((i & MASK) as usize).read() }
    }
}

/// Lends blocks of indices above two slabs' elements (an arena's nodes
/// and their data, which share ids), one holder per block at a time.
#[derive(Default)]
pub struct Pool {
    state: Mutex<PoolState>,
}

#[derive(Default)]
struct PoolState {
    /// The slabs this pool lends from (their ids), set at the first loan.
    bound: Option<(u32, u32)>,
    /// The first block never lent.
    next: u32,
    /// Blocks given back.
    free: Vec<u32>,
}

impl Pool {
    /// A block of [`BLOCK`] unused indices of `a` and `b`, if any are
    /// left. A pool lends from one pair of slabs only, and a slab is
    /// lent from by one pool only.
    pub fn take<'p, A: Copy, B: Copy>(
        &'p self,
        a: &'p Slab<A>,
        b: &'p Slab<B>,
    ) -> Option<Block<'p, A, B>> {
        assert!(a.id != 0 && b.id != 0, "a pool lends from reserved slabs");
        let bases = (a.id, b.id);
        let mut st = self.state.lock().expect("pool");
        match st.bound {
            Some(x) => assert_eq!(x, bases, "a pool lends from one pair of slabs"),
            None => {
                for p in [&a.pooled, &b.pooled] {
                    assert!(
                        !p.swap(true, Ordering::Relaxed),
                        "a slab is lent from by one pool"
                    );
                }
                st.bound = Some(bases);
            }
        }
        // Blocks start above both slabs' elements. The slabs may have
        // grown since a block was given back (no block was out then).
        let floor = a.len.max(b.len).div_ceil(BLOCK as usize) as u32;
        st.free.retain(|&k| k >= floor);
        st.next = st.next.max(floor);
        let k = match st.free.pop() {
            Some(k) => k,
            None => {
                // A reduced mapping may be out of room: extend both in
                // place (blocks are out, so they cannot move).
                let need = (st.next as usize + 1) << BLOCK_BITS;
                if !(a.grow_in_place(need) && b.grow_in_place(need)) {
                    return None;
                }
                st.next += 1;
                st.next - 1
            }
        };
        Some(Block {
            first: k << BLOCK_BITS,
            a: a.base,
            b: b.base,
            pool: self,
            _s: PhantomData,
        })
    }
}

/// [`BLOCK`] indices of two slabs, lent to one holder: given back when
/// dropped.
pub struct Block<'p, A: Copy, B: Copy> {
    first: u32,
    a: NonNull<A>,
    b: NonNull<B>,
    pool: &'p Pool,
    _s: PhantomData<(&'p Slab<A>, &'p Slab<B>)>,
}

// SAFETY: the block's slots belong to its holder alone; sending the block
// sends that right.
unsafe impl<A: Copy + Send, B: Copy + Send> Send for Block<'_, A, B> {}

impl<A: Copy, B: Copy> Block<'_, A, B> {
    /// The block's first index.
    #[inline]
    pub fn first(&self) -> u32 {
        self.first
    }

    /// Whether `i` is one of the block's indices.
    #[inline]
    pub fn contains(&self, i: u32) -> bool {
        i >> BLOCK_BITS == self.first >> BLOCK_BITS
    }

    /// Write the elements at index `first + slot` of both slabs.
    #[inline]
    pub fn put(&mut self, slot: u32, x: A, y: B) {
        debug_assert!(slot < BLOCK);
        let i = ((self.first | (slot & (BLOCK - 1))) & MASK) as usize;
        // SAFETY: the index is inside both mappings (masked), above both
        // slabs' elements (see `Pool::take`; they cannot grow while the
        // block borrows them), and in this block, which no one else holds.
        unsafe {
            self.a.as_ptr().add(i).write(x);
            self.b.as_ptr().add(i).write(y);
        }
    }
}

impl<A: Copy, B: Copy> Drop for Block<'_, A, B> {
    fn drop(&mut self) {
        if let Ok(mut st) = self.pool.state.lock() {
            st.free.push(self.first >> BLOCK_BITS);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    thread_local! {
        /// Slabs made on this thread take the reduced path, with this share.
        pub(super) static SHARE: Cell<Option<usize>> = const { Cell::new(None) };
    }

    /// A reduced slab grows (moving) as it is pushed, keeps its elements,
    /// and leaves room above them for blocks.
    #[test]
    fn reduced_slab_grows() {
        SHARE.set(Some(4 << 20));
        let mut a: Slab<u32> = Slab::new();
        let mut b: Slab<u64> = Slab::default();
        SHARE.set(None);
        assert_eq!(a.cap.load(Ordering::Relaxed), 1 << 20);
        assert_eq!(a.room, 1 << 19);
        SHARE.set(Some(4 << 20));
        let n = 3_000_000;
        for i in 0..n {
            a.push(i);
            b.push(u64::from(i) * 3);
        }
        a.extend_from_slice(&[7; 100]);
        SHARE.set(None);
        assert!(a.cap.load(Ordering::Relaxed) >= 2 * a.len());
        assert!(a.cap.load(Ordering::Relaxed) < CAP);
        assert!((0..n).all(|i| *a.get(i) == i && *b.get(i) == u64::from(i) * 3));
        assert_eq!(*a.get(n + 99), 7);
        let pool = Pool::default();
        let (ra, rb) = (a.reader(), b.reader());
        let mut held = Vec::new();
        for _ in 0..8 {
            let mut k = pool.take(&a, &b).expect("room above the elements");
            assert!(k.first() as usize >= a.len().max(b.len()));
            k.put(5, 1, 2);
            assert_eq!((ra.get(k.first() + 5), rb.get(k.first() + 5)), (1, 2));
            held.push(k);
        }
    }

    /// A reduced mapping with free space above it extends in place: its
    /// base and elements stay.
    #[test]
    fn reduced_slab_grows_in_place() {
        SHARE.set(Some(1 << 20));
        let mut a: Slab<u32> = Slab::new();
        SHARE.set(None);
        a.push(42);
        let cap = a.cap.load(Ordering::Relaxed);
        let base = a.base;
        // Free the upper half of the mapping, then grow back into it.
        // SAFETY: the slab's own mapping, above its one element.
        unsafe { libc::munmap(base.as_ptr().add(cap / 2).cast(), cap / 2 * 4) };
        *a.cap.get_mut() = cap / 2;
        assert!(a.grow_in_place(cap));
        assert_eq!((a.cap.load(Ordering::Relaxed), a.base), (cap, base));
        assert_eq!(*a.get(0), 42);
    }

    /// A pool out of a reduced slab's room extends it in place, or else
    /// returns `None`; given back blocks are lent again.
    #[test]
    fn reduced_pool_runs_out_cleanly() {
        SHARE.set(Some(1 << 20));
        let (a, b): (Slab<u32>, Slab<u32>) = (Slab::new(), Slab::new());
        SHARE.set(None);
        let pool = Pool::default();
        assert_eq!(a.cap.load(Ordering::Relaxed), 4 * BLOCK as usize);
        let mut held = Vec::new();
        // Taken until none is left, or (extended in place) a few more.
        while held.len() < 64
            && let Some(mut k) = pool.take(&a, &b)
        {
            k.put(BLOCK - 1, 1, 1);
            held.push(k);
        }
        let cap = a
            .cap
            .load(Ordering::Relaxed)
            .min(b.cap.load(Ordering::Relaxed));
        assert!(held.len() >= 4);
        if held.len() < 64 {
            assert_eq!(held.len(), cap >> BLOCK_BITS);
        } else {
            assert!(cap >= 64 << BLOCK_BITS);
        }
        let first = held.pop().expect("a block").first();
        assert_eq!(pool.take(&a, &b).expect("given back").first(), first);
    }

    #[test]
    fn push_and_lend() {
        let mut a: Slab<u32> = Slab::new();
        let mut b: Slab<u32> = Slab::new();
        for i in 0..100 {
            a.push(i);
            b.push(2 * i);
        }
        assert_eq!(*a.get(42), 42);
        assert_eq!(b.as_slice()[7], 14);
        let pool = Pool::default();
        let (ra, rb) = (a.reader(), b.reader());
        let mut k = pool.take(&a, &b).expect("a block");
        assert!(k.first() >= 100);
        k.put(3, 7, 8);
        assert_eq!((ra.get(k.first() + 3), rb.get(k.first() + 3)), (7, 8));
        let first = k.first();
        drop(k);
        let k2 = pool.take(&a, &b).expect("a block");
        assert_eq!(k2.first(), first, "given back blocks are lent again");
        drop(k2);
        // Grown past the block: the next loan is above the elements.
        a.fill_to(first as usize + 10, 0);
        let k3 = pool.take(&a, &b).expect("a block");
        assert!(k3.first() as usize >= a.len());
    }

    #[test]
    #[should_panic(expected = "one pool")]
    fn one_pool_per_slab() {
        let (a, b): (Slab<u32>, Slab<u32>) = (Slab::new(), Slab::new());
        let (p, q) = (Pool::default(), Pool::default());
        let _k = p.take(&a, &b);
        let _l = q.take(&a, &b);
    }
}
