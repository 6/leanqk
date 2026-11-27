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
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicUsize, Ordering};
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
    /// Once the slab has views (see [`Slab::alias`]): the mapping, which
    /// the last of them, or the slab, unmaps.
    shared: Option<std::sync::Arc<Mapping>>,
    /// A view's own elements, or for a slab with views the most any view
    /// has: only [`Slab::store_shared`] writes below it.
    frozen: usize,
    /// Whether this is a view.
    view: bool,
    _t: PhantomData<T>,
}

/// A mapping that views share: unmapped when the last one goes.
struct Mapping {
    base: NonNull<u8>,
    bytes: usize,
}

// SAFETY: the mapping is only unmapped, by the last owner.
unsafe impl Send for Mapping {}
// SAFETY: as above.
unsafe impl Sync for Mapping {}

impl Drop for Mapping {
    fn drop(&mut self) {
        // SAFETY: a mapping of this module's, which no slab or view refers
        // to any more.
        unsafe { libc::munmap(self.base.as_ptr().cast(), self.bytes) };
    }
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
            shared: None,
            frozen: 0,
            view: false,
            _t: PhantomData,
        }
    }
}

impl<T: Copy> Drop for Slab<T> {
    fn drop(&mut self) {
        let cap = *self.cap.get_mut();
        if cap > 0 && self.shared.is_none() {
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
        assert!(!self.view, "nothing is pushed onto a view");
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
        if self.len >= self.room {
            if self.len >= CAP {
                return false;
            }
            self.grow(self.len + 1);
        }
        // SAFETY: as in `push`.
        unsafe { self.base.as_ptr().add(self.len).write(v) };
        self.len += 1;
        true
    }

    #[inline(always)]
    pub fn push(&mut self, v: T) {
        let len = self.len;
        if len >= self.room {
            self.grow(len + 1);
        }
        // SAFETY: `len < room <= cap` is inside the mapping, and `&mut self`
        // excludes every other access (no block is lent while it is
        // borrowed mutably).
        unsafe { self.base.as_ptr().add(len).write(v) };
        self.len = len + 1;
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

    #[inline(always)]
    pub fn as_slice(&self) -> &[T] {
        // SAFETY: elements `0..len` are initialized and inside the mapping
        // (with none, `base` is still aligned and not null).
        unsafe { std::slice::from_raw_parts(self.base.as_ptr(), self.len) }
    }

    /// Memory the elements take (the reservation costs none; a view's are
    /// its slab's).
    pub fn heap_bytes(&self) -> usize {
        if self.view {
            return 0;
        }
        self.len * size_of::<T>()
    }

    /// Whether this slab has the full reservation, so that it never moves
    /// (and may have views: see [`Slab::alias`]).
    pub fn is_fixed(&self) -> bool {
        self.cap.load(Ordering::Relaxed) == CAP
    }

    /// A view of the first `len` elements (at most all), for other
    /// threads to read while this slab goes on growing. It has the same
    /// elements at the same addresses, and the same identity (a pool lends
    /// from either alike), and keeps the mapping alive. From now on those
    /// elements are only written through [`Slab::store_shared`] (and
    /// [`Slab::set`] refuses them), and nothing is pushed onto the view.
    /// Panics unless the slab has the full reservation (it never moves).
    pub fn alias(&mut self, len: usize) -> Slab<T> {
        assert!(self.is_fixed() && !self.view, "a view of a fixed slab");
        let len = len.min(self.len);
        let shared = self.shared.get_or_insert_with(|| {
            std::sync::Arc::new(Mapping {
                base: self.base.cast(),
                bytes: CAP * size_of::<T>(),
            })
        });
        self.frozen = self.frozen.max(len);
        Slab {
            base: self.base,
            len,
            room: len,
            cap: AtomicUsize::new(CAP),
            id: self.id,
            pooled: AtomicBool::new(false),
            shared: Some(shared.clone()),
            frozen: len,
            view: true,
            _t: PhantomData,
        }
    }

    /// Whether some view of this slab is alive.
    pub fn has_views(&self) -> bool {
        self.shared
            .as_ref()
            .is_some_and(|m| std::sync::Arc::strong_count(m) > 1)
    }

    /// Push `f` of each element of `src` (making room for all at once).
    #[inline]
    pub fn extend_map(&mut self, src: &[T], mut f: impl FnMut(T) -> T) {
        let (len, n) = (self.len, src.len());
        if n > self.room - len {
            self.grow(len.saturating_add(n));
        }
        let to = self.base.as_ptr();
        for (k, &v) in src.iter().enumerate() {
            // SAFETY: as in `push`: `len + k < len + n <= room`.
            unsafe { to.add(len + k).write(f(v)) };
        }
        self.len = len + n;
    }

    /// Set each element `i` in `from..to` (and below `len`) for which
    /// `f(self, i)` (which sees the slab as it is so far) gives a value.
    /// Panics if a view sees element `from`.
    #[inline]
    pub fn fill_range(
        &mut self,
        from: usize,
        to: usize,
        mut f: impl FnMut(&Self, usize) -> Option<T>,
    ) {
        assert!(from >= self.frozen, "a slab's views see element {from}");
        for i in from..to.min(self.len) {
            if let Some(v) = f(self, i) {
                // SAFETY: `i < len`, inside the mapping, past what views
                // see; `&mut self` excludes every other access (`f` is done
                // with its borrow).
                unsafe { self.base.as_ptr().add(i).write(v) };
            }
        }
    }

    /// The elements, mutably. Panics while a view of the slab is alive.
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        assert!(!self.view && !self.has_views(), "a slab with views");
        if self.len == 0 {
            return &mut [];
        }
        // SAFETY: elements `0..len` are initialized and inside the mapping;
        // `&mut self` excludes every other access, and there is no view.
        unsafe { std::slice::from_raw_parts_mut(self.base.as_ptr(), self.len) }
    }

    /// A view of the first `len` elements (at most all) that reads them
    /// atomically, as [`Slab::store_shared`] may set them at once. As
    /// [`Slab::alias`] otherwise.
    pub fn atomic_alias(&mut self, len: usize) -> AtomicView
    where
        T: Plain,
    {
        const _: () = assert!(size_of::<AtomicU64>() == size_of::<u64>());
        assert!(size_of::<T>() == size_of::<u64>(), "a view of 64-bit words");
        let v = self.alias(len);
        AtomicView {
            base: v.base.cast(),
            len: v.len,
            _shared: v.shared.clone(),
        }
    }
}

impl<T: Plain> Slab<T> {
    /// Set element `i` (below `len`), which views on other threads may be
    /// reading at once, atomically (see [`Slab::atomic_alias`]).
    #[inline(always)]
    pub fn store_shared(&mut self, i: usize, v: u64) {
        assert!(size_of::<T>() == size_of::<u64>() && i < self.len);
        // SAFETY: inside the mapping and aligned for a 64-bit atomic;
        // `&mut self` excludes every plain access on this thread, and any
        // view reads the words atomically.
        unsafe { AtomicU64::from_ptr(self.base.as_ptr().cast::<u64>().add(i)) }
            .store(v, Ordering::Relaxed);
    }
}

impl<T: Copy> std::ops::Deref for Slab<T> {
    type Target = [T];
    #[inline(always)]
    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

/// A view of a slab of 64-bit words that another thread may set at once
/// (see [`Slab::atomic_alias`]): read atomically.
pub struct AtomicView {
    base: NonNull<u64>,
    len: usize,
    _shared: Option<std::sync::Arc<Mapping>>,
}

// SAFETY: it only reads its words, atomically, and keeps them mapped.
unsafe impl Send for AtomicView {}
// SAFETY: as above.
unsafe impl Sync for AtomicView {}

impl AtomicView {
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Word `i` (below `len`).
    #[inline(always)]
    pub fn load(&self, i: usize) -> u64 {
        assert!(i < self.len, "view index {i} out of bounds");
        // SAFETY: inside the mapping, which `_shared` keeps; the slab sets
        // these words atomically only (see `Slab::alias`).
        unsafe { AtomicU64::from_ptr(self.base.as_ptr().add(i)) }.load(Ordering::Relaxed)
    }
}

/// Give the whole pages inside `b` back to the system: their bytes read
/// as zeros from then on.
pub fn release_pages(b: &mut [u8]) {
    #[cfg(unix)]
    {
        // SAFETY: `sysconf` only reads a value.
        let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
        let Ok(page) = usize::try_from(page) else {
            return;
        };
        if !page.is_power_of_two() {
            return;
        }
        let start = b.as_mut_ptr() as usize;
        let from = start.next_multiple_of(page);
        let to = (start + b.len()) & !(page - 1);
        if to > from {
            // SAFETY: the pages are inside `b`, which is borrowed mutably
            // (so nothing else reads them); private anonymous pages read as
            // zeros after this, which every byte value allows.
            unsafe { libc::madvise(from as *mut libc::c_void, to - from, libc::MADV_DONTNEED) };
        }
    }
    #[cfg(not(unix))]
    let _ = b;
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
    /// The first block lent at the least (see [`Pool::lend_above`]).
    floor: AtomicU32,
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
    /// Lend no block below index `i` from now on: for views of slabs that
    /// are still growing (see [`Slab::alias`]), whose blocks must be above
    /// anything the slabs will hold.
    pub fn lend_above(&self, i: usize) {
        let k = u32::try_from(i.div_ceil(BLOCK as usize)).unwrap_or(u32::MAX);
        self.floor.fetch_max(k, Ordering::Relaxed);
    }

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
        let floor = (a.len.max(b.len).div_ceil(BLOCK as usize) as u32)
            .max(self.floor.load(Ordering::Relaxed));
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

/// Plain integers: any bytes, zeros included, are one of their values.
pub trait Plain: Copy + private::Sealed {}
impl Plain for u32 {}
impl Plain for u64 {}
mod private {
    pub trait Sealed {}
    impl Sealed for u32 {}
    impl Sealed for u64 {}
}

/// A fixed array of plain integers in memory of its own, zeros at first:
/// a fresh mapping, whose pages cost nothing until written (where a
/// zeroed `Vec` from the allocator may be written through first). It can
/// shrink, giving back the pages past its new end.
pub struct Zeroed<T: Plain> {
    ptr: NonNull<T>,
    len: usize,
    /// The mapping's bytes (0 for an empty array, which has none).
    bytes: usize,
}

// SAFETY: it owns its elements, like a `Box<[T]>`.
unsafe impl<T: Plain + Send> Send for Zeroed<T> {}
// SAFETY: as above.
unsafe impl<T: Plain + Sync> Sync for Zeroed<T> {}

impl<T: Plain> Zeroed<T> {
    /// `len` zeros. Panics if the system has no room for them.
    pub fn new(len: usize) -> Self {
        let bytes = len.checked_mul(size_of::<T>()).expect("array size");
        if bytes == 0 {
            return Zeroed {
                ptr: NonNull::dangling(),
                len,
                bytes: 0,
            };
        }
        let Some(p) = map(bytes) else {
            panic!(
                "nitrolean: resource limit: out of memory for {} MiB",
                bytes >> 20
            );
        };
        Zeroed {
            ptr: p.cast(),
            len,
            bytes,
        }
    }

    /// Keep the first `len` elements (at most as many as there are) and
    /// give back the pages after them.
    pub fn truncate(&mut self, len: usize) {
        if len >= self.len {
            return;
        }
        self.len = len;
        let keep = (len * size_of::<T>()).next_multiple_of(page_size());
        if keep < self.bytes {
            // SAFETY: the tail of this array's own mapping, past its
            // elements: nothing refers to it.
            unsafe {
                libc::munmap(
                    self.ptr.as_ptr().cast::<u8>().add(keep).cast(),
                    self.bytes - keep,
                )
            };
            self.bytes = keep;
        }
    }
}

impl<T: Plain> std::ops::Deref for Zeroed<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        // SAFETY: `len` elements of the mapping, zeros or written since
        // (any bytes are a value of a plain type), owned by `self`.
        unsafe { std::slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
    }
}

impl<T: Plain> std::ops::DerefMut for Zeroed<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        // SAFETY: as in `deref`, borrowed mutably through `self`.
        unsafe { std::slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len) }
    }
}

impl<T: Plain> Drop for Zeroed<T> {
    fn drop(&mut self) {
        if self.bytes > 0 {
            // SAFETY: the array's own mapping, which nothing borrows now.
            unsafe { libc::munmap(self.ptr.as_ptr().cast(), self.bytes) };
        }
    }
}

/// A fixed set of bits in memory of its own (as [`Zeroed`], so that its
/// pages cost nothing until a bit in them is set), which one thread sets
/// while others read it.
pub struct Bits(Zeroed<u64>);

impl Bits {
    /// `n` bits, all clear.
    pub fn new(n: usize) -> Self {
        Bits(Zeroed::new(n.div_ceil(64)))
    }

    fn words(&self) -> &[AtomicU64] {
        const _: () = assert!(
            size_of::<AtomicU64>() == size_of::<u64>()
                && align_of::<AtomicU64>() == align_of::<u64>()
        );
        // SAFETY: the words of the mapping, owned by `self`, as atomics of
        // the same size and alignment; no plain reference to them is
        // handed out (`self.0` is private and only read through here).
        unsafe { std::slice::from_raw_parts(self.0.ptr.as_ptr().cast::<AtomicU64>(), self.0.len) }
    }

    /// Whether bit `i` is set (false past the end).
    #[inline(always)]
    pub fn get(&self, i: usize) -> bool {
        self.words()
            .get(i / 64)
            .is_some_and(|w| w.load(Ordering::Relaxed) >> (i % 64) & 1 != 0)
    }

    /// Set bit `i` (nothing past the end). Meant for one thread: another
    /// setting a bit of the same word at once may clear it again.
    #[inline(always)]
    pub fn set(&self, i: usize) {
        if let Some(w) = self.words().get(i / 64) {
            let m = 1 << (i % 64);
            let v = w.load(Ordering::Relaxed);
            if v & m == 0 {
                w.store(v | m, Ordering::Relaxed);
            }
        }
    }
}

pub(crate) fn page_size() -> usize {
    static PAGE: OnceLock<usize> = OnceLock::new();
    *PAGE.get_or_init(|| {
        // SAFETY: plain sysconf.
        let p = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
        usize::try_from(p)
            .ok()
            .filter(|p| p.is_power_of_two())
            .unwrap_or(1 << 16)
    })
}

/// Give the system back the memory pages that lie wholly inside `v`
/// (`MADV_DONTNEED`), for elements that will not be read again: what is
/// read there afterwards is zeros (a value of `T`, which is plain). The
/// buffer stays allocated: freeing it later is as usual.
pub fn release<T: Plain>(v: &mut [T]) {
    let page = page_size();
    let start = v.as_mut_ptr() as usize;
    let end = start + std::mem::size_of_val(v);
    let (from, to) = (start.next_multiple_of(page), end & !(page - 1));
    if from < to {
        // SAFETY: whole pages inside `v`, which this borrow holds alone;
        // the memory is private and anonymous, so its pages read as zeros
        // afterwards, which are values of `T`.
        unsafe { libc::madvise(from as *mut libc::c_void, to - from, libc::MADV_DONTNEED) };
    }
}

/// `s` as atomics, for threads that share it.
pub fn atomic_u32(s: &mut [u32]) -> &[AtomicU32] {
    const { assert!(align_of::<AtomicU32>() == align_of::<u32>()) };
    // SAFETY: AtomicU32 has u32's size and (asserted) alignment, and the
    // exclusive borrow covers every access through the atomics.
    unsafe { std::slice::from_raw_parts(s.as_mut_ptr().cast::<AtomicU32>(), s.len()) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    #[test]
    fn bits_set_and_get() {
        let b = Bits::new(130);
        for i in [0, 1, 63, 64, 129] {
            assert!(!b.get(i));
            b.set(i);
            assert!(b.get(i));
        }
        assert!(!b.get(2) && !b.get(65) && !b.get(128));
        // Past the end: nothing set, nothing found.
        b.set(1 << 20);
        assert!(!b.get(1 << 20));
    }

    thread_local! {
        /// Slabs made on this thread take the reduced path, with this share.
        pub(super) static SHARE: Cell<Option<usize>> = const { Cell::new(None) };
    }

    /// A zeroed array reads zeros, keeps what is written, and shrinks.
    #[test]
    fn zeroed_arrays() {
        let mut z: Zeroed<u64> = Zeroed::new(1 << 20);
        assert!(z.iter().all(|&x| x == 0));
        z[12345] = 7;
        z[(1 << 20) - 1] = 9;
        z.truncate(20000);
        assert_eq!((z.len(), z[12345]), (20000, 7));
        z.truncate(30000);
        assert_eq!(z.len(), 20000);
        let e: Zeroed<u32> = Zeroed::new(0);
        assert!(e.is_empty());
    }

    /// Released elements read as zeros, the others as they were.
    #[test]
    fn released_pages_read_zero() {
        let mut v: Vec<u64> = (1..=1 << 20).collect();
        release(&mut v[100..(1 << 20) - 100]);
        assert_eq!(v[99], 100);
        assert_eq!(v[(1 << 20) - 100], (1 << 20) - 99);
        assert_eq!(v[1 << 19], 0, "a page in the middle went back");
        let mut w = vec![7u32; 10];
        release(&mut w);
        assert_eq!(w, vec![7; 10], "no whole page inside");
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
        // Free the upper half of the mapping, then grow back into it. In a
        // child process: there no other thread (another test's) can map
        // the freed range first. The child only makes system calls and
        // reads memory, then exits with the outcome.
        // SAFETY: fork; the child runs no code that could need a lock
        // another thread held (no allocation, no panic) before `_exit`.
        let pid = unsafe { libc::fork() };
        assert!(pid >= 0, "fork");
        if pid == 0 {
            // SAFETY: the slab's own mapping, above its one element.
            let freed = unsafe { libc::munmap(base.as_ptr().add(cap / 2).cast(), cap / 2 * 4) };
            *a.cap.get_mut() = cap / 2;
            let ok = freed == 0
                && a.grow_in_place(cap)
                && (a.cap.load(Ordering::Relaxed), a.base) == (cap, base)
                && *a.get(0) == 42;
            // SAFETY: ends the child at once, running nothing of the
            // test harness's.
            unsafe { libc::_exit(if ok { 0 } else { 1 }) };
        }
        let mut status = 0;
        // SAFETY: waits for the child just made.
        assert_eq!(unsafe { libc::waitpid(pid, &mut status, 0) }, pid);
        assert!(
            libc::WIFEXITED(status) && libc::WEXITSTATUS(status) == 0,
            "grown in place in the child: {status:#x}"
        );
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
