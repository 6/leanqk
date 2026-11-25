//! Arrays that never move, in reserved address space, read with one load
//! and no bounds check.
//!
//! A [`Slab`] reserves room for [`CAP`] elements (`MAP_NORESERVE`: the
//! reservation costs no memory; a page is backed when first written) and
//! fills it from index 0 like a `Vec`, but it never reallocates, so its
//! base address stays fixed and an element is at `base + index`.
//!
//! Above a slab's elements, a [`Pool`] lends out blocks of [`BLOCK`]
//! indices to the checker's stores, one store per block at a time: a
//! store's own terms then live in the same array as the environment's,
//! and reading either is the same single load ([`Reader::get`]).
//!
//! All the `unsafe` code of the arenas is in this module. What makes it
//! sound:
//! - The mapping is `CAP` elements long and every index is masked to
//!   `CAP - 1`, so no read or write leaves the mapping.
//! - Elements below `len` are only written through `&mut Slab`.
//! - A pool slot is only written through its [`Block`], and a block is
//!   lent to one holder at a time and cannot outlive the borrows of its
//!   slabs, so nothing can push onto them (or free them) while it exists.
//!   Its slots are above `len` when it is lent.
//! - The one rule the types do not enforce: an index read must be below
//!   `len`, or in a block that the reader holds (the ids a store makes
//!   come from its own blocks; debug builds check this at the store).
//!   and that its holder has written. Reading another holder's slot would
//!   race with its writes, and an index never written holds zero bytes,
//!   which need not be a value of the type.

#![allow(unsafe_code)]

use std::marker::PhantomData;
use std::ptr::NonNull;
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering};

/// Index bits of a slab: ids are `u32`s below 2^31.
pub const CAP_BITS: u32 = 31;
/// Elements a slab has room for.
pub const CAP: usize = 1 << CAP_BITS;
const MASK: u32 = CAP as u32 - 1;

/// Index bits of a pool block.
pub const BLOCK_BITS: u32 = 16;
/// Indices per pool block.
pub const BLOCK: u32 = 1 << BLOCK_BITS;

/// An array of up to [`CAP`] elements that never moves.
pub struct Slab<T: Copy> {
    base: NonNull<T>,
    len: usize,
    /// The reservation; `None` for an empty slab that has not reserved.
    map: Option<memmap2::MmapMut>,
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
            map: None,
            pooled: AtomicBool::new(false),
            _t: PhantomData,
        }
    }
}

impl<T: Copy> Slab<T> {
    /// An empty slab with its range reserved.
    pub fn new() -> Self {
        let mut s = Self::default();
        s.reserve_range();
        s
    }

    #[cold]
    fn reserve_range(&mut self) {
        if self.map.is_some() {
            return;
        }
        let bytes = CAP * size_of::<T>();
        let mut map = memmap2::MmapOptions::new()
            .len(bytes)
            .no_reserve_swap()
            .map_anon()
            .unwrap_or_else(|e| {
                panic!(
                    "nitrolean: cannot reserve {} GiB of address space: {e}",
                    bytes >> 30
                )
            });
        // Fewer page faults and TLB misses; a hint only.
        let _ = map.advise(memmap2::Advice::HugePage);
        self.base = NonNull::new(map.as_mut_ptr().cast::<T>()).expect("mapping");
        self.map = Some(map);
    }

    /// The elements of `chunks`, in order.
    pub fn from_chunks(chunks: Vec<Vec<T>>) -> Self {
        let mut s = Self::new();
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

    #[inline]
    pub fn push(&mut self, v: T) {
        assert!(self.len < CAP, "slab full");
        if self.map.is_none() {
            self.reserve_range();
        }
        // SAFETY: `len < CAP` is inside the mapping, and `&mut self`
        // excludes every other access (no block is lent while it is
        // borrowed mutably).
        unsafe { self.base.as_ptr().add(self.len).write(v) };
        self.len += 1;
    }

    pub fn extend_from_slice(&mut self, vs: &[T]) {
        assert!(vs.len() <= CAP - self.len, "slab full");
        if vs.is_empty() {
            return;
        }
        self.reserve_range();
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
        while self.len < n {
            self.push(v);
        }
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
    /// The slabs this pool lends from (their base addresses), set at the
    /// first loan.
    bound: Option<(usize, usize)>,
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
        assert!(
            a.map.is_some() && b.map.is_some(),
            "a pool lends from reserved slabs"
        );
        let bases = (a.base.as_ptr() as usize, b.base.as_ptr() as usize);
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
            None if (st.next as usize) < CAP >> BLOCK_BITS => {
                st.next += 1;
                st.next - 1
            }
            None => return None,
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
