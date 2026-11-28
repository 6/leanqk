//! The checker's direct-mapped tables, together in one 2 MiB block mapped
//! with huge pages where the kernel allows: lookups land all over these
//! tables, and with 4 KiB pages most of them miss the TLB. Each table is
//! reached through a pointer of its own, as from a `Box`, so that a lookup
//! costs no more instructions than one in a table of its own.

use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

use super::{BINDER_SLOTS, EAGER_DIRECT_SLOTS, EAGER_SLOTS, INFER_SLOTS, PRUNES, SYN_T, memo, val};

/// One huge page.
const HUGE: usize = 2 << 20;

/// A table of `Tables`, in its block.
pub(super) struct Slot<T>(NonNull<T>);

impl<T> Deref for Slot<T> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &T {
        // SAFETY: the table is aligned and initialised, in a block owned
        // by the `Tables` that owns `self`.
        unsafe { self.0.as_ref() }
    }
}

impl<T> DerefMut for Slot<T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: as in `deref`; the tables do not overlap, and `&mut self`
        // is unique.
        unsafe { self.0.as_mut() }
    }
}

// SAFETY: a `Slot` owns its table as a `Box` would.
unsafe impl<T: Send> Send for Slot<T> {}
// SAFETY: shared, a `Slot` gives out only `&T`.
unsafe impl<T: Sync> Sync for Slot<T> {}

pub(super) struct Tables {
    /// A direct-mapped front of `eager_memo`: (term, environment,
    /// substitution, value).
    pub eager_slots: Slot<[[u32; 4]; EAGER_SLOTS]>,
    /// `eager`'s direct-mapped memo: (term, substitution, values read,
    /// value).
    pub eager_direct: Slot<[[u32; 4]; EAGER_DIRECT_SLOTS]>,
    /// λ and Π values by term, environment and substitution (`eval_binder`).
    pub binder_slots: Slot<[[u32; 4]; BINDER_SLOTS]>,
    /// A direct-mapped front of `tuples`: (environment, range, holes (two
    /// words), id).
    pub tuple_slots: Slot<[[u32; 5]; memo::TUPLE_SLOTS]>,
    /// A direct-mapped front of `infer_memo`: (term, environment,
    /// substitution, entry).
    pub infer_slots: Slot<[[u32; 4]; INFER_SLOTS]>,
    /// Structural comparisons of term pairs and value–term pairs.
    pub syn_t: Slot<[[u32; 8]; SYN_T]>,
    /// `trim_long`: (environment, length, result).
    pub trim_cache: Slot<[[u32; 3]; PRUNES]>,
    /// `prune` by environment and holes: (environment, holes, pruned
    /// environment).
    pub prunes: Slot<[[u32; 3]; PRUNES]>,
    /// `trim_holes`: (environment, holes, length, result).
    pub trim_holes_memo: Slot<[[u32; 4]; PRUNES]>,
    /// The mapping: `HUGE` bytes more than `HUGE`, to align the block in.
    map: NonNull<libc::c_void>,
}

// Every table is arrays of `u32`, laid one after the other.
const _: () = assert!(
    size_of::<[[u32; 4]; EAGER_SLOTS]>()
        + size_of::<[[u32; 4]; EAGER_DIRECT_SLOTS]>()
        + size_of::<[[u32; 4]; BINDER_SLOTS]>()
        + size_of::<[[u32; 5]; memo::TUPLE_SLOTS]>()
        + size_of::<[[u32; 4]; INFER_SLOTS]>()
        + size_of::<[[u32; 8]; SYN_T]>()
        + 2 * size_of::<[[u32; 3]; PRUNES]>()
        + size_of::<[[u32; 4]; PRUNES]>()
        <= HUGE
);
// `new` fills with bytes of all ones.
const _: () = assert!(val::NONE == u32::MAX);

impl Tables {
    /// The tables, every slot empty.
    pub fn new() -> Tables {
        let len = 2 * HUGE;
        // SAFETY: a new private anonymous mapping; touches no existing
        // memory.
        let p = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                len,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
                -1,
                0,
            )
        };
        let (Some(map), false) = (NonNull::new(p), p == libc::MAP_FAILED) else {
            std::alloc::handle_alloc_error(std::alloc::Layout::new::<[u8; HUGE]>());
        };
        let at = (p as usize).next_multiple_of(HUGE) as *mut u8;
        // SAFETY: `at..at + HUGE` lies in the mapping just made: advice
        // only; then a name for it in `/proc/PID/smaps`, where the kernel
        // allows it, to see whether it got a huge page (the name is
        // copied); then every slot `NONE`.
        unsafe {
            libc::madvise(at.cast(), HUGE, libc::MADV_HUGEPAGE);
            libc::prctl(
                libc::PR_SET_VMA,
                libc::PR_SET_VMA_ANON_NAME,
                at as usize,
                HUGE,
                c"nitrolean-tables".as_ptr(),
            );
            at.write_bytes(0xff, HUGE);
        }
        let mut n = at;
        let n = &mut n;
        Tables {
            eager_slots: carve(n),
            eager_direct: carve(n),
            binder_slots: carve(n),
            tuple_slots: carve(n),
            infer_slots: carve(n),
            syn_t: carve(n),
            trim_cache: carve(n),
            prunes: carve(n),
            trim_holes_memo: carve(n),
            map,
        }
    }

    /// Every slot empty.
    pub fn clear(&mut self) {
        self.eager_slots.as_flattened_mut().fill(val::NONE);
        self.eager_direct.as_flattened_mut().fill(val::NONE);
        self.binder_slots.as_flattened_mut().fill(val::NONE);
        self.tuple_slots.as_flattened_mut().fill(val::NONE);
        self.infer_slots.as_flattened_mut().fill(val::NONE);
        self.syn_t.as_flattened_mut().fill(val::NONE);
        self.trim_cache.as_flattened_mut().fill(val::NONE);
        self.prunes.as_flattened_mut().fill(val::NONE);
        self.trim_holes_memo.as_flattened_mut().fill(val::NONE);
    }
}

/// The table at `*next` in the block, and `*next` moved past it.
fn carve<T>(next: &mut *mut u8) -> Slot<T> {
    let t = NonNull::new(next.cast()).expect("mapped");
    // SAFETY: the tables fit the block (asserted above).
    *next = unsafe { next.add(size_of::<T>()) };
    Slot(t)
}

impl Drop for Tables {
    fn drop(&mut self) {
        // SAFETY: the mapping made in `new`; the tables go with `self`.
        unsafe { libc::munmap(self.map.as_ptr(), 2 * HUGE) };
    }
}

// SAFETY: `map` is owned by the tables, as a `Box` would be.
unsafe impl Send for Tables {}
// SAFETY: shared, the tables give out only shared references.
unsafe impl Sync for Tables {}
