//! The checker's direct-mapped tables, together in one 2 MiB block mapped
//! with huge pages where the kernel allows: lookups land all over these
//! tables, and with 4 KiB pages most of them miss the TLB.

use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

use super::{BINDER_SLOTS, EAGER_DIRECT_SLOTS, EAGER_SLOTS, INFER_SLOTS, PRUNES, SYN_T, memo, val};

/// One huge page.
const HUGE: usize = 2 << 20;

#[repr(C)]
pub(super) struct Tables {
    /// A direct-mapped front of `eager_memo`: (term, environment,
    /// substitution, value).
    pub eager_slots: [[u32; 4]; EAGER_SLOTS],
    /// `eager`'s direct-mapped memo: (term, substitution, values read,
    /// value).
    pub eager_direct: [[u32; 4]; EAGER_DIRECT_SLOTS],
    /// λ and Π values by term, environment and substitution (`eval_binder`).
    pub binder_slots: [[u32; 4]; BINDER_SLOTS],
    /// A direct-mapped front of `tuples`: (environment, range, holes (two
    /// words), id).
    pub tuple_slots: [[u32; 5]; memo::TUPLE_SLOTS],
    /// A direct-mapped front of `infer_memo`: (term, environment,
    /// substitution, entry).
    pub infer_slots: [[u32; 4]; INFER_SLOTS],
    /// Structural comparisons of term pairs and value–term pairs.
    pub syn_t: [[u32; 8]; SYN_T],
    /// `trim_long`: (environment, length, result).
    pub trim_cache: [[u32; 3]; PRUNES],
    /// `prune` by environment and holes: (environment, holes, pruned
    /// environment).
    pub prunes: [[u32; 3]; PRUNES],
    /// `trim_holes`: (environment, holes, length, result).
    pub trim_holes_memo: [[u32; 4]; PRUNES],
}

const _: () = assert!(size_of::<Tables>() <= HUGE);

impl Tables {
    /// Every slot empty.
    pub fn clear(&mut self) {
        // SAFETY: `Tables` is all `u32`s (`repr(C)`, no padding: every
        // field has the alignment of `u32`), so it is a slice of them.
        let words = unsafe {
            std::slice::from_raw_parts_mut(
                (self as *mut Tables).cast::<u32>(),
                size_of::<Tables>() / 4,
            )
        };
        words.fill(val::NONE);
    }
}

/// [`Tables`] in a mapping of their own, starting on a huge page boundary.
pub(super) struct Fixed {
    t: NonNull<Tables>,
    /// The mapping: `HUGE` bytes more than `HUGE`, to align `t` in.
    map: NonNull<libc::c_void>,
}

impl Fixed {
    pub fn new() -> Fixed {
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
            std::alloc::handle_alloc_error(std::alloc::Layout::new::<Tables>());
        };
        let at = (p as usize).next_multiple_of(HUGE);
        // SAFETY: `at..at + HUGE` lies in the mapping just made; advice
        // only.
        unsafe { libc::madvise(at as *mut libc::c_void, HUGE, libc::MADV_HUGEPAGE) };
        // A name for the mapping in `/proc/PID/smaps`, where the kernel
        // allows it, to see whether it got a huge page.
        // SAFETY: names a range of the mapping just made; the name is
        // copied.
        unsafe {
            libc::prctl(
                libc::PR_SET_VMA,
                libc::PR_SET_VMA_ANON_NAME,
                at,
                HUGE,
                c"nitrolean-tables".as_ptr(),
            )
        };
        let t = NonNull::new(at as *mut Tables).expect("mapped");
        let mut f = Fixed { t, map };
        // The mapping reads as zeros: a valid `Tables`, then filled.
        f.clear();
        f
    }
}

impl Deref for Fixed {
    type Target = Tables;
    #[inline(always)]
    fn deref(&self) -> &Tables {
        // SAFETY: `t` is aligned and initialised, and owned by `self`.
        unsafe { self.t.as_ref() }
    }
}

impl DerefMut for Fixed {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Tables {
        // SAFETY: as in `deref`, and `&mut self` is unique.
        unsafe { self.t.as_mut() }
    }
}

impl Drop for Fixed {
    fn drop(&mut self) {
        // SAFETY: the mapping made in `new`, unused from here on.
        unsafe { libc::munmap(self.map.as_ptr(), 2 * HUGE) };
    }
}

// SAFETY: `Fixed` owns its tables as a `Box` would.
unsafe impl Send for Fixed {}
// SAFETY: shared, `Fixed` gives out only `&Tables`.
unsafe impl Sync for Fixed {}
