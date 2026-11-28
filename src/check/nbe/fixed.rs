//! The checker's direct-mapped tables, together in one 2 MiB block mapped
//! with huge pages where the kernel allows: lookups land all over these
//! tables, and with 4 KiB pages most of them miss the TLB.

use super::{BINDER_SLOTS, EAGER_DIRECT_SLOTS, EAGER_SLOTS, INFER_SLOTS, PRUNES, SYN_T, memo, val};

/// One huge page.
const HUGE: usize = 2 << 20;

/// Aligned to a huge page, so that one can hold them all.
#[repr(C, align(2097152))]
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

const _: () = assert!(size_of::<Tables>() == HUGE && align_of::<Tables>() == HUGE);
// `new` fills with bytes of all ones.
const _: () = assert!(val::NONE == u32::MAX);

impl Tables {
    /// The tables, every slot empty, advised to the kernel for a huge page.
    pub fn new() -> Box<Tables> {
        let mut b = Box::<Tables>::new_uninit();
        let at = b.as_mut_ptr();
        // SAFETY: advice only, on the allocation just made; then a name for
        // it in `/proc/PID/smaps`, where the kernel allows it, to see
        // whether it got a huge page (the name is copied).
        unsafe {
            libc::madvise(at.cast(), HUGE, libc::MADV_HUGEPAGE);
            libc::prctl(
                libc::PR_SET_VMA,
                libc::PR_SET_VMA_ANON_NAME,
                at as usize,
                HUGE,
                c"nitrolean-tables".as_ptr(),
            );
        }
        // SAFETY: all ones is `NONE` in every slot, and every field is
        // arrays of `u32`.
        unsafe {
            at.write_bytes(0xff, 1);
            b.assume_init()
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
