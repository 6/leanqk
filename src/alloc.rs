//! The global allocator of the binaries: mimalloc, called without an
//! alignment where the platform's default alignment suffices.
//!
//! `mimalloc::MiMalloc` passes every allocation to `mi_malloc_aligned`,
//! which with mimalloc v3 takes a slower path than `mi_malloc` even for
//! alignments `mi_malloc` already guarantees. The evaluator makes a few
//! small allocations per step (thunks, values, environments), so on
//! computation-heavy proofs this costs 5 to 15% of the time.

use std::alloc::{GlobalAlloc, Layout};

use libmimalloc_sys as mi;

/// What `mi_malloc` guarantees (`MI_MAX_ALIGN_SIZE`).
const MIN_ALIGN: usize = 16;

pub struct Mi;

unsafe impl GlobalAlloc for Mi {
    #[inline]
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        unsafe {
            if l.align() <= MIN_ALIGN {
                mi::mi_malloc(l.size()) as *mut u8
            } else {
                mi::mi_malloc_aligned(l.size(), l.align()) as *mut u8
            }
        }
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        unsafe {
            if l.align() <= MIN_ALIGN {
                mi::mi_zalloc(l.size()) as *mut u8
            } else {
                mi::mi_zalloc_aligned(l.size(), l.align()) as *mut u8
            }
        }
    }

    #[inline]
    unsafe fn dealloc(&self, p: *mut u8, _l: Layout) {
        unsafe { mi::mi_free(p.cast()) }
    }

    #[inline]
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        unsafe {
            if l.align() <= MIN_ALIGN {
                mi::mi_realloc(p.cast(), n) as *mut u8
            } else {
                mi::mi_realloc_aligned(p.cast(), n, l.align()) as *mut u8
            }
        }
    }
}
