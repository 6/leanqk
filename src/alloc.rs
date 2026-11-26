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

/// `mi_option_purge_delay` in mimalloc v3's `mi_option_t` (the bindings
/// do not name it).
const MI_OPTION_PURGE_DELAY: std::ffi::c_int = 15;

unsafe extern "C" {
    fn mi_option_get(option: std::ffi::c_int) -> std::ffi::c_long;
    fn mi_option_set_default(option: std::ffi::c_int, value: std::ffi::c_long);
}

/// Return freed memory to the system at once rather than after mimalloc
/// v3's default second: the checker's workers free a declaration's terms
/// in bulk and allocate the next one's, and pages held for that second
/// added some 150 MB to the peak on Mathlib at 8 jobs (and some 100 MB at
/// one), at no measurable cost in time or instructions.
/// `MIMALLOC_PURGE_DELAY` in the environment still decides.
pub fn configure() {
    // SAFETY: plain option calls, before any thread is started.
    unsafe {
        // The index names that option: v3 defaults it to 1000 (unless the
        // environment set it; then `set_default` leaves it).
        debug_assert!(
            std::env::var_os("MIMALLOC_PURGE_DELAY").is_some()
                || mi_option_get(MI_OPTION_PURGE_DELAY) == 1000
        );
        mi_option_set_default(MI_OPTION_PURGE_DELAY, 0);
    }
}

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
