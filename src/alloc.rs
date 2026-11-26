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

/// `mi_option_purge_delay` and `mi_option_allow_thp` in mimalloc v3's
/// `mi_option_t` (the bindings do not name them).
const MI_OPTION_PURGE_DELAY: std::ffi::c_int = 15;
const MI_OPTION_ALLOW_THP: std::ffi::c_int = 43;

unsafe extern "C" {
    fn mi_option_get(option: std::ffi::c_int) -> std::ffi::c_long;
    fn mi_option_set_default(option: std::ffi::c_int, value: std::ffi::c_long);
    fn mi_option_set(option: std::ffi::c_int, value: std::ffi::c_long);
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

/// Small pages for the heap memory not touched yet, before checking on
/// several threads: each checker keeps a few partly used pages of every
/// size, and in 2 MiB pages those held some 50 to 140 MiB more on Mathlib
/// at 8 jobs (some 90 to 250 MiB at 12). What reading built keeps its huge
/// pages, as does a single checker: on small pages from the start, one job
/// took some 10% longer on Mathlib. The slabs ask for their own huge pages
/// (`slab.rs`). Not done if `MIMALLOC_ALLOW_THP` is set (as `0`, it turns
/// huge pages off for the whole process, the slabs' too).
pub fn small_heap_pages() {
    // SAFETY: plain option calls; mimalloc reads the option at each new
    // mapping.
    unsafe {
        if std::env::var_os("MIMALLOC_ALLOW_THP").is_some()
            || mi_option_get(MI_OPTION_ALLOW_THP) == 0
        {
            return;
        }
        mi_option_set(MI_OPTION_ALLOW_THP, 0);
    }
    // The heap's mappings so far asked for huge pages (`MADV_HUGEPAGE`):
    // take that back for the pages not touched yet. mimalloc names them,
    // where the kernel allows it; else the one a fresh allocation is in.
    let probe = Box::new(0u64);
    let at = &*probe as *const u64 as usize;
    let Ok(maps) = std::fs::read_to_string("/proc/self/maps") else {
        return;
    };
    for line in maps.lines() {
        let mut f = line.split_whitespace();
        let Some((lo, hi)) = f.next().and_then(|r| r.split_once('-')).and_then(|(a, b)| {
            Some((
                usize::from_str_radix(a, 16).ok()?,
                usize::from_str_radix(b, 16).ok()?,
            ))
        }) else {
            continue;
        };
        if (lo..hi).contains(&at) || f.nth(4).is_some_and(|n| n.contains("mimalloc")) {
            // SAFETY: advice only, on a mapping of the allocator's.
            unsafe { libc::madvise(lo as *mut libc::c_void, hi - lo, libc::MADV_NOHUGEPAGE) };
        }
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
