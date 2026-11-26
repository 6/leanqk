//! Interned strings: one contiguous byte buffer plus an end-offset table.
//!
//! Name components repeat heavily (`mk`, `rec`, `inst`, `proof_1`, ...), so
//! interning them saves memory, and it makes string equality an id compare.
//! Per string the pool costs its bytes plus 4 bytes of offset plus one
//! hash-table slot; there is no per-string heap allocation.

use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Mutex, OnceLock};

use hashbrown::HashTable;

use crate::hash::hash_bytes;

/// Id of an interned string.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct StrId(pub(crate) u32);

impl StrId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Error when an arena outgrows its 32-bit ids or offsets.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Overflow(pub &'static str);

#[derive(Default)]
pub struct StrPool {
    bytes: String,
    ends: Vec<u32>,
    table: HashTable<u32>,
    /// Strings added through a shared reference ([`StrPool::intern_late`]),
    /// once enabled: ids from `ends.len()` on.
    late: Option<Box<Late>>,
}

/// Late strings: a locked table, and write-once cells read without the
/// lock. Chunk `c` holds `2^(c + LATE_BITS)` cells.
struct Late {
    table: Mutex<HashTable<u32>>,
    chunks: Vec<OnceLock<LateChunk>>,
    next: AtomicU32,
}

const LATE_BITS: u32 = 10;

type LateChunk = Box<[OnceLock<Box<str>>]>;

/// The chunk and offset of late string `i`.
fn late_slot(i: u32) -> (usize, usize) {
    let j = (i as u64 >> LATE_BITS) + 1;
    let c = 63 - j.leading_zeros() as usize;
    let start = ((1u64 << c) - 1) << LATE_BITS;
    (c, (i as u64 - start) as usize)
}

impl Late {
    fn new() -> Self {
        Late {
            table: Mutex::new(HashTable::new()),
            chunks: (0..=(32 - LATE_BITS)).map(|_| OnceLock::new()).collect(),
            next: AtomicU32::new(0),
        }
    }

    fn cell(&self, i: u32) -> &OnceLock<Box<str>> {
        let (c, o) = late_slot(i);
        let n = 1usize << (c as u32 + LATE_BITS);
        &self.chunks[c].get_or_init(|| (0..n).map(|_| OnceLock::new()).collect())[o]
    }

    fn get(&self, i: u32) -> &str {
        self.cell(i).get().expect("published before use")
    }
}

impl StrPool {
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of strings (not counting late ones).
    pub fn len(&self) -> usize {
        self.ends.len()
    }

    pub fn is_empty(&self) -> bool {
        self.ends.is_empty()
    }

    fn range(&self, i: usize) -> (usize, usize) {
        let start = if i == 0 { 0 } else { self.ends[i - 1] as usize };
        (start, self.ends[i] as usize)
    }

    pub fn get(&self, id: StrId) -> &str {
        let i = id.index();
        if i >= self.ends.len()
            && let Some(l) = &self.late
        {
            return l.get(id.0 - self.ends.len() as u32);
        }
        let (a, b) = self.range(i);
        &self.bytes[a..b]
    }

    /// Empty, keeping the allocations (not for a pool with late strings).
    pub fn clear(&mut self) {
        self.bytes.clear();
        self.ends.clear();
        self.table.clear();
    }

    /// Allow [`StrPool::intern_late`].
    pub fn enable_late(&mut self) {
        self.late.get_or_insert_with(|| Box::new(Late::new()));
    }

    /// The id of `s`, adding it if new, through a shared reference (for
    /// strings first met while decoding a value lazily, on any thread).
    /// Strings are identified by content, so this never gives one string
    /// two ids. Needs [`StrPool::enable_late`].
    pub fn intern_late(&self, s: &str) -> Result<StrId, Overflow> {
        if let Some(id) = self.find(s) {
            return Ok(id);
        }
        let l = self
            .late
            .as_ref()
            .ok_or(Overflow("late strings are not enabled"))?;
        let base = self.ends.len() as u32;
        let h = hash_bytes(s.as_bytes());
        let mut t = l.table.lock().expect("late strings");
        if let Some(&i) = t.find(h, |&i| l.get(i) == s) {
            return Ok(StrId(base + i));
        }
        let i = l.next.load(Ordering::Relaxed);
        if i >= u32::MAX - base - 1 {
            return Err(Overflow("too many strings"));
        }
        let _ = l.cell(i).set(s.into());
        l.next.store(i + 1, Ordering::Release);
        t.insert_unique(h, i, |&i| hash_bytes(l.get(i).as_bytes()));
        Ok(StrId(base + i))
    }

    /// The id of `s`, if interned.
    pub fn find(&self, s: &str) -> Option<StrId> {
        self.table
            .find(hash_bytes(s.as_bytes()), |&id| self.get(StrId(id)) == s)
            .map(|&id| StrId(id))
    }

    pub fn intern(&mut self, s: &str) -> Result<StrId, Overflow> {
        self.intern_hashed(hash_bytes(s.as_bytes()), s)
    }

    /// [`StrPool::intern`] for bytes, or `None` if they are not UTF-8.
    /// (Bytes equal to a string here are UTF-8, so only new ones are
    /// checked.)
    pub fn intern_bytes(&mut self, s: &[u8]) -> Option<Result<StrId, Overflow>> {
        let h = hash_bytes(s);
        if self
            .late
            .as_ref()
            .is_none_or(|l| l.next.load(Ordering::Relaxed) == 0)
        {
            let Self {
                bytes, ends, table, ..
            } = self;
            if let Some(&id) = table.find(h, |&id| {
                let i = id as usize;
                let start = if i == 0 { 0 } else { ends[i - 1] as usize };
                &bytes.as_bytes()[start..ends[i] as usize] == s
            }) {
                return Some(Ok(StrId(id)));
            }
        }
        Some(self.intern_hashed(h, std::str::from_utf8(s).ok()?))
    }

    fn intern_hashed(&mut self, h: u64, s: &str) -> Result<StrId, Overflow> {
        assert!(
            self.late
                .as_ref()
                .is_none_or(|l| l.next.load(Ordering::Relaxed) == 0),
            "no strings are added after late ones"
        );
        let Self {
            bytes, ends, table, ..
        } = self;
        let range = |i: usize| {
            let start = if i == 0 { 0 } else { ends[i - 1] as usize };
            (start, ends[i] as usize)
        };
        if let Some(&id) = table.find(h, |&id| {
            let (a, b) = range(id as usize);
            &bytes[a..b] == s
        }) {
            return Ok(StrId(id));
        }
        let end = bytes.len() + s.len();
        if end > u32::MAX as usize || ends.len() >= u32::MAX as usize {
            return Err(Overflow("string pool exceeds 4 GiB"));
        }
        let id = ends.len() as u32;
        bytes.push_str(s);
        ends.push(end as u32);
        let (bytes, ends) = (&*bytes, &*ends);
        table.insert_unique(h, id, |&id| {
            let i = id as usize;
            let start = if i == 0 { 0 } else { ends[i - 1] as usize };
            hash_bytes(&bytes.as_bytes()[start..ends[i] as usize])
        });
        Ok(StrId(id))
    }

    /// Approximate heap bytes held.
    pub fn heap_bytes(&self) -> usize {
        self.bytes.capacity() + self.ends.capacity() * 4 + self.table.capacity() * 5
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interns() {
        let mut p = StrPool::new();
        let a = p.intern("Nat").unwrap();
        let b = p.intern("").unwrap();
        let c = p.intern("Nat").unwrap();
        let d = p.intern("succ").unwrap();
        assert_eq!(a, c);
        assert_ne!(a, b);
        assert_eq!(p.get(a), "Nat");
        assert_eq!(p.get(b), "");
        assert_eq!(p.get(d), "succ");
        assert_eq!(p.len(), 3);
    }

    #[test]
    fn late_strings() {
        let mut p = StrPool::new();
        let a = p.intern("Nat").unwrap();
        p.enable_late();
        assert_eq!(p.intern_late("Nat").unwrap(), a);
        let ids: Vec<StrId> = (0..5000)
            .map(|i| p.intern_late(&format!("x{i}")).unwrap())
            .collect();
        for (i, &id) in ids.iter().enumerate() {
            assert_eq!(p.get(id), format!("x{i}"));
            assert_eq!(p.intern_late(&format!("x{i}")).unwrap(), id);
        }
        assert_eq!(late_slot(0), (0, 0));
        assert_eq!(late_slot(1023), (0, 1023));
        assert_eq!(late_slot(1024), (1, 0));
        assert_eq!(late_slot(3071), (1, 2047));
        assert_eq!(late_slot(3072), (2, 0));
    }
}
