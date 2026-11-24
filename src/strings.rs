//! Interned strings: one contiguous byte buffer plus an end-offset table.
//!
//! Name components repeat heavily (`mk`, `rec`, `inst`, `proof_1`, ...), so
//! interning them saves memory, and it makes string equality an id compare.
//! Per string the pool costs its bytes plus 4 bytes of offset plus one
//! hash-table slot; there is no per-string heap allocation.

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
}

impl StrPool {
    pub fn new() -> Self {
        Self::default()
    }

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
        let (a, b) = self.range(id.index());
        &self.bytes[a..b]
    }

    /// The id of `s`, if interned.
    pub fn find(&self, s: &str) -> Option<StrId> {
        self.table
            .find(hash_bytes(s.as_bytes()), |&id| self.get(StrId(id)) == s)
            .map(|&id| StrId(id))
    }

    pub fn intern(&mut self, s: &str) -> Result<StrId, Overflow> {
        let h = hash_bytes(s.as_bytes());
        let Self { bytes, ends, table } = self;
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
}
