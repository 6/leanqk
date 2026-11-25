//! Maps the ids used in an export file (`in`, `il`, `ie`) to arena ids.
//!
//! The format only says these are natural numbers; `leanexport` happens to
//! number each table densely from 0 in order, and then (as long as no two
//! records hash-cons to the same node) the export id *is* the arena id. The
//! map exploits that: it starts in an identity mode that costs nothing per
//! entry, and only falls back to a dense table (4 bytes per id) or, for ids
//! far beyond the count seen so far, a hash map, when the input deviates.

use hashbrown::HashMap;

const NONE: u32 = u32::MAX;

/// Ids up to `SLACK` beyond twice the current count go in the dense table.
const SLACK: u64 = 1 << 16;

#[derive(Debug, PartialEq, Eq)]
pub enum BindError {
    Duplicate,
}

pub struct IdMap {
    /// In identity mode, ids `0..identity` map to themselves.
    identity: u64,
    dense_mode: bool,
    dense: Vec<u32>,
    sparse: HashMap<u64, u32>,
    /// The id [`IdMap::bind`] takes on its fast path: the next one of the
    /// identity map, or of the dense table while there are no sparse
    /// entries (else `u64::MAX`).
    next: u64,
}

impl IdMap {
    /// A map with export ids `0..prebound` already bound to themselves.
    pub fn new(prebound: u64) -> Self {
        IdMap {
            identity: prebound,
            dense_mode: false,
            dense: Vec::new(),
            sparse: HashMap::new(),
            next: prebound,
        }
    }

    #[inline(always)]
    pub fn get(&self, id: u64) -> Option<u32> {
        if !self.dense_mode {
            return (id < self.identity).then_some(id as u32);
        }
        if let Some(&v) = self.dense.get(id as usize) {
            return (v != NONE).then_some(v);
        }
        self.sparse.get(&id).copied()
    }

    #[inline(always)]
    pub fn bind(&mut self, id: u64, target: u32) -> Result<(), BindError> {
        // The common cases: the next id of an identity map, or of a dense
        // one.
        if id == self.next {
            if self.dense_mode {
                self.dense.push(target);
                self.next += 1;
                return Ok(());
            }
            if target as u64 == id {
                self.identity += 1;
                self.next += 1;
                return Ok(());
            }
        }
        let r = self.bind_slow(id, target);
        self.next = self.fast_next();
        r
    }

    fn fast_next(&self) -> u64 {
        if !self.dense_mode {
            self.identity
        } else if self.sparse.is_empty() {
            self.dense.len() as u64
        } else {
            u64::MAX
        }
    }

    #[inline(never)]
    fn bind_slow(&mut self, id: u64, target: u32) -> Result<(), BindError> {
        if !self.dense_mode {
            if id < self.identity {
                return Err(BindError::Duplicate);
            }
            self.dense.clear();
            self.dense.extend(0..self.identity as u32);
            self.dense_mode = true;
        }
        // Ids up to about twice the count bound so far go in the dense
        // table (holes count, which only makes it a little roomier).
        let count = (self.dense.len() + self.sparse.len()) as u64;
        let limit = count.saturating_mul(2).saturating_add(SLACK);
        if (id as usize) < self.dense.len() {
            let slot = &mut self.dense[id as usize];
            if *slot != NONE {
                return Err(BindError::Duplicate);
            }
            *slot = target;
        } else if id < limit && id < NONE as u64 {
            if self.sparse.contains_key(&id) {
                return Err(BindError::Duplicate);
            }
            self.dense.resize(id as usize, NONE);
            self.dense.push(target);
            // Move sparse entries now covered by the dense table.
            if !self.sparse.is_empty() {
                let n = self.dense.len() as u64;
                let moved: Vec<(u64, u32)> = self.sparse.extract_if(|&k, _| k < n).collect();
                for (k, v) in moved {
                    self.dense[k as usize] = v;
                }
            }
        } else if self.sparse.insert(id, target).is_some() {
            return Err(BindError::Duplicate);
        }
        Ok(())
    }

    /// Make room for ids up to `n` without copying the table as it grows.
    pub fn reserve(&mut self, n: usize) {
        self.dense.reserve(n.saturating_sub(self.dense.len()));
    }

    /// Whether the map is still in its zero-cost identity mode.
    /// Change the target of a bound id.
    #[inline(always)]
    pub fn rebind(&mut self, id: u64, target: u32) {
        if self.dense_mode
            && let Some(slot) = self.dense.get_mut(id as usize)
        {
            *slot = target;
            return;
        }
        self.rebind_slow(id, target);
    }

    #[inline(never)]
    fn rebind_slow(&mut self, id: u64, target: u32) {
        if !self.dense_mode {
            if id < self.identity && target as u64 == id {
                return;
            }
            self.dense.clear();
            self.dense.extend(0..self.identity as u32);
            self.dense_mode = true;
        }
        match self.dense.get_mut(id as usize) {
            Some(slot) => *slot = target,
            None => {
                self.sparse.insert(id, target);
            }
        }
        self.next = self.fast_next();
    }

    #[cfg(test)]
    pub fn is_identity(&self) -> bool {
        !self.dense_mode
    }

    pub fn heap_bytes(&self) -> usize {
        self.dense.capacity() * 4 + self.sparse.capacity() * 13
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identity_then_dense_then_sparse() {
        let mut m = IdMap::new(1);
        assert_eq!(m.get(0), Some(0));
        assert_eq!(m.get(1), None);
        m.bind(1, 1).unwrap();
        m.bind(2, 2).unwrap();
        assert!(m.is_identity());
        assert_eq!(m.bind(2, 3), Err(BindError::Duplicate));
        // Out of order: switches to dense.
        m.bind(5, 3).unwrap();
        assert!(!m.is_identity());
        assert_eq!(m.get(2), Some(2));
        assert_eq!(m.get(5), Some(3));
        assert_eq!(m.get(4), None);
        m.bind(4, 4).unwrap();
        assert_eq!(m.bind(4, 4), Err(BindError::Duplicate));
        // Far away: sparse.
        m.bind(1 << 40, 7).unwrap();
        assert_eq!(m.get(1 << 40), Some(7));
        assert_eq!(m.bind(1 << 40, 8), Err(BindError::Duplicate));
        assert_eq!(m.get(u64::MAX), None);
    }

    #[test]
    fn sparse_entries_migrate_to_dense() {
        let mut m = IdMap::new(0);
        m.bind(100_000, 0).unwrap(); // beyond the slack: sparse
        for i in 0..100_000u64 {
            m.bind(i, i as u32 + 1).unwrap();
        }
        // The dense table has grown over 100_000.
        m.bind(100_001, 9).unwrap();
        assert_eq!(m.get(100_000), Some(0));
        assert_eq!(m.bind(100_000, 1), Err(BindError::Duplicate));
        assert_eq!(m.get(5), Some(6));
    }
}
