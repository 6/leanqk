//! Small, fast, non-cryptographic hashing for the hash-consing tables.
//!
//! Arena nodes refer to their children by canonical id, so a node's hash only
//! has to mix a couple of machine words; no recursion and no stored hashes.
//! The folded 64x64->128 multiply is the mixing step used by foldhash and
//! wyhash.

const K0: u64 = 0x243f_6a88_85a3_08d3;
const K2: u64 = 0xa409_3822_299f_31d0;

#[inline]
fn fold_mul(a: u64, b: u64) -> u64 {
    let r = (a as u128).wrapping_mul(b as u128);
    (r as u64) ^ ((r >> 64) as u64)
}

/// Hash two words: [`hash_front`]. The result has entropy in its high
/// bits too, which the SwissTable control bytes need.
#[inline]
pub fn hash2(w0: u64, w1: u64) -> u64 {
    hash_front(w0, w1)
}

/// 32 bits of a 64-bit hash, for a [`Table`].
#[inline]
pub fn fold32(h: u64) -> u32 {
    (h >> 32) as u32 ^ h as u32
}

/// Hash two words with one multiply (the folded product of the two words,
/// each offset by the same constant, the second rotated so that swapping
/// the words changes the hash). One constant, as loading a 64-bit
/// constant takes four instructions on some targets. Enough for
/// direct-mapped fronts and for the hash-consing tables keyed by ids; a
/// word equal to the constant would make every hash with it zero, which
/// only costs time.
#[inline]
pub fn hash_front(w0: u64, w1: u64) -> u64 {
    fold_mul(w0 ^ K0, w1.rotate_left(32) ^ K0)
}

/// Hash a byte string.
pub fn hash_bytes(bytes: &[u8]) -> u64 {
    let mut h = K2 ^ bytes.len() as u64;
    let (chunks, rest) = bytes.as_chunks::<8>();
    for c in chunks {
        h = fold_mul(h ^ u64::from_le_bytes(*c), K0);
    }
    let mut buf = [0u8; 8];
    buf[..rest.len()].copy_from_slice(rest);
    hash2(h, u64::from_le_bytes(buf))
}

/// An open-addressing set of `u32` ids for one thread, keyed by a 32-bit
/// hash that is stored with each id: probing compares stored hashes and
/// calls back for the id only when they agree, and growing reads only the
/// table. Linear probing over single slots at a load of at most 1/2, the
/// slot picked by the hash's top bits; nothing is ever removed, so a probe
/// stops at the first empty slot.
pub struct Table {
    /// `(hash | 1) << 32 | id`, or `EMPTY`: zero, so that a new table is
    /// zeroed memory.
    slots: Box<[u64]>,
    /// `32 - log2(slots.len())`.
    shift: u32,
    len: usize,
}

const EMPTY: u64 = 0;

/// The high word of an entry for hash `h`: never 0.
#[inline(always)]
fn tag(h: u32) -> u64 {
    ((h | 1) as u64) << 32
}

/// Slots of a new table.
const MIN_SLOTS: usize = 16;

/// Where a probe for a missing id stopped: insert it there with
/// [`Table::insert_at`].
#[derive(Clone, Copy)]
pub struct Slot(usize);

impl Default for Table {
    fn default() -> Self {
        Table::new()
    }
}

impl Table {
    pub fn new() -> Self {
        Table::with_slots(MIN_SLOTS)
    }

    fn with_slots(n: usize) -> Self {
        debug_assert!(n.is_power_of_two() && n >= MIN_SLOTS);
        Table {
            slots: vec![EMPTY; n].into_boxed_slice(),
            shift: 32 - n.trailing_zeros(),
            len: 0,
        }
    }

    #[inline(always)]
    fn start(&self, h: u32) -> usize {
        (h >> self.shift) as usize
    }

    #[inline(always)]
    fn mask(&self) -> usize {
        self.slots.len() - 1
    }

    #[inline(always)]
    #[allow(unsafe_code)]
    fn slot(&self, i: usize) -> u64 {
        debug_assert!(i < self.slots.len());
        // SAFETY: every index is masked by `slots.len() - 1`, a power of
        // two less one.
        unsafe { *self.slots.get_unchecked(i) }
    }

    #[cfg(test)]
    pub fn len(&self) -> usize {
        self.len
    }

    #[cfg(test)]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Slots held.
    pub fn capacity(&self) -> usize {
        self.slots.len()
    }

    /// The id with hash `h` for which `eq` holds.
    #[inline]
    pub fn find(&self, h: u32, mut eq: impl FnMut(u32) -> bool) -> Option<u32> {
        let tag = tag(h);
        let mut i = self.start(h);
        loop {
            let v = self.slot(i);
            if v == EMPTY {
                return None;
            }
            if v & !0xffff_ffff == tag && eq(v as u32) {
                return Some(v as u32);
            }
            i = (i + 1) & self.mask();
        }
    }

    /// The id with hash `h` for which `eq` holds, or else where to insert
    /// one: the slot stays good until something else is inserted.
    #[inline]
    pub fn find_or_slot(&mut self, h: u32, mut eq: impl FnMut(u32) -> bool) -> Result<u32, Slot> {
        let tag = tag(h);
        let mut i = self.start(h);
        loop {
            let v = self.slot(i);
            if v == EMPTY {
                return Err(Slot(i));
            }
            if v & !0xffff_ffff == tag && eq(v as u32) {
                return Ok(v as u32);
            }
            i = (i + 1) & self.mask();
        }
    }

    /// Add `id` with hash `h` where [`Table::find_or_slot`] said.
    #[inline]
    #[allow(unsafe_code)]
    pub fn insert_at(&mut self, slot: Slot, h: u32, id: u32) {
        debug_assert!(slot.0 < self.slots.len() && self.slots[slot.0] == EMPTY);
        // SAFETY: `find_or_slot` gave an index into `slots`, which has not
        // changed since (no insert in between).
        unsafe { *self.slots.get_unchecked_mut(slot.0) = tag(h) | id as u64 };
        self.len += 1;
        // Grow once more than half full, so that a probe always meets an
        // empty slot.
        if self.len * 2 > self.slots.len() {
            self.grow();
        }
    }

    /// Add `id` with hash `h`; the caller knows no equal key is present.
    pub fn insert_new(&mut self, h: u32, id: u32) {
        let mut i = self.start(h);
        while self.slot(i) != EMPTY {
            i = (i + 1) & self.mask();
        }
        self.insert_at(Slot(i), h, id);
    }

    #[cold]
    #[inline(never)]
    fn grow(&mut self) {
        let old = std::mem::replace(self, Table::with_slots(self.slots.len() * 2));
        for &v in old.slots.iter() {
            if v != EMPTY {
                let mut i = self.start((v >> 32) as u32);
                while self.slot(i) != EMPTY {
                    i = (i + 1) & self.mask();
                }
                self.slots[i] = v;
            }
        }
        self.len = old.len;
    }

    /// Empty the table, keeping its storage.
    pub fn clear(&mut self) {
        if self.len != 0 {
            self.slots.fill(EMPTY);
            self.len = 0;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn table_finds_what_it_holds() {
        let mut t = Table::new();
        let hash = |id: u32| (hash2(id as u64, 0) >> 32) as u32 & 0xf000_00ff;
        for id in 0..3_000u32 {
            match t.find_or_slot(hash(id), |x| x == id) {
                Ok(_) => panic!("{id} found before it was added"),
                Err(s) => t.insert_at(s, hash(id), id),
            }
        }
        assert_eq!(t.len(), 3_000);
        for id in 0..3_000u32 {
            assert_eq!(t.find(hash(id), |x| x == id), Some(id));
            assert_eq!(t.find_or_slot(hash(id), |x| x == id).ok(), Some(id));
        }
        assert_eq!(t.find(hash(10_001), |x| x == 10_001), None);
        t.clear();
        assert!(t.is_empty());
        assert_eq!(t.find(hash(5), |x| x == 5), None);
        t.insert_new(hash(5), 5);
        assert_eq!(t.find(hash(5), |x| x == 5), Some(5));
    }

    #[test]
    fn distinguishes_small_inputs() {
        assert_ne!(hash2(0, 1), hash2(1, 0));
        assert_ne!(hash_bytes(b"a"), hash_bytes(b"a\0"));
        assert_ne!(hash_bytes(b""), hash_bytes(b"\0"));
        assert_eq!(hash_bytes(b"Nat.succ"), hash_bytes(b"Nat.succ"));
    }
}
