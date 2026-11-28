//! Memos keyed by a term, its universe substitution and the entries of its
//! environment it reads: terms met again in environments that agree where
//! they look find what was found, with no environment cut to build a key.

use hashbrown::HashTable;

use super::val::{Env, Ls, V, spread};
use super::{Nbe, val};
use crate::expr::ExprId;
use crate::hash::{Table, fold32, hash_front, hash2};

/// Whether keys hold the id of the values read (`read_tuple`), not the
/// values.
const READ_TUPLES: bool = true;

/// Whether a key of a term that reads no value of its range (all holes)
/// takes a fixed id for the values read, with no tuple looked up.
const FAST_KEYS: bool = true;

/// The id of no values read (`FAST_KEYS`).
const EMPTY_TUPLE: u32 = val::NONE - 1;

/// The bit of a tuple id that is an environment's id (`read_tuple`).
const WHOLE_ENV: u32 = 1 << 31;

/// Slots of `Nbe::tuple_slots`.
pub(super) const TUPLE_SLOTS: usize = 1 << 13;

/// Interned tuples store the range, two hole words, and the values read.
#[derive(Default)]
pub(super) struct TupleMemo {
    table: Table,
    words: Vec<u32>,
}

impl TupleMemo {
    pub(super) fn heap_bytes(&self) -> usize {
        self.table.capacity() * size_of::<u64>() + self.words.capacity() * size_of::<u32>()
    }

    pub(super) fn clear(&mut self) {
        if self.table.capacity() > 1 << 16 {
            *self = Self::default();
        } else {
            self.table.clear();
            self.words.clear();
        }
    }
}

/// A memo of `WORDS` words per key (see the module).
pub struct EnvMemo<const WORDS: usize> {
    table: HashTable<u32>,
    /// Records: hash, term, substitution, range, holes (two words), number
    /// of values read, those values, then the `WORDS` words.
    keys: Vec<u32>,
}

impl<const WORDS: usize> Default for EnvMemo<WORDS> {
    fn default() -> Self {
        EnvMemo {
            table: HashTable::new(),
            keys: Vec::new(),
        }
    }
}

impl<const WORDS: usize> EnvMemo<WORDS> {
    /// Bytes held, roughly.
    pub fn heap_bytes(&self) -> usize {
        self.table.capacity() * 5 + self.keys.capacity() * 4
    }

    pub fn clear(&mut self) {
        if self.table.capacity() > 1 << 16 {
            *self = Self::default();
        } else {
            self.table.clear();
            self.keys.clear();
        }
    }

    /// The words at `i` (from `find_or_add`).
    #[inline]
    pub fn get(&self, i: usize) -> &[u32] {
        val::at_slice(&self.keys, i, i + WORDS)
    }

    #[inline]
    pub fn set(&mut self, i: usize, w: usize, v: u32) {
        self.keys[i + w] = v;
    }
}

/// Inference keys use a tuple id and hold the inferred type and check scope.
/// Each entry sits in its slot of an open-addressed table, so that the load
/// of the slot decides a lookup. Indices are slots: growth moves entries and
/// bumps `moves`, after which an index held from before is found again by its
/// key (`refind`).
pub(super) struct InferMemo {
    /// Term, substitution, tuple, then the type and its check scope: zero
    /// for unchecked, or `u32::MAX` when the check is independent of the
    /// universe parameter list. The term is `NONE` in an empty slot.
    slots: Box<[[u32; 5]]>,
    /// `32 - log2(slots.len())`.
    shift: u32,
    len: usize,
    /// Growths so far.
    pub(super) moves: u32,
}

/// Slots of a new table.
const INFER_MIN_SLOTS: usize = 16;

impl Default for InferMemo {
    fn default() -> Self {
        InferMemo::with_slots(INFER_MIN_SLOTS, 0)
    }
}

impl InferMemo {
    fn with_slots(n: usize, moves: u32) -> Self {
        InferMemo {
            slots: vec![[val::NONE; 5]; n].into_boxed_slice(),
            shift: 32 - n.trailing_zeros(),
            len: 0,
            moves,
        }
    }

    /// Bytes held: the table's 20-byte slots.
    pub fn heap_bytes(&self) -> usize {
        self.slots.len() * size_of::<[u32; 5]>()
    }

    #[inline(always)]
    fn start(&self, e: ExprId, ls: Ls, tuple: u32) -> usize {
        (fold32(hash_front(e.0 as u64 | (ls.0 as u64) << 32, tuple as u64)) >> self.shift) as usize
    }

    /// The index of the key, added (with no type, unchecked) if missing.
    #[inline]
    pub(super) fn find_or_add(&mut self, e: ExprId, ls: Ls, tuple: u32) -> usize {
        let mask = self.slots.len() - 1;
        let mut i = self.start(e, ls, tuple);
        loop {
            let s = val::at(&self.slots, i);
            if s[0] == e.0 && s[1] == ls.0 && s[2] == tuple {
                return i;
            }
            if s[0] == val::NONE {
                break;
            }
            i = (i + 1) & mask;
        }
        self.slots[i] = [e.0, ls.0, tuple, val::NONE, 0];
        self.len += 1;
        // Grow once more than half full, so that a probe always meets an
        // empty slot.
        if self.len * 2 > self.slots.len() {
            self.grow();
            return self.refind(e, ls, tuple);
        }
        i
    }

    /// The index of a key known to be present.
    pub(super) fn refind(&self, e: ExprId, ls: Ls, tuple: u32) -> usize {
        let mask = self.slots.len() - 1;
        let mut i = self.start(e, ls, tuple);
        loop {
            let s = val::at(&self.slots, i);
            if s[0] == e.0 && s[1] == ls.0 && s[2] == tuple {
                return i;
            }
            assert!(s[0] != val::NONE, "nitrolean: infer memo key lost");
            i = (i + 1) & mask;
        }
    }

    #[cold]
    #[inline(never)]
    fn grow(&mut self) {
        assert!(
            self.slots.len() < 1 << 31,
            "nitrolean: resource limit: memo too large"
        );
        let old = std::mem::replace(
            self,
            InferMemo::with_slots(self.slots.len() * 2, self.moves.wrapping_add(1)),
        );
        let mask = self.slots.len() - 1;
        for s in old.slots.iter() {
            if s[0] != val::NONE {
                let mut i = self.start(ExprId(s[0]), Ls(s[1]), s[2]);
                while self.slots[i][0] != val::NONE {
                    i = (i + 1) & mask;
                }
                self.slots[i] = *s;
            }
        }
        self.len = old.len;
    }

    /// The tuple of the key at `i`.
    #[inline]
    pub(super) fn tuple(&self, i: usize) -> u32 {
        val::at(&self.slots, i)[2]
    }

    /// The type and check scope at `i`.
    #[inline]
    pub(super) fn get(&self, i: usize) -> [u32; 2] {
        let s = val::at(&self.slots, i);
        [s[3], s[4]]
    }

    #[inline]
    pub(super) fn set(&mut self, i: usize, w: usize, v: u32) {
        self.slots[i][3 + w] = v;
    }

    pub(super) fn clear(&mut self) {
        if self.slots.len() > 1 << 17 {
            *self = Self::with_slots(INFER_MIN_SLOTS, self.moves.wrapping_add(1));
        } else if self.len != 0 {
            self.slots.fill([val::NONE; 5]);
            self.len = 0;
        }
    }
}

/// A key being looked up: its hash and fixed words; the values it reads
/// are on `Nbe::vargs` from `base`.
pub struct Key {
    h: u32,
    head: [u32; 6],
    base: usize,
}

impl Key {
    /// Hash, term, substitution and the id of the values read, if the key
    /// holds the id (`READ_TUPLES`).
    #[inline]
    pub fn by_tuple(&self) -> Option<[u32; 4]> {
        (self.head[2] == val::NONE).then_some([self.h, self.head[0], self.head[1], self.head[3]])
    }

    /// Drop the key, taking the values it read off `vargs`.
    #[inline]
    pub fn drop_in(self, vargs: &mut Vec<V>) {
        vargs.truncate(self.base);
    }
}

impl Nbe<'_> {
    /// The key of `e` in `env` under `ls`, reading the entries below its
    /// range but those `holes` sets (from bit 64 on, all are read); `None`
    /// past `max` entries in range. The values read are left on `vargs`
    /// (give the key to `memo_find_or_add`, which takes them off).
    #[inline]
    pub(super) fn memo_key(
        &mut self,
        e: ExprId,
        env: Env,
        ls: Ls,
        holes: u64,
        max: u32,
    ) -> Option<Key> {
        let d = self.st.data(e);
        let n = d.loose_bvar_range().min(self.a.env_len(env));
        if n > max {
            return None;
        }
        let ls2 = if d.has_level_param() { ls } else { Ls::ID };
        let holes = if n >= 64 {
            holes
        } else {
            holes & ((1u64 << n) - 1)
        };
        if READ_TUPLES {
            let t = self.memo_tuple(env, d.loose_bvar_range(), n, holes);
            let h = hash_front(e.0 as u64 | (ls2.0 as u64) << 32, t as u64);
            return Some(Key {
                h: (h >> 32) as u32,
                head: [e.0, ls2.0, val::NONE, t, 0, 0],
                base: self.vargs.len(),
            });
        }
        let base = self.vargs.len();
        let mut cur = env;
        let mut h = hash2(
            e.0 as u64 | (ls2.0 as u64) << 32,
            n as u64 ^ holes.rotate_left(17),
        );
        for j in 0..n {
            if j >= 64 || holes >> j & 1 == 0 {
                let v = self.a.env_head(cur);
                h = (h.rotate_left(5) ^ v.0 as u64).wrapping_mul(0x517c_c1b7_2722_0a95);
                self.vargs.push(v);
            }
            cur = self.a.env_tail(cur);
        }
        let cnt = (self.vargs.len() - base) as u32;
        Some(Key {
            h: (h >> 32) as u32,
            head: [e.0, ls2.0, n, holes as u32, (holes >> 32) as u32, cnt],
            base,
        })
    }

    /// The tuple id for a term's environment, with `holes` masked to `n`.
    #[inline]
    pub(super) fn memo_tuple(&mut self, env: Env, range: u32, n: u32, holes: u64) -> u32 {
        if FAST_KEYS && n == range && n < 64 && n == holes.count_ones() {
            // With the whole range present, every empty list is the same.
            return EMPTY_TUPLE;
        }
        self.read_tuple(env, n, holes)
    }

    /// The id of the values of the first `n` entries of `env` but those
    /// `holes` sets (from bit 64 on, all): equal values, equal ids.
    fn read_tuple(&mut self, env: Env, n: u32, holes: u64) -> u32 {
        // All of a whole environment: environments are hash-consed, so its
        // id names its values (with the top bit, which no record id has).
        if n < 64 && holes & ((1u64 << n) - 1) == 0 && n == self.a.env_len(env) {
            return env.0 | WHOLE_ENV;
        }
        let si = (crate::hash::hash_front(env.0 as u64 | (n as u64) << 32, holes) >> 50) as usize
            & (TUPLE_SLOTS - 1);
        let s = self.tuple_slots[si];
        if s[0] == env.0 && s[1] == n && s[2] == holes as u32 && s[3] == (holes >> 32) as u32 {
            return s[4];
        }
        let t = self.read_tuple_in_place(env, n, holes);
        self.tuple_slots[si] = [env.0, n, holes as u32, (holes >> 32) as u32, t];
        t
    }

    /// `read_tuple` past its front: the record is written at the end of
    /// `tuples` as it is read, and dropped if it is there already. Out of
    /// line, so that a call met in the front costs no frame for it.
    #[inline(never)]
    fn read_tuple_in_place(&mut self, env: Env, n: u32, holes: u64) -> u32 {
        let TupleMemo { table, words } = &mut self.tuples;
        let base = words.len();
        let head = [n, holes as u32, (holes >> 32) as u32];
        let mut cur = env;
        let mut mask = holes;
        let mut h = hash_front(n as u64, holes);
        let skipped = if n >= 64 {
            holes.count_ones()
        } else {
            (holes & ((1u64 << n) - 1)).count_ones()
        };
        // One extend of known length, not a check per push.
        let a = &self.a;
        words.extend(head.into_iter().chain((0..n - skipped).map(|_| {
            while mask & 1 != 0 {
                mask >>= 1;
                cur = a.env_tail(cur);
            }
            let v = a.env_head(cur);
            h = (h.rotate_left(5) ^ v.0 as u64).wrapping_mul(0x517c_c1b7_2722_0a95);
            mask >>= 1;
            cur = a.env_tail(cur);
            v.0
        })));
        let end = words.len();
        let len = end - base;
        let h = fold32(h);
        let slot = match table.find_or_slot(h, |i| {
            let i = i as usize;
            // Equal ranges and hole masks give equal numbers of values.
            // Word by word: a call to compare memory costs more than the
            // loop for records this short.
            (0..len).all(|j| *val::at(words, i + j) == *val::at(words, base + j))
        }) {
            Ok(i) => {
                words.truncate(base);
                return i;
            }
            Err(slot) => slot,
        };
        assert!(
            end < WHOLE_ENV as usize,
            "nitrolean: resource limit: memo too large"
        );
        let id = base as u32;
        table.insert_at(slot, h, id);
        id
    }

    /// The words of `k` in `memo` (by index, for `EnvMemo::get` and `set`),
    /// and whether they were there already; new words are `init`.
    pub(super) fn memo_find_or_add<const WORDS: usize>(
        vargs: &mut Vec<V>,
        memo: &mut EnvMemo<WORDS>,
        k: Key,
        init: [u32; WORDS],
    ) -> (usize, bool) {
        let vals = &vargs[k.base..];
        let EnvMemo { table, keys } = memo;
        let cnt = vals.len();
        let eq = |&i: &u32| {
            let i = i as usize;
            *val::at(keys, i) == k.h
                && (0..6).all(|j| *val::at(keys, i + 1 + j) == k.head[j])
                && val::at_slice(keys, i + 7, i + 7 + cnt)
                    .iter()
                    .zip(vals)
                    .all(|(&a, b)| a == b.0)
        };
        let r = match table.find(spread(k.h), eq) {
            Some(&i) => (i as usize + 7 + cnt, true),
            None => {
                let i = keys.len();
                assert!(
                    i + 7 + cnt + WORDS < val::NONE as usize,
                    "nitrolean: resource limit: memo too large"
                );
                keys.push(k.h);
                keys.extend_from_slice(&k.head);
                keys.extend(vals.iter().map(|v| v.0));
                keys.extend_from_slice(&init);
                let keys = &*keys;
                table.insert_unique(spread(k.h), i as u32, |&i| spread(keys[i as usize]));
                (i + 7 + cnt, false)
            }
        };
        vargs.truncate(k.base);
        r
    }
}
