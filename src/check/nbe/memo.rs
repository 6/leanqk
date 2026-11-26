//! Memos keyed by a term, its universe substitution and the entries of its
//! environment it reads: terms met again in environments that agree where
//! they look find what was found, with no environment cut to build a key.

use hashbrown::HashTable;

use super::val::{Env, Ls, V, spread};
use super::{Nbe, val};
use crate::expr::ExprId;
use crate::hash::hash2;

/// Whether keys hold the id of the values read (`read_tuple`), not the
/// values.
const READ_TUPLES: bool = true;

/// Whether a key of a term that reads no value of its range (all holes)
/// takes a fixed id for the values read, with no tuple looked up.
const FAST_KEYS: bool = true;

/// The id of no values read (`FAST_KEYS`).
const EMPTY_TUPLE: u32 = val::NONE - 1;

/// Slots of `Nbe::tuple_slots`.
pub(super) const TUPLE_SLOTS: usize = 1 << 14;

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
        &self.keys[i..i + WORDS]
    }

    #[inline]
    pub fn set(&mut self, i: usize, w: usize, v: u32) {
        self.keys[i + w] = v;
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
            let t = if FAST_KEYS && n == d.loose_bvar_range() && n < 64 {
                // An empty list of values read is the same list whatever
                // the range and holes.
                if n == holes.count_ones() {
                    EMPTY_TUPLE
                } else {
                    self.read_tuple(env, n, holes)
                }
            } else {
                self.read_tuple(env, n, holes)
            };
            let h = hash2(e.0 as u64 | (ls2.0 as u64) << 32, t as u64);
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

    /// The id of the values of the first `n` entries of `env` but those
    /// `holes` sets (from bit 64 on, all): equal values, equal ids.
    fn read_tuple(&mut self, env: Env, n: u32, holes: u64) -> u32 {
        let si = (hash2(env.0 as u64 | (n as u64) << 32, holes) >> 50) as usize & (TUPLE_SLOTS - 1);
        let s = self.tuple_slots[si];
        if s[0] == env.0 && s[1] == n && s[2] == holes as u32 && s[3] == (holes >> 32) as u32 {
            return s[4];
        }
        let base = self.vargs.len();
        let mut cur = env;
        let mut h = hash2(n as u64, holes);
        for j in 0..n {
            if j >= 64 || holes >> j & 1 == 0 {
                let v = self.a.env_head(cur);
                h = (h.rotate_left(5) ^ v.0 as u64).wrapping_mul(0x517c_c1b7_2722_0a95);
                self.vargs.push(v);
            }
            cur = self.a.env_tail(cur);
        }
        let k = Key {
            h: (h >> 32) as u32,
            head: [
                0,
                0,
                n,
                holes as u32,
                (holes >> 32) as u32,
                (self.vargs.len() - base) as u32,
            ],
            base,
        };
        let (i, _) = Self::memo_find_or_add(&mut self.vargs, &mut self.tuples, k, []);
        let t = i as u32;
        self.tuple_slots[si] = [env.0, n, holes as u32, (holes >> 32) as u32, t];
        t
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
            keys[i] == k.h
                && keys[i + 1..i + 7] == k.head
                && keys[i + 7..i + 7 + cnt]
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
