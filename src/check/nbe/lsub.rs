//! Universe substitutions remembered: a direct-mapped table in front of a
//! map. Most lookups are for the few levels and lists of the declaration
//! at hand, which the table answers with one probe; the map keeps the rest.

use std::hash::Hash;

use crate::env::NameList;
use crate::name::NameId;

use super::super::store::{IdMap, Store};
use super::Cap;

/// Whether the substitution caches have the direct-mapped table.
pub const LSUB_DIRECT: bool = true;

const SLOTS: usize = 1 << 12;

/// A key of two 32-bit ids.
pub trait Key: Copy + Eq + Hash {
    fn bits(self) -> u64;
}

impl Key for (crate::level::LevelId, super::val::Ls) {
    fn bits(self) -> u64 {
        (self.0.0 as u64) << 32 | self.1.0 as u64
    }
}

impl Key for (crate::level::LevelList, super::val::Ls) {
    fn bits(self) -> u64 {
        (self.0.0 as u64) << 32 | self.1.0 as u64
    }
}

pub struct Lsub<K, V> {
    /// Slot `i` holds a key whose hash is `i` and its value; `None` empty.
    slots: Vec<Option<(K, V)>>,
    map: IdMap<K, V>,
}

impl<K, V> Default for Lsub<K, V> {
    fn default() -> Self {
        Lsub {
            slots: Vec::new(),
            map: IdMap::default(),
        }
    }
}

#[inline]
fn slot(bits: u64) -> usize {
    (bits.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> (64 - 12)) as usize
}

impl<K: Key, V: Copy> Lsub<K, V> {
    #[inline]
    pub fn get(&mut self, k: K) -> Option<V> {
        if LSUB_DIRECT
            && let Some(Some((k2, v))) = self.slots.get(slot(k.bits()))
            && *k2 == k
        {
            return Some(*v);
        }
        let v = *self.map.get(&k)?;
        self.put(k, v);
        Some(v)
    }

    pub fn insert(&mut self, k: K, v: V) {
        self.map.insert(k, v);
        self.put(k, v);
    }

    #[inline]
    fn put(&mut self, k: K, v: V) {
        if !LSUB_DIRECT {
            return;
        }
        if self.slots.is_empty() {
            self.slots.resize_with(SLOTS, || None);
        }
        self.slots[slot(k.bits())] = Some((k, v));
    }
}

impl<K, V> Cap for Lsub<K, V> {
    fn cap(&self) -> usize {
        self.map.cap()
    }

    fn clear_keep(&mut self) {
        self.map.clear_keep();
        for s in &mut self.slots {
            *s = None;
        }
    }
}

/// Whether constants whose universe parameters have the same names share
/// substitutions (`ParamClasses`).
pub const PARAM_CLASSES: bool = true;

/// One list of universe parameters per sequence of names: `c.{u}` at `v`
/// and `d.{u}` at `v` are then the same substitution, and what is cached
/// under it (levels, values) is shared. A substitution only depends on the
/// names it replaces and what it replaces them by.
#[derive(Default)]
pub struct ParamClasses {
    by_list: IdMap<u64, NameList>,
    by_names: std::collections::HashMap<Vec<NameId>, NameList>,
}

impl ParamClasses {
    pub fn class(&mut self, st: &Store<'_>, l: NameList) -> NameList {
        if !PARAM_CLASSES {
            return l;
        }
        let k = (l.start as u64) << 32 | l.len as u64;
        if let Some(&c) = self.by_list.get(&k) {
            return c;
        }
        let c = *self.by_names.entry(st.name_list(l).to_vec()).or_insert(l);
        self.by_list.insert(k, c);
        c
    }
}
