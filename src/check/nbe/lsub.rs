//! Universe substitutions remembered: a direct-mapped table in front of a
//! map. Most lookups are for the few levels and lists of the declaration
//! at hand, which the table answers with one probe. The map keeps entries
//! evicted from the table.

use crate::env::NameList;
use crate::level::{LevelId, LevelList};
use crate::name::NameId;

use super::super::store::{IdMap, Store};
use super::super::univ;
use super::Cap;
use super::val::{Ls, LsNode};

/// Find the replacement for a parameter in an interned substitution.
pub(super) fn replacement(st: &Store<'_>, node: LsNode, name: NameId) -> Option<LevelId> {
    let i = st.name_list(node.params).iter().position(|&p| p == name)?;
    st.list(node.levels).get(i).copied()
}

/// Whether the substitution caches have the direct-mapped table.
pub const LSUB_DIRECT: bool = true;

const SLOTS: usize = 1 << 12;

/// A key of two 32-bit ids.
pub trait Key {
    type Value;

    fn bits(self) -> u64;
}

impl Key for (LevelId, Ls) {
    type Value = LevelId;

    fn bits(self) -> u64 {
        (self.0.0 as u64) << 32 | self.1.0 as u64
    }
}

impl Key for (LevelList, Ls) {
    type Value = LevelList;

    fn bits(self) -> u64 {
        (self.0.0 as u64) << 32 | self.1.0 as u64
    }
}

pub struct Lsub<V> {
    // Key zero denotes an empty slot. The callers handle Ls::ID directly.
    direct: Box<[(u64, V); SLOTS]>,
    map: IdMap<u64, V>,
}

impl<V: Copy + Default> Default for Lsub<V> {
    fn default() -> Self {
        Lsub {
            direct: vec![(0, V::default()); SLOTS]
                .into_boxed_slice()
                .try_into()
                .unwrap_or_else(|_| unreachable!()),
            map: IdMap::default(),
        }
    }
}

#[inline]
fn slot(bits: u64) -> usize {
    let id = (bits >> 32) as u32;
    let ls = bits as u32;
    let mixed = (id ^ (id >> 21)).wrapping_mul(0x9e37);
    mixed.wrapping_add(ls) as usize & (SLOTS - 1)
}

impl<V: Copy> Lsub<V> {
    #[inline(always)]
    pub fn get_direct(&self, k: impl Key<Value = V>) -> Option<V> {
        let bits = k.bits();
        debug_assert_ne!(bits, 0);
        if LSUB_DIRECT {
            let (key, value) = self.direct[slot(bits)];
            if key == bits {
                return Some(value);
            }
        }
        None
    }

    /// Look up an evicted entry and restore it to the direct table.
    #[inline]
    pub(super) fn get_evicted(&mut self, k: impl Key<Value = V>) -> Option<V> {
        let bits = k.bits();
        let v = *self.map.get(&bits)?;
        if LSUB_DIRECT {
            self.put(bits, v);
        }
        Some(v)
    }

    pub fn insert(&mut self, k: impl Key<Value = V>, v: V) {
        let bits = k.bits();
        debug_assert_ne!(bits, 0);
        if LSUB_DIRECT {
            self.put(bits, v);
        } else {
            self.map.insert(bits, v);
        }
    }

    fn put(&mut self, bits: u64, v: V) {
        let (old, value) = std::mem::replace(&mut self.direct[slot(bits)], (bits, v));
        if old != 0 {
            self.map.insert(old, value);
        }
    }
}

impl Lsub<LevelId> {
    #[inline]
    pub(super) fn instantiate_uncached(
        &mut self,
        st: &mut Store<'_>,
        l: LevelId,
        ls: Ls,
        node: LsNode,
    ) -> LevelId {
        let result = univ::instantiate_level(st, l, |st, n| replacement(st, node, n));
        self.insert((l, ls), result);
        result
    }
}

impl<V: Copy> Cap for Lsub<V> {
    fn cap(&self) -> usize {
        self.map.cap()
    }

    fn clear_keep(&mut self) {
        self.map.clear_keep();
        for (key, _) in self.direct.iter_mut() {
            *key = 0;
        }
    }
}

/// Recent declaration substitutions, keyed by the original parameter range
/// and the supplied levels. Their values are indices into the NbE arena.
pub(super) struct DeclLs(Box<[DeclLsSlot; Self::SLOTS]>);

#[derive(Clone, Copy)]
struct DeclLsSlot {
    params: NameList,
    levels: LevelList,
    value: Ls,
}

impl DeclLsSlot {
    const EMPTY: Self = Self {
        params: NameList { start: 0, len: 0 },
        levels: LevelList::EMPTY,
        value: Ls::ID,
    };
}

impl Default for DeclLs {
    fn default() -> Self {
        Self(Box::new([DeclLsSlot::EMPTY; Self::SLOTS]))
    }
}

impl DeclLs {
    const SLOTS: usize = 512;

    #[inline]
    pub fn get_or_insert(
        &mut self,
        params: NameList,
        levels: LevelList,
        build: impl FnOnce() -> Ls,
    ) -> Ls {
        debug_assert!(!params.is_empty());
        let key = (params.start as u64) << 32 | levels.0 as u64;
        let slot = &mut self.0[slot(key) & (Self::SLOTS - 1)];
        if slot.params == params && slot.levels == levels {
            return slot.value;
        }
        let value = build();
        *slot = DeclLsSlot {
            params,
            levels,
            value,
        };
        value
    }

    pub fn clear(&mut self) {
        self.0.fill(DeclLsSlot::EMPTY);
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
