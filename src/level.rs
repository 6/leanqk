//! Universe levels (`Lean.Level`), hash-consed with a summary of each
//! level's parameters. Also interned lists of levels, for `Expr.const`.

use hashbrown::HashTable;

use crate::hash::hash2;
use crate::intern::{Interner, Node};
use crate::name::NameId;
use crate::strings::Overflow;

/// Id of an interned level. `LevelId::ZERO` is `Level.zero`.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct LevelId(pub(crate) u32);

impl LevelId {
    pub const ZERO: LevelId = LevelId(0);

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LevelNode {
    Zero,
    Succ(LevelId),
    Max(LevelId, LevelId),
    IMax(LevelId, LevelId),
    Param(NameId),
}

impl Node for LevelNode {
    #[inline]
    fn hash(&self) -> u64 {
        let (tag, a, b) = match *self {
            LevelNode::Zero => (0, 0, 0),
            LevelNode::Succ(l) => (1, l.0, 0),
            LevelNode::Max(l, r) => (2, l.0, r.0),
            LevelNode::IMax(l, r) => (3, l.0, r.0),
            LevelNode::Param(n) => (4, n.0, 0),
        };
        hash2(tag | (a as u64) << 8, b as u64)
    }
}

/// The parameter names of a level, summarized when it is interned.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum LevelParams {
    None,
    One(NameId),
    Many,
}

impl LevelParams {
    pub(crate) fn of_node(node: LevelNode, params: impl Fn(LevelId) -> Self) -> Self {
        match node {
            LevelNode::Zero => Self::None,
            LevelNode::Param(n) => Self::One(n),
            LevelNode::Succ(l) => params(l),
            LevelNode::Max(a, b) | LevelNode::IMax(a, b) => {
                let pa = params(a);
                if pa == Self::Many {
                    return Self::Many;
                }
                let pb = params(b);
                match (pa, pb) {
                    (Self::None, p) | (p, Self::None) => p,
                    (p, q) if p == q => p,
                    _ => Self::Many,
                }
            }
        }
    }
}

/// Id of an interned list of levels. `LevelList::EMPTY` is `[]`.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
pub struct LevelList(pub(crate) u32);

impl LevelList {
    pub const EMPTY: LevelList = LevelList(0);
}

pub struct Levels {
    arena: Interner<LevelNode>,
    params: Vec<LevelParams>,
    // Interned lists: concatenated elements, offsets (list `i` is from
    // `list_offs[i]` to `list_offs[i + 1]`), and a flag per list.
    list_data: Vec<LevelId>,
    list_offs: Vec<u32>,
    list_has_param: Vec<bool>,
    list_table: HashTable<u32>,
}

impl Default for Levels {
    fn default() -> Self {
        Self::new()
    }
}

pub(crate) fn list_hash(ls: &[LevelId]) -> u64 {
    let mut hash = ls.len() as u64;
    let (pairs, rest) = ls.as_chunks::<2>();
    for &[a, b] in pairs {
        hash = hash2(hash, a.0 as u64 | ((b.0 as u64) << 32));
    }
    if let [a] = *rest {
        hash = hash2(hash, a.0 as u64);
    }
    hash
}

/// List `i` of a store of lists: `data`, with `offs` (list `i` is from
/// `offs[i]` to `offs[i + 1]`).
#[inline(always)]
pub(crate) fn list_at<'a>(data: &'a [LevelId], offs: &[u32], i: usize) -> &'a [LevelId] {
    let [a, b] = *offs[i..].first_chunk().expect("a list id");
    &data[a as usize..b as usize]
}

impl Levels {
    pub fn new() -> Self {
        let mut arena = Interner::new("too many universe levels");
        let (zero, _) = arena.intern(LevelNode::Zero).expect("empty arena");
        debug_assert_eq!(zero, LevelId::ZERO.0);
        Levels {
            arena,
            params: vec![LevelParams::None],
            list_data: Vec::new(),
            list_offs: vec![0, 0],
            list_has_param: vec![false],
            list_table: HashTable::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.arena.len()
    }

    pub fn is_empty(&self) -> bool {
        false
    }

    #[inline]
    pub fn get(&self, l: LevelId) -> LevelNode {
        *self.arena.get(l.0)
    }

    #[inline]
    pub fn has_param(&self, l: LevelId) -> bool {
        self.params(l) != LevelParams::None
    }

    #[inline]
    pub(crate) fn params(&self, l: LevelId) -> LevelParams {
        self.params[l.index()]
    }

    pub fn intern(&mut self, node: LevelNode) -> Result<(LevelId, bool), Overflow> {
        let (id, fresh) = self.arena.intern(node)?;
        if fresh {
            let params = LevelParams::of_node(node, |l| self.params(l));
            self.params.push(params);
        }
        Ok((LevelId(id), fresh))
    }

    /// Number of interned level lists, counting `[]`.
    pub fn list_count(&self) -> usize {
        self.list_offs.len() - 1
    }

    #[inline(always)]
    pub fn list(&self, l: LevelList) -> &[LevelId] {
        list_at(&self.list_data, &self.list_offs, l.0 as usize)
    }

    pub fn list_has_param(&self, l: LevelList) -> bool {
        self.list_has_param[l.0 as usize]
    }

    /// The id of `node`, if interned here.
    #[inline]
    pub(crate) fn find(&self, node: &LevelNode) -> Option<LevelId> {
        self.arena.find(node).map(LevelId)
    }

    /// The id of the list `ls`, if interned here.
    pub(crate) fn find_list(&self, ls: &[LevelId]) -> Option<LevelList> {
        if ls.is_empty() {
            return Some(LevelList::EMPTY);
        }
        self.list_table
            .find(list_hash(ls), |&id| self.list(LevelList(id)) == ls)
            .map(|&id| LevelList(id))
    }

    pub fn intern_list(&mut self, ls: &[LevelId]) -> Result<LevelList, Overflow> {
        if ls.is_empty() {
            return Ok(LevelList::EMPTY);
        }
        let h = list_hash(ls);
        let Self {
            list_data,
            list_offs,
            list_table,
            ..
        } = self;
        if let Some(&id) =
            list_table.find(h, |&id| list_at(list_data, list_offs, id as usize) == ls)
        {
            return Ok(LevelList(id));
        }
        let end = list_data.len() + ls.len();
        if end > u32::MAX as usize || list_offs.len() > u32::MAX as usize {
            return Err(Overflow("too many universe level lists"));
        }
        let id = (list_offs.len() - 1) as u32;
        list_data.extend_from_slice(ls);
        list_offs.push(end as u32);
        let (list_data, list_offs) = (&*list_data, &*list_offs);
        list_table.insert_unique(h, id, |&id| {
            list_hash(list_at(list_data, list_offs, id as usize))
        });
        let hp = ls.iter().any(|&l| self.has_param(l));
        self.list_has_param.push(hp);
        Ok(LevelList(id))
    }

    pub fn heap_bytes(&self) -> usize {
        self.arena.heap_bytes()
            + self.params.capacity() * size_of::<LevelParams>()
            + self.list_data.capacity() * 4
            + self.list_offs.capacity() * 4
            + self.list_has_param.capacity()
            + self.list_table.capacity() * 5
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn levels_and_lists() {
        let mut ls = Levels::new();
        let (one, _) = ls.intern(LevelNode::Succ(LevelId::ZERO)).unwrap();
        let (one2, fresh) = ls.intern(LevelNode::Succ(LevelId::ZERO)).unwrap();
        assert_eq!(one, one2);
        assert!(!fresh);
        let (u, _) = ls.intern(LevelNode::Param(NameId(3))).unwrap();
        let (m, _) = ls.intern(LevelNode::Max(one, u)).unwrap();
        assert!(ls.has_param(m) && !ls.has_param(one));
        let a = ls.intern_list(&[one, u]).unwrap();
        let b = ls.intern_list(&[one, u]).unwrap();
        let c = ls.intern_list(&[u, one]).unwrap();
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_eq!(ls.list(a), &[one, u]);
        assert_eq!(ls.intern_list(&[]).unwrap(), LevelList::EMPTY);
        assert!(ls.list(LevelList::EMPTY).is_empty());
        assert!(ls.list_has_param(a));
        assert_eq!(size_of::<LevelNode>(), 12);
    }
}
