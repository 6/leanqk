//! A generic hash-consing arena: nodes live in one `Vec`, and a SwissTable
//! of `u32` ids (5 bytes per slot including the control byte) finds the
//! existing copy of a node. Nodes refer to children by id, so equality and
//! hashing are shallow, and two ids are equal iff their terms are.

use hashbrown::HashTable;
use hashbrown::hash_table::Entry;

use crate::strings::Overflow;

/// A node that can be hash-consed. Children must be canonical ids.
pub trait Node: Copy + Eq {
    fn hash(&self) -> u64;

    /// The equality the table interns by; `hash` must agree with it.
    /// Defaults to `==`.
    #[inline]
    fn same(&self, other: &Self) -> bool {
        self == other
    }
}

pub struct Interner<T> {
    nodes: Vec<T>,
    table: HashTable<u32>,
    what: &'static str,
}

#[allow(dead_code)] // `is_empty`, `nodes` and `reserve` are kept for symmetry with `Sharded`.
impl<T: Node> Interner<T> {
    pub fn new(what: &'static str) -> Self {
        Interner {
            nodes: Vec::new(),
            table: HashTable::new(),
            what,
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    #[inline]
    pub fn get(&self, id: u32) -> &T {
        &self.nodes[id as usize]
    }

    #[inline]
    pub fn nodes(&self) -> &[T] {
        &self.nodes
    }

    /// The id of `node`, if present.
    pub fn find(&self, node: &T) -> Option<u32> {
        let nodes = &self.nodes;
        self.table
            .find(node.hash(), |&id| nodes[id as usize].same(node))
            .copied()
    }

    /// Return the id of `node`, adding it if new. The flag says whether it
    /// was added.
    #[inline]
    pub fn intern(&mut self, node: T) -> Result<(u32, bool), Overflow> {
        let h = node.hash();
        let Self { nodes, table, what } = self;
        let id = nodes.len() as u32;
        match table.entry(
            h,
            |&id| nodes[id as usize].same(&node),
            |&id| nodes[id as usize].hash(),
        ) {
            Entry::Occupied(e) => Ok((*e.get(), false)),
            Entry::Vacant(e) => {
                // u32::MAX is kept free as a sentinel.
                if id >= u32::MAX - 1 {
                    return Err(Overflow(what));
                }
                e.insert(id);
                nodes.push(node);
                Ok((id, true))
            }
        }
    }

    /// Make room for `extra` more nodes without rehashing.
    pub fn reserve(&mut self, extra: usize) {
        let Self { nodes, table, .. } = self;
        nodes.reserve(extra);
        let nodes = &*nodes;
        table.reserve(extra, |&id| nodes[id as usize].hash());
    }

    pub fn heap_bytes(&self) -> usize {
        self.nodes.capacity() * size_of::<T>() + self.table.capacity() * 5
    }
}

/// A [`Interner`] whose table is split into [`SHARDS`] shards, chosen by
/// hash bits that the SwissTable itself does not use (it takes the top 7
/// bits for control bytes and the low bits for the bucket), so lookups
/// cost the same. Used for the environment's big expression arena: the
/// `.olean` loader builds the shards in parallel and hands them over
/// ([`Sharded::from_parts`]). The checker's small overlay arenas stay
/// unsharded.
pub struct Sharded<T> {
    nodes: Vec<T>,
    tables: Box<[HashTable<u32>]>,
    what: &'static str,
}

pub const SHARDS: usize = 64;

/// The shard of a hash.
#[inline]
pub fn shard_of(h: u64) -> usize {
    (h >> 51) as usize & (SHARDS - 1)
}

impl<T: Node> Sharded<T> {
    pub fn new(what: &'static str) -> Self {
        Sharded {
            nodes: Vec::new(),
            tables: (0..SHARDS).map(|_| HashTable::new()).collect(),
            what,
        }
    }

    /// An arena of `nodes` with shard tables that index them: each node's
    /// id in the shard of its hash. The caller guarantees that the nodes
    /// are pairwise distinct under [`Node::same`] and the tables complete.
    pub(crate) fn from_parts(
        nodes: Vec<T>,
        tables: Vec<HashTable<u32>>,
        what: &'static str,
    ) -> Self {
        assert_eq!(tables.len(), SHARDS);
        debug_assert_eq!(tables.iter().map(|t| t.len()).sum::<usize>(), nodes.len());
        Sharded {
            nodes,
            tables: tables.into_boxed_slice(),
            what,
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    #[inline]
    pub fn get(&self, id: u32) -> &T {
        &self.nodes[id as usize]
    }

    #[inline]
    pub fn nodes(&self) -> &[T] {
        &self.nodes
    }

    /// The id of `node`, if present.
    pub fn find(&self, node: &T) -> Option<u32> {
        let nodes = &self.nodes;
        let h = node.hash();
        self.tables[shard_of(h)]
            .find(h, |&id| nodes[id as usize].same(node))
            .copied()
    }

    /// Return the id of `node`, adding it if new. The flag says whether it
    /// was added.
    #[inline]
    pub fn intern(&mut self, node: T) -> Result<(u32, bool), Overflow> {
        let h = node.hash();
        let Self {
            nodes,
            tables,
            what,
        } = self;
        let id = nodes.len() as u32;
        match tables[shard_of(h)].entry(
            h,
            |&id| nodes[id as usize].same(&node),
            |&id| nodes[id as usize].hash(),
        ) {
            Entry::Occupied(e) => Ok((*e.get(), false)),
            Entry::Vacant(e) => {
                // u32::MAX is kept free as a sentinel.
                if id >= u32::MAX - 1 {
                    return Err(Overflow(what));
                }
                e.insert(id);
                nodes.push(node);
                Ok((id, true))
            }
        }
    }

    /// Make room for `extra` more nodes without rehashing (if they spread
    /// evenly over the shards).
    pub fn reserve(&mut self, extra: usize) {
        let Self { nodes, tables, .. } = self;
        nodes.reserve(extra);
        let nodes = &*nodes;
        let per = extra / SHARDS + extra / (4 * SHARDS) + 16;
        for t in tables.iter_mut() {
            t.reserve(per, |&id| nodes[id as usize].hash());
        }
    }

    pub fn heap_bytes(&self) -> usize {
        self.nodes.capacity() * size_of::<T>()
            + self.tables.iter().map(|t| t.capacity() * 5).sum::<usize>()
    }
}
