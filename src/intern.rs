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
}

pub struct Interner<T> {
    nodes: Vec<T>,
    table: HashTable<u32>,
    what: &'static str,
}

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
            .find(node.hash(), |&id| nodes[id as usize] == *node)
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
            |&id| nodes[id as usize] == node,
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
