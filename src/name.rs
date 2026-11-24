//! Hierarchical names (`Lean.Name`), hash-consed. 16 bytes per node.

use std::fmt;

use crate::hash::hash2;
use crate::intern::{Interner, Node};
use crate::strings::{Overflow, StrId, StrPool};

/// Id of an interned name. `NameId::ANON` is the anonymous name.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct NameId(pub(crate) u32);

impl NameId {
    pub const ANON: NameId = NameId(0);

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NameNode {
    Anon,
    Str(NameId, StrId),
    Num(NameId, u64),
}

impl Node for NameNode {
    #[inline]
    fn hash(&self) -> u64 {
        match *self {
            NameNode::Anon => hash2(0, 0),
            NameNode::Str(p, s) => hash2(1 | (p.0 as u64) << 8, s.index() as u64),
            NameNode::Num(p, n) => hash2(2 | (p.0 as u64) << 8, n),
        }
    }
}

pub struct Names {
    arena: Interner<NameNode>,
    pub strings: StrPool,
}

impl Default for Names {
    fn default() -> Self {
        Self::new()
    }
}

impl Names {
    pub fn new() -> Self {
        let mut arena = Interner::new("too many names");
        let (anon, _) = arena.intern(NameNode::Anon).expect("empty arena");
        debug_assert_eq!(anon, NameId::ANON.0);
        Names {
            arena,
            strings: StrPool::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.arena.len()
    }

    pub fn is_empty(&self) -> bool {
        false
    }

    #[inline]
    pub fn get(&self, n: NameId) -> NameNode {
        *self.arena.get(n.0)
    }

    pub fn intern(&mut self, node: NameNode) -> Result<(NameId, bool), Overflow> {
        let (id, fresh) = self.arena.intern(node)?;
        Ok((NameId(id), fresh))
    }

    pub fn str(&mut self, pre: NameId, s: &str) -> Result<(NameId, bool), Overflow> {
        let s = self.strings.intern(s)?;
        self.intern(NameNode::Str(pre, s))
    }

    pub fn num(&mut self, pre: NameId, n: u64) -> Result<(NameId, bool), Overflow> {
        self.intern(NameNode::Num(pre, n))
    }

    /// The id of `node`, if present.
    pub fn find(&self, node: NameNode) -> Option<NameId> {
        self.arena.find(&node).map(NameId)
    }

    /// Look up a dotted name such as `Nat.succ` without adding anything.
    /// Components made only of digits are numeric. (Components containing
    /// dots cannot be written this way.)
    pub fn find_dotted(&self, s: &str) -> Option<NameId> {
        let mut n = NameId::ANON;
        for c in s.split('.') {
            let node = match c.parse::<u64>() {
                Ok(k) if c.bytes().all(|b| b.is_ascii_digit()) => NameNode::Num(n, k),
                _ => NameNode::Str(n, self.strings.find(c)?),
            };
            n = self.find(node)?;
        }
        Some(n)
    }

    /// Display adaptor, e.g. `Nat.succ` or `_private.Foo.0.bar`.
    pub fn display(&self, n: NameId) -> DisplayName<'_> {
        DisplayName { names: self, n }
    }

    pub fn heap_bytes(&self) -> usize {
        self.arena.heap_bytes() + self.strings.heap_bytes()
    }
}

pub struct DisplayName<'a> {
    names: &'a Names,
    n: NameId,
}

impl fmt::Display for DisplayName<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Collect components iteratively; names can be deep.
        let mut comps = Vec::new();
        let mut cur = self.n;
        loop {
            match self.names.get(cur) {
                NameNode::Anon => break,
                NameNode::Str(p, _) | NameNode::Num(p, _) => {
                    comps.push(cur);
                    cur = p;
                }
            }
        }
        if comps.is_empty() {
            return f.write_str("[anonymous]");
        }
        for (i, c) in comps.iter().rev().enumerate() {
            if i > 0 {
                f.write_str(".")?;
            }
            match self.names.get(*c) {
                NameNode::Str(_, s) => f.write_str(self.names.strings.get(s))?,
                NameNode::Num(_, k) => write!(f, "{k}")?,
                NameNode::Anon => {}
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hash_consing_and_display() {
        let mut ns = Names::new();
        let (nat, f1) = ns.str(NameId::ANON, "Nat").unwrap();
        let (succ, _) = ns.str(nat, "succ").unwrap();
        let (nat2, f2) = ns.str(NameId::ANON, "Nat").unwrap();
        let (n0, _) = ns.num(succ, 0).unwrap();
        assert!(f1 && !f2);
        assert_eq!(nat, nat2);
        assert_eq!(ns.display(n0).to_string(), "Nat.succ.0");
        assert_eq!(ns.display(NameId::ANON).to_string(), "[anonymous]");
        assert_eq!(size_of::<NameNode>(), 16);
        assert_eq!(ns.find_dotted("Nat.succ.0"), Some(n0));
        assert_eq!(ns.find_dotted("Nat"), Some(nat));
        assert_eq!(ns.find_dotted("Nat.zero"), None);
    }
}
