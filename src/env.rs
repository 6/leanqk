//! Declarations, and the environment that holds them with their arenas.
//!
//! The field set mirrors Lean's `ConstantInfo` (`src/Lean/Declaration.lean`)
//! as written by `leanexport`. Lists of names (level parameters, `all`,
//! constructors) are ranges into one shared pool, so a declaration owns no
//! heap memory of its own.

use hashbrown::HashMap;

use crate::expr::{ExprId, Exprs};
use crate::level::Levels;
use crate::name::{NameId, Names};

/// A list of names, as a range into [`Env::name_list`].
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct NameList {
    start: u32,
    len: u32,
}

impl NameList {
    pub fn len(self) -> usize {
        self.len as usize
    }

    pub fn is_empty(self) -> bool {
        self.len == 0
    }
}

/// A range of recursor rules in [`Env::rec_rules`].
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct RuleList {
    start: u32,
    len: u32,
}

impl RuleList {
    pub fn len(self) -> usize {
        self.len as usize
    }

    pub fn is_empty(self) -> bool {
        self.len == 0
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Hints {
    Opaque,
    Abbrev,
    Regular(u32),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Safety {
    Unsafe,
    Safe,
    Partial,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum QuotKind {
    Type,
    Ctor,
    Lift,
    Ind,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct RecRule {
    pub ctor: NameId,
    pub nfields: u32,
    pub rhs: ExprId,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DeclKind {
    Axiom {
        is_unsafe: bool,
    },
    Definition {
        value: ExprId,
        hints: Hints,
        safety: Safety,
        all: NameList,
    },
    Theorem {
        value: ExprId,
        all: NameList,
    },
    Opaque {
        value: ExprId,
        all: NameList,
        is_unsafe: bool,
    },
    Quot {
        kind: QuotKind,
    },
    Inductive {
        num_params: u32,
        num_indices: u32,
        all: NameList,
        ctors: NameList,
        num_nested: u32,
        is_rec: bool,
        is_reflexive: bool,
        is_unsafe: bool,
    },
    Constructor {
        induct: NameId,
        cidx: u32,
        num_params: u32,
        num_fields: u32,
        is_unsafe: bool,
    },
    Recursor {
        all: NameList,
        num_params: u32,
        num_indices: u32,
        num_motives: u32,
        num_minors: u32,
        rules: RuleList,
        k: bool,
        is_unsafe: bool,
    },
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Decl {
    pub name: NameId,
    pub level_params: NameList,
    pub ty: ExprId,
    pub kind: DeclKind,
}

/// One export record's worth of declarations, in file order. An inductive
/// record holds its types, then its constructors, then its recursors.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Block {
    /// First declaration, an index into [`Env::decls`].
    pub start: u32,
    pub kind: BlockKind,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BlockKind {
    Single,
    Inductive { types: u32, ctors: u32, recs: u32 },
}

impl Block {
    pub fn len(&self) -> usize {
        match self.kind {
            BlockKind::Single => 1,
            BlockKind::Inductive { types, ctors, recs } => (types + ctors + recs) as usize,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// Metadata from the export's first line.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Meta {
    pub format_version: String,
    pub exporter_name: Option<String>,
    pub exporter_version: Option<String>,
    pub lean_version: Option<String>,
    pub lean_githash: Option<String>,
}

/// Counts of declarations per kind.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DeclCounts {
    pub axioms: usize,
    pub definitions: usize,
    pub theorems: usize,
    pub opaques: usize,
    pub quotients: usize,
    pub inductives: usize,
    pub constructors: usize,
    pub recursors: usize,
}

#[derive(Default)]
pub struct Env {
    pub meta: Meta,
    pub names: Names,
    pub levels: Levels,
    pub exprs: Exprs,
    pub decls: Vec<Decl>,
    pub blocks: Vec<Block>,
    pub(crate) name_pool: Vec<NameId>,
    pub(crate) rule_pool: Vec<RecRule>,
    pub(crate) by_name: HashMap<NameId, u32>,
}

impl Env {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn name_list(&self, l: NameList) -> &[NameId] {
        &self.name_pool[l.start as usize..(l.start + l.len) as usize]
    }

    pub fn rec_rules(&self, l: RuleList) -> &[RecRule] {
        &self.rule_pool[l.start as usize..(l.start + l.len) as usize]
    }

    pub fn block_decls(&self, b: &Block) -> &[Decl] {
        &self.decls[b.start as usize..b.start as usize + b.len()]
    }

    /// The declaration named `n`, if any.
    pub fn find(&self, n: NameId) -> Option<&Decl> {
        self.by_name.get(&n).map(|&i| &self.decls[i as usize])
    }

    /// The declaration with the dotted name `s`, if any.
    pub fn find_dotted(&self, s: &str) -> Option<&Decl> {
        self.find(self.names.find_dotted(s)?)
    }

    pub(crate) fn push_names(&mut self, ns: &[NameId]) -> Option<NameList> {
        let start = u32::try_from(self.name_pool.len()).ok()?;
        let len = u32::try_from(ns.len()).ok()?;
        start.checked_add(len)?;
        self.name_pool.extend_from_slice(ns);
        Some(NameList { start, len })
    }

    pub(crate) fn push_rules(&mut self, rs: &[RecRule]) -> Option<RuleList> {
        let start = u32::try_from(self.rule_pool.len()).ok()?;
        let len = u32::try_from(rs.len()).ok()?;
        start.checked_add(len)?;
        self.rule_pool.extend_from_slice(rs);
        Some(RuleList { start, len })
    }

    pub fn counts(&self) -> DeclCounts {
        let mut c = DeclCounts::default();
        for d in &self.decls {
            match d.kind {
                DeclKind::Axiom { .. } => c.axioms += 1,
                DeclKind::Definition { .. } => c.definitions += 1,
                DeclKind::Theorem { .. } => c.theorems += 1,
                DeclKind::Opaque { .. } => c.opaques += 1,
                DeclKind::Quot { .. } => c.quotients += 1,
                DeclKind::Inductive { .. } => c.inductives += 1,
                DeclKind::Constructor { .. } => c.constructors += 1,
                DeclKind::Recursor { .. } => c.recursors += 1,
            }
        }
        c
    }

    /// Approximate heap bytes held by the environment.
    pub fn heap_bytes(&self) -> usize {
        self.names.heap_bytes()
            + self.levels.heap_bytes()
            + self.exprs.heap_bytes()
            + self.decls.capacity() * size_of::<Decl>()
            + self.blocks.capacity() * size_of::<Block>()
            + self.name_pool.capacity() * 4
            + self.rule_pool.capacity() * size_of::<RecRule>()
            + self.by_name.capacity() * 9
    }
}
