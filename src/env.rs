//! Declarations, and the environment that holds them with their arenas.
//!
//! The field set mirrors Lean's `ConstantInfo` (`src/Lean/Declaration.lean`)
//! as written by `leanexport`. Lists of names (level parameters, `all`,
//! constructors) are ranges into one shared pool, so a declaration owns no
//! heap memory of its own.

use hashbrown::{HashMap, HashSet};

use num_bigint::BigUint;

use crate::expr::{ExprId, ExprNode, Exprs, LetBinder};
use crate::level::{LevelId, LevelList, LevelNode, Levels};
use crate::name::{NameId, NameNode, Names};

/// A list of names, as a range into [`Env::name_list`].
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct NameList {
    pub(crate) start: u32,
    pub(crate) len: u32,
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
    pub(crate) start: u32,
    pub(crate) len: u32,
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

/// Lazily read values: a value left in its `.olean` file has the id
/// `LAZY_BASE + k` until it is decoded ([`Env::value_into`]). Such an id
/// is never a valid id in the shared arena or in a checker's overlay
/// (which uses ids from 2^31 up, far fewer than 2^31 - 2^28 of them).
pub const LAZY_BASE: u32 = u32::MAX - (1 << 28);

/// Whether `e` stands for a value left in its file.
#[inline]
pub fn is_lazy(e: ExprId) -> bool {
    e.0 >= LAZY_BASE
}

/// Where [`Env::value_into`] builds a lazily read value: a checker's own
/// store, which looks each node up in the shared arena first. Nodes come
/// children first; names after their prefixes. Strings are the shared
/// pool's ([`crate::strings::StrPool::intern_late`] adds those first met in
/// a lazily read value).
pub trait TermSink {
    fn name(&mut self, node: NameNode) -> NameId;
    fn level(&mut self, node: LevelNode) -> LevelId;
    fn list(&mut self, levels: &[LevelId]) -> LevelList;
    /// A node other than `Let` and big literals.
    fn expr(&mut self, node: ExprNode) -> ExprId;
    /// A compound node (not `Let`) that no other term uses: the sink may
    /// give it an id of its own without looking it up or indexing it (so
    /// an equal node may get another id).
    fn expr_owned(&mut self, node: ExprNode) -> ExprId {
        self.expr(node)
    }
    fn let_in(&mut self, binder: LetBinder, body: ExprId) -> ExprId;
    /// A natural number literal of at least 2^64.
    fn nat_big(&mut self, n: BigUint) -> ExprId;
    /// A name of the shared arena (a subterm decoded at load time): the
    /// sink's id for it. A store above the same environment keeps it.
    fn shared_name(&mut self, n: NameId) -> NameId {
        n
    }
    /// An expression of the shared arena, likewise.
    fn shared_expr(&mut self, e: ExprId) -> ExprId {
        e
    }
    /// Whether [`TermSink::shared_name`] and [`TermSink::shared_expr`]
    /// give back what they get (so a caller may skip them).
    fn keeps_shared(&self) -> bool {
        true
    }
}

/// The source of lazily read values (the `.olean` loader's).
pub(crate) trait LazyValues: Send + Sync {
    /// Decode value `k` into `sink`.
    fn decode(&self, env: &Env, k: u32, sink: &mut dyn TermSink) -> Result<ExprId, String>;
    /// [`LazyValues::decode`] into a checker's store.
    fn decode_store(
        &self,
        env: &Env,
        k: u32,
        sink: &mut crate::check::store::Store<'_>,
    ) -> Result<ExprId, String> {
        self.decode(env, k, sink)
    }
    fn count(&self) -> usize;
    fn heap_bytes(&self) -> usize;
}

/// Where a declaration's value is (see [`Env::value_into`]).
enum Lazy<'a> {
    /// Read at load time (or none).
    No(Option<ExprId>),
    /// Value `k` of a source.
    Yes(&'a dyn LazyValues, u32),
    /// Left in a file, with no source.
    Missing,
}

/// Declaration index by name. While names are added it is a flat array over
/// name ids (names are dense small integers), so a lookup is one load.
/// [`NameIndex::freeze`] then packs it to 16 bits a name: declarations are
/// numbered nearly in the order their names are, so within a group of
/// [`GROUP`] name ids the indices lie in a short range, and an entry is its
/// offset from the group's least index (0: no declaration). Offsets that do
/// not fit go to a side map. About 8.5 MB for Mathlib's 4.3M names, against
/// 17 MB flat, and a lookup is still one load of the entry (the bases are a
/// few KB).
#[derive(Default)]
pub(crate) struct NameIndex {
    v: Vec<u32>,
    small: Vec<u16>,
    bases: Vec<u32>,
    far: HashMap<u32, u32>,
}

/// Name ids per base in a frozen index.
const GROUP_BITS: u32 = 12;
const FAR: u16 = u16::MAX;

impl NameIndex {
    const NONE: u32 = u32::MAX;

    #[inline]
    pub(crate) fn get(&self, n: &NameId) -> Option<u32> {
        if self.small.is_empty() {
            return self
                .v
                .get(n.0 as usize)
                .copied()
                .filter(|&x| x != Self::NONE);
        }
        let e = *self.small.get(n.0 as usize)?;
        if e == 0 {
            None
        } else if e == FAR {
            self.far.get(&n.0).copied()
        } else {
            Some(self.bases[(n.0 >> GROUP_BITS) as usize] + u32::from(e) - 1)
        }
    }

    #[inline]
    pub(crate) fn contains_key(&self, n: &NameId) -> bool {
        self.get(n).is_some()
    }

    pub(crate) fn insert(&mut self, n: NameId, i: u32) -> Option<u32> {
        if !self.small.is_empty() {
            self.thaw();
        }
        let k = n.0 as usize;
        if k >= self.v.len() {
            // In 256K-entry steps: names are dense, so rounding up to a
            // power of two would touch up to twice the memory needed.
            self.v.resize((k + 1).next_multiple_of(1 << 18), Self::NONE);
        }
        let old = std::mem::replace(&mut self.v[k], i);
        (old != Self::NONE).then_some(old)
    }

    /// Packs the index once no more names are added. Lookups give the same
    /// answers; adding a name later unpacks it again.
    pub(crate) fn freeze(&mut self) {
        if !self.small.is_empty() || self.v.is_empty() {
            return;
        }
        let mut small = vec![0u16; self.v.len()];
        let mut bases = Vec::with_capacity((self.v.len() >> GROUP_BITS) + 1);
        let mut far = HashMap::new();
        for (g, chunk) in self.v.chunks(1 << GROUP_BITS).enumerate() {
            let base = chunk
                .iter()
                .copied()
                .filter(|&x| x != Self::NONE)
                .min()
                .unwrap_or(0);
            bases.push(base);
            for (j, &x) in chunk.iter().enumerate() {
                if x == Self::NONE {
                    continue;
                }
                let k = (g << GROUP_BITS) + j;
                let off = x - base + 1;
                if off < u32::from(FAR) {
                    small[k] = off as u16;
                } else {
                    small[k] = FAR;
                    far.insert(k as u32, x);
                }
            }
        }
        self.small = small;
        self.bases = bases;
        self.far = far;
        self.v = Vec::new();
    }

    fn thaw(&mut self) {
        let mut v = vec![Self::NONE; self.small.len()];
        for (k, x) in v.iter_mut().enumerate() {
            if let Some(i) = self.get(&NameId(k as u32)) {
                *x = i;
            }
        }
        self.v = v;
        self.small = Vec::new();
        self.bases = Vec::new();
        self.far = HashMap::new();
    }

    pub(crate) fn heap_bytes(&self) -> usize {
        self.v.capacity() * 4
            + self.small.capacity() * 2
            + self.bases.capacity() * 4
            + self.far.capacity() * 9
    }
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
    pub(crate) by_name: NameIndex,
    pub(crate) lazy: Option<Box<dyn LazyValues>>,
    pub(crate) mdata_errors: HashMap<NameId, &'static str>,
    /// The inductive types and constructors whose exported type contains
    /// metadata (Lean's quotient check compares `Eq`'s syntactically).
    pub(crate) mdata_types: HashSet<NameId>,
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

    /// The value of a definition, theorem or opaque constant (`None` for
    /// other kinds). A value read at load time is the shared arena's id; a
    /// value left in its `.olean` file is decoded into `sink`, every time
    /// this is called (nothing is cached, so the shared arena never
    /// changes). An error means the file is malformed.
    pub fn value_into(&self, d: &Decl, sink: &mut dyn TermSink) -> Result<Option<ExprId>, String> {
        match self.lazy_value(d) {
            Lazy::No(v) => Ok(v),
            Lazy::Yes(l, k) => l.decode(self, k, sink).map(Some),
            Lazy::Missing => Err("internal: a lazy value without its source".into()),
        }
    }

    /// [`Env::value_into`] a checker's store.
    pub(crate) fn value_into_store(
        &self,
        d: &Decl,
        sink: &mut crate::check::store::Store<'_>,
    ) -> Result<Option<ExprId>, String> {
        match self.lazy_value(d) {
            Lazy::No(v) => Ok(v),
            Lazy::Yes(l, k) => l.decode_store(self, k, sink).map(Some),
            Lazy::Missing => Err("internal: a lazy value without its source".into()),
        }
    }

    /// Where the value of `d` is.
    fn lazy_value(&self, d: &Decl) -> Lazy<'_> {
        let v = match d.kind {
            DeclKind::Definition { value, .. }
            | DeclKind::Theorem { value, .. }
            | DeclKind::Opaque { value, .. } => value,
            _ => return Lazy::No(None),
        };
        if !is_lazy(v) {
            return Lazy::No(Some(v));
        }
        match &self.lazy {
            Some(l) => Lazy::Yes(&**l, v.0 - LAZY_BASE),
            None => Lazy::Missing,
        }
    }

    /// Number of values left in their files.
    pub fn lazy_values(&self) -> usize {
        self.lazy.as_ref().map_or(0, |l| l.count())
    }

    /// The declaration named `n`, if any.
    pub fn find(&self, n: NameId) -> Option<&Decl> {
        self.by_name.get(&n).map(|i| &self.decls[i as usize])
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

    /// Packs the name index once no more declarations are added (lookups
    /// answer as before; a later addition unpacks it).
    pub fn finish_loading(&mut self) {
        self.by_name.freeze();
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
            + self.by_name.heap_bytes()
            + self.lazy.as_ref().map_or(0, |l| l.heap_bytes())
    }
}

#[cfg(test)]
mod name_index_tests {
    use super::*;

    #[test]
    fn frozen_index_answers_as_the_flat_one() {
        let mut ix = NameIndex::default();
        let ids: Vec<u32> = (0..20000u32)
            .filter(|i| i % 7 == 0 || i % 31 == 5)
            .collect();
        for (j, &i) in ids.iter().enumerate() {
            // Mostly in order, with some far away.
            let idx = if i % 1001 == 0 {
                400_000 + j as u32
            } else {
                j as u32
            };
            assert_eq!(ix.insert(NameId(i), idx), None);
        }
        assert_eq!(ix.insert(NameId(0), 9), Some(400_000));
        let want: Vec<Option<u32>> = (0..30000u32).map(|i| ix.get(&NameId(i))).collect();
        ix.freeze();
        assert!(!ix.small.is_empty() && !ix.far.is_empty());
        let got: Vec<Option<u32>> = (0..30000u32).map(|i| ix.get(&NameId(i))).collect();
        assert_eq!(want, got);
        assert!(ix.get(&NameId(u32::MAX)).is_none());
        assert_eq!(ix.insert(NameId(7), 1), want[7]);
        assert_eq!(ix.get(&NameId(14)), want[14]);
    }
}
