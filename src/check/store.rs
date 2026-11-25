//! The term store a type checker works in: the environment's arenas,
//! read-only and shared, plus a private overlay for the names, levels,
//! expressions and declarations built while checking.
//!
//! Ids with the top bit set refer to the overlay. A node is looked up in
//! the environment's arena before it is added to the overlay (only when
//! all its children are environment ids: otherwise it cannot be there), so
//! every term still has exactly one id and id equality stays structural
//! equality. The overlay is dropped between declarations, which bounds the
//! memory a check holds and keeps the shared environment immutable, so
//! independent declarations can be checked on several threads, each with
//! its own store. (nanoda_lib also keeps per-checker arenas on top of a
//! shared one.)

use hashbrown::HashTable;
use num_bigint::BigUint;

use crate::env::{Decl, Env, NameList, RecRule, RuleList};
use crate::expr::{BigId, BinderInfo, ExprData, ExprId, ExprNode, LetBinder, LetId, big_hash};
use crate::intern::Interner;
use crate::level::{LevelId, LevelList, LevelNode, list_hash};
use crate::name::{NameId, NameNode};
use crate::strings::StrId;

/// The bit that marks an overlay id.
pub const LOCAL: u32 = 1 << 31;

#[inline]
pub fn is_local(id: u32) -> bool {
    id & LOCAL != 0
}

/// Raised (as a panic, caught by the driver) when an overlay outgrows its
/// 31-bit ids. Checking a declaration that builds two billion terms is a
/// resource failure, not a verdict.
pub const OVERFLOW_MSG: &str =
    "nitrolean: resource limit: a declaration built more than 2^31 terms";

fn local_id(i: u32) -> u32 {
    assert!(i < LOCAL, "{OVERFLOW_MSG}");
    i | LOCAL
}

pub struct Store<'e> {
    pub env: &'e Env,
    names: Interner<NameNode>,
    levels: Interner<LevelNode>,
    level_hp: Vec<bool>,
    list_data: Vec<LevelId>,
    list_ends: Vec<u32>,
    list_hp: Vec<bool>,
    list_table: HashTable<u32>,
    exprs: Interner<ExprNode>,
    edata: Vec<ExprData>,
    lets: Interner<LetBinder>,
    bigs: Vec<BigUint>,
    big_table: HashTable<u32>,
    decl_names: Vec<NameId>,
    decl_rules: Vec<RecRule>,
    /// Scratch memo for the traversals in `subst.rs`.
    pub(crate) memo: IdMap<(ExprId, u32), ExprId>,
}

impl<'e> Store<'e> {
    pub fn new(env: &'e Env) -> Self {
        Store {
            env,
            names: Interner::new("too many names"),
            levels: Interner::new("too many levels"),
            level_hp: Vec::new(),
            list_data: Vec::new(),
            list_ends: Vec::new(),
            list_hp: Vec::new(),
            list_table: HashTable::new(),
            exprs: Interner::new("too many expressions"),
            edata: Vec::new(),
            lets: Interner::new("too many let binders"),
            bigs: Vec::new(),
            big_table: HashTable::new(),
            decl_names: Vec::new(),
            decl_rules: Vec::new(),
            memo: IdMap::default(),
        }
    }

    /// Drop the overlay. Every overlay id becomes invalid.
    pub fn clear(&mut self) {
        let env = self.env;
        *self = Store::new(env);
    }

    /// Number of overlay expressions.
    pub fn local_exprs(&self) -> usize {
        self.exprs.len()
    }

    // ---- names ----

    #[inline]
    pub fn name(&self, n: NameId) -> NameNode {
        if is_local(n.0) {
            *self.names.get(n.0 & !LOCAL)
        } else {
            self.env.names.get(n)
        }
    }

    pub fn mk_name(&mut self, node: NameNode) -> NameId {
        let global = match node {
            NameNode::Anon => return NameId::ANON,
            NameNode::Str(p, _) | NameNode::Num(p, _) => !is_local(p.0),
        };
        if global && let Some(n) = self.env.names.find(node) {
            return n;
        }
        let (i, _) = self.names.intern(node).expect("names");
        NameId(local_id(i))
    }

    pub fn str(&self, s: StrId) -> &str {
        self.env.names.strings.get(s)
    }

    /// `n` with its prefix `old` replaced by `new`, if `old` is a prefix.
    pub fn replace_prefix(&mut self, n: NameId, old: NameId, new: NameId) -> Option<NameId> {
        if n == old {
            return Some(new);
        }
        match self.name(n) {
            NameNode::Anon => None,
            NameNode::Str(p, s) => {
                let p = self.replace_prefix(p, old, new)?;
                Some(self.mk_name(NameNode::Str(p, s)))
            }
            NameNode::Num(p, k) => {
                let p = self.replace_prefix(p, old, new)?;
                Some(self.mk_name(NameNode::Num(p, k)))
            }
        }
    }

    pub fn is_prefix_of(&self, pre: NameId, mut n: NameId) -> bool {
        loop {
            if n == pre {
                return true;
            }
            match self.name(n) {
                NameNode::Anon => return false,
                NameNode::Str(p, _) | NameNode::Num(p, _) => n = p,
            }
        }
    }

    pub fn show(&self, n: NameId) -> String {
        let mut comps = Vec::new();
        let mut cur = n;
        loop {
            match self.name(cur) {
                NameNode::Anon => break,
                NameNode::Str(p, s) => {
                    comps.push(self.str(s).to_string());
                    cur = p;
                }
                NameNode::Num(p, k) => {
                    comps.push(k.to_string());
                    cur = p;
                }
            }
        }
        if comps.is_empty() {
            return "[anonymous]".into();
        }
        comps.reverse();
        comps.join(".")
    }

    // ---- levels ----

    #[inline]
    pub fn level(&self, l: LevelId) -> LevelNode {
        if is_local(l.0) {
            *self.levels.get(l.0 & !LOCAL)
        } else {
            self.env.levels.get(l)
        }
    }

    #[inline]
    pub fn level_has_param(&self, l: LevelId) -> bool {
        if is_local(l.0) {
            self.level_hp[(l.0 & !LOCAL) as usize]
        } else {
            self.env.levels.has_param(l)
        }
    }

    pub fn mk_level(&mut self, node: LevelNode) -> LevelId {
        let global = match node {
            LevelNode::Zero => return LevelId::ZERO,
            LevelNode::Succ(a) => !is_local(a.0),
            LevelNode::Max(a, b) | LevelNode::IMax(a, b) => !is_local(a.0) && !is_local(b.0),
            LevelNode::Param(n) => !is_local(n.0),
        };
        if global && let Some(l) = self.env.levels.find(&node) {
            return l;
        }
        let (i, fresh) = self.levels.intern(node).expect("levels");
        if fresh {
            let hp = match node {
                LevelNode::Zero => false,
                LevelNode::Succ(a) => self.level_has_param(a),
                LevelNode::Max(a, b) | LevelNode::IMax(a, b) => {
                    self.level_has_param(a) || self.level_has_param(b)
                }
                LevelNode::Param(_) => true,
            };
            self.level_hp.push(hp);
        }
        LevelId(local_id(i))
    }

    pub fn succ(&mut self, l: LevelId) -> LevelId {
        self.mk_level(LevelNode::Succ(l))
    }

    pub fn max(&mut self, a: LevelId, b: LevelId) -> LevelId {
        self.mk_level(LevelNode::Max(a, b))
    }

    pub fn imax(&mut self, a: LevelId, b: LevelId) -> LevelId {
        self.mk_level(LevelNode::IMax(a, b))
    }

    pub fn param(&mut self, n: NameId) -> LevelId {
        self.mk_level(LevelNode::Param(n))
    }

    fn local_list(&self, i: usize) -> &[LevelId] {
        let start = if i == 0 {
            0
        } else {
            self.list_ends[i - 1] as usize
        };
        &self.list_data[start..self.list_ends[i] as usize]
    }

    #[inline]
    pub fn list(&self, l: LevelList) -> &[LevelId] {
        if is_local(l.0) {
            self.local_list((l.0 & !LOCAL) as usize)
        } else {
            self.env.levels.list(l)
        }
    }

    pub fn list_has_param(&self, l: LevelList) -> bool {
        if is_local(l.0) {
            self.list_hp[(l.0 & !LOCAL) as usize]
        } else {
            self.env.levels.list_has_param(l)
        }
    }

    pub fn mk_list(&mut self, ls: &[LevelId]) -> LevelList {
        if ls.is_empty() {
            return LevelList::EMPTY;
        }
        if ls.iter().all(|l| !is_local(l.0))
            && let Some(l) = self.env.levels.find_list(ls)
        {
            return l;
        }
        let h = list_hash(ls);
        let Self {
            list_data,
            list_ends,
            list_table,
            ..
        } = self;
        let slice = |i: usize| {
            let start = if i == 0 { 0 } else { list_ends[i - 1] as usize };
            &list_data[start..list_ends[i] as usize]
        };
        if let Some(&id) = list_table.find(h, |&id| slice(id as usize) == ls) {
            return LevelList(id | LOCAL);
        }
        let id = list_ends.len() as u32;
        list_data.extend_from_slice(ls);
        list_ends.push(list_data.len() as u32);
        let (list_data, list_ends) = (&*list_data, &*list_ends);
        list_table.insert_unique(h, id, |&id| {
            let i = id as usize;
            let start = if i == 0 { 0 } else { list_ends[i - 1] as usize };
            list_hash(&list_data[start..list_ends[i] as usize])
        });
        let hp = ls.iter().any(|&l| self.level_has_param(l));
        self.list_hp.push(hp);
        LevelList(local_id(id))
    }

    // ---- expressions ----

    #[inline]
    pub fn node(&self, e: ExprId) -> ExprNode {
        if is_local(e.0) {
            *self.exprs.get(e.0 & !LOCAL)
        } else {
            self.env.exprs.get(e)
        }
    }

    #[inline]
    pub fn data(&self, e: ExprId) -> ExprData {
        if is_local(e.0) {
            self.edata[(e.0 & !LOCAL) as usize]
        } else {
            self.env.exprs.data(e)
        }
    }

    #[inline]
    pub fn has_loose_bvars(&self, e: ExprId) -> bool {
        self.data(e).has_loose_bvars()
    }

    #[inline]
    pub fn has_fvar(&self, e: ExprId) -> bool {
        self.data(e).has_fvar()
    }

    pub fn let_binder(&self, l: LetId) -> LetBinder {
        if is_local(l.0) {
            *self.lets.get(l.0 & !LOCAL)
        } else {
            self.env.exprs.let_binder(l)
        }
    }

    pub fn big(&self, b: BigId) -> &BigUint {
        if is_local(b.0) {
            &self.bigs[(b.0 & !LOCAL) as usize]
        } else {
            self.env.exprs.big(b)
        }
    }

    fn all_global(node: &ExprNode) -> bool {
        let g = |x: u32| !is_local(x);
        match *node {
            ExprNode::BVar(_) | ExprNode::NatSmall(..) | ExprNode::Str(_) => true,
            ExprNode::Sort(l) => g(l.0),
            ExprNode::Const(n, ls) => g(n.0) && g(ls.0),
            ExprNode::App(f, a) => g(f.0) && g(a.0),
            ExprNode::Lam(_, n, t, b) | ExprNode::Pi(_, n, t, b) => g(n.0) && g(t.0) && g(b.0),
            ExprNode::Let(h, b) => g(h.0) && g(b.0),
            ExprNode::NatBig(b) => g(b.0),
            ExprNode::Proj(n, _, e) => g(n.0) && g(e.0),
            ExprNode::FVar(_) => false,
        }
    }

    /// The id of `node`, adding it to the overlay if it is new.
    #[inline]
    pub fn mk(&mut self, node: ExprNode) -> ExprId {
        if Self::all_global(&node)
            && let Some(e) = self.env.exprs.find(&node)
        {
            return e;
        }
        self.mk_local(node)
    }

    fn mk_local(&mut self, node: ExprNode) -> ExprId {
        let (i, fresh) = self.exprs.intern(node).expect("expressions");
        if fresh {
            let d = match node {
                ExprNode::BVar(i) => ExprData::new((i + 1).min(ExprData::MAX_RANGE), false),
                ExprNode::Sort(l) => ExprData::new(0, self.level_has_param(l)),
                ExprNode::Const(_, ls) => ExprData::new(0, self.list_has_param(ls)),
                ExprNode::App(f, a) => self.data(f).union(self.data(a)),
                ExprNode::Lam(_, _, t, b) | ExprNode::Pi(_, _, t, b) => {
                    self.data(t).union(self.data(b).under_binder())
                }
                ExprNode::Let(h, b) => {
                    let h = self.let_binder(h);
                    self.data(h.ty)
                        .union(self.data(h.value))
                        .union(self.data(b).under_binder())
                }
                ExprNode::NatSmall(..) | ExprNode::NatBig(_) | ExprNode::Str(_) => {
                    ExprData::new(0, false)
                }
                ExprNode::Proj(_, _, e) => self.data(e),
                ExprNode::FVar(_) => ExprData::FVAR,
            };
            self.edata.push(d);
        }
        ExprId(local_id(i))
    }

    pub fn bvar(&mut self, i: u32) -> ExprId {
        assert!(i < ExprData::MAX_RANGE, "{OVERFLOW_MSG}");
        self.mk(ExprNode::BVar(i))
    }

    pub fn sort(&mut self, l: LevelId) -> ExprId {
        self.mk(ExprNode::Sort(l))
    }

    pub fn cnst(&mut self, n: NameId, ls: LevelList) -> ExprId {
        self.mk(ExprNode::Const(n, ls))
    }

    pub fn app(&mut self, f: ExprId, a: ExprId) -> ExprId {
        self.mk(ExprNode::App(f, a))
    }

    pub fn apps(&mut self, mut f: ExprId, args: &[ExprId]) -> ExprId {
        for &a in args {
            f = self.app(f, a);
        }
        f
    }

    pub fn lam(&mut self, bi: BinderInfo, n: NameId, t: ExprId, b: ExprId) -> ExprId {
        self.mk(ExprNode::Lam(bi, n, t, b))
    }

    pub fn pi(&mut self, bi: BinderInfo, n: NameId, t: ExprId, b: ExprId) -> ExprId {
        self.mk(ExprNode::Pi(bi, n, t, b))
    }

    pub fn proj(&mut self, s: NameId, i: u32, e: ExprId) -> ExprId {
        self.mk(ExprNode::Proj(s, i, e))
    }

    pub fn fvar(&mut self, i: u32) -> ExprId {
        self.mk_local(ExprNode::FVar(i))
    }

    pub fn mk_let(&mut self, name: NameId, ty: ExprId, value: ExprId, body: ExprId) -> ExprId {
        let b = LetBinder {
            name,
            ty,
            value,
            nondep: false,
        };
        self.mk_let_binder(b, body)
    }

    fn mk_let_binder(&mut self, b: LetBinder, body: ExprId) -> ExprId {
        let LetBinder {
            name, ty, value, ..
        } = b;
        let h = if !is_local(name.0) && !is_local(ty.0) && !is_local(value.0) {
            self.env.exprs.find_let(&b)
        } else {
            None
        };
        let h = match h {
            Some(h) => h,
            None => LetId(local_id(self.lets.intern(b).expect("lets").0)),
        };
        self.mk(ExprNode::Let(h, body))
    }

    /// The literal `n`.
    pub fn nat(&mut self, n: BigUint) -> ExprId {
        if let Ok(v) = u64::try_from(&n) {
            return self.nat_u64(v);
        }
        if let Some(b) = self.env.exprs.find_big(&n) {
            return self.mk(ExprNode::NatBig(b));
        }
        let h = big_hash(&n);
        let Self {
            bigs, big_table, ..
        } = self;
        let id = if let Some(&id) = big_table.find(h, |&id| bigs[id as usize] == n) {
            id
        } else {
            let id = bigs.len() as u32;
            bigs.push(n);
            let bigs = &*bigs;
            big_table.insert_unique(h, id, |&id| big_hash(&bigs[id as usize]));
            id
        };
        self.mk_local(ExprNode::NatBig(BigId(local_id(id))))
    }

    pub fn nat_u64(&mut self, v: u64) -> ExprId {
        self.mk(ExprNode::NatSmall(v as u32, (v >> 32) as u32))
    }

    // ---- application spines ----

    /// The head of an application spine.
    #[inline]
    pub fn head(&self, mut e: ExprId) -> ExprId {
        while let ExprNode::App(f, _) = self.node(e) {
            e = f;
        }
        e
    }

    /// The head and arguments (in order) of an application spine.
    pub fn spine(&self, mut e: ExprId, args: &mut Vec<ExprId>) -> ExprId {
        args.clear();
        while let ExprNode::App(f, a) = self.node(e) {
            args.push(a);
            e = f;
        }
        args.reverse();
        e
    }

    pub fn nargs(&self, mut e: ExprId) -> usize {
        let mut n = 0;
        while let ExprNode::App(f, _) = self.node(e) {
            n += 1;
            e = f;
        }
        n
    }

    /// The constant at the head of `e`, if any.
    pub fn head_const(&self, e: ExprId) -> Option<(NameId, LevelList)> {
        match self.node(self.head(e)) {
            ExprNode::Const(n, ls) => Some((n, ls)),
            _ => None,
        }
    }

    // ---- declaration pools ----

    pub fn name_list(&self, l: NameList) -> &[NameId] {
        if is_local(l.start) {
            let s = (l.start & !LOCAL) as usize;
            &self.decl_names[s..s + l.len as usize]
        } else {
            self.env.name_list(l)
        }
    }

    pub fn rec_rules(&self, l: RuleList) -> &[RecRule] {
        if is_local(l.start) {
            let s = (l.start & !LOCAL) as usize;
            &self.decl_rules[s..s + l.len as usize]
        } else {
            self.env.rec_rules(l)
        }
    }

    pub fn push_names(&mut self, ns: &[NameId]) -> NameList {
        let start = local_id(self.decl_names.len() as u32);
        self.decl_names.extend_from_slice(ns);
        NameList {
            start,
            len: ns.len() as u32,
        }
    }

    pub fn push_rules(&mut self, rs: &[RecRule]) -> RuleList {
        let start = local_id(self.decl_rules.len() as u32);
        self.decl_rules.extend_from_slice(rs);
        RuleList {
            start,
            len: rs.len() as u32,
        }
    }

    pub fn lparams(&self, d: &Decl) -> &[NameId] {
        self.name_list(d.level_params)
    }
}

/// A fast hasher for maps keyed by ids.
#[derive(Default, Clone, Copy)]
pub struct IdHasher(u64);

impl std::hash::Hasher for IdHasher {
    #[inline]
    fn finish(&self) -> u64 {
        crate::hash::hash2(self.0, 0x9e37_79b9_7f4a_7c15)
    }
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = (self.0.rotate_left(8) ^ b as u64).wrapping_mul(0x100_0000_01b3);
        }
    }
    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.0 = (self.0.rotate_left(32) ^ i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
    }
    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.0 = (self.0.rotate_left(32) ^ i).wrapping_mul(0x9e37_79b9_7f4a_7c15);
    }
    #[inline]
    fn write_u8(&mut self, i: u8) {
        self.write_u32(i as u32)
    }
    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.write_u64(i as u64)
    }
}

pub type IdBuild = std::hash::BuildHasherDefault<IdHasher>;
pub type IdMap<K, V> = hashbrown::HashMap<K, V, IdBuild>;
pub type IdSet<K> = hashbrown::HashSet<K, IdBuild>;

/// A value read lazily from an `.olean` file is built in the store, like
/// the checker's own terms (see [`Env::value_into`]).
impl crate::env::TermSink for Store<'_> {
    fn name(&mut self, node: NameNode) -> NameId {
        self.mk_name(node)
    }

    fn level(&mut self, node: LevelNode) -> LevelId {
        self.mk_level(node)
    }

    fn list(&mut self, levels: &[LevelId]) -> LevelList {
        self.mk_list(levels)
    }

    fn expr(&mut self, node: ExprNode) -> ExprId {
        self.mk(node)
    }

    fn let_in(&mut self, binder: LetBinder, body: ExprId) -> ExprId {
        self.mk_let_binder(binder, body)
    }

    fn nat_big(&mut self, n: BigUint) -> ExprId {
        self.nat(n)
    }
}
