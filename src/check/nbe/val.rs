//! Values: weak-head forms with closures, hash-consed in a worker's arena.
//!
//! A value is either a head form (a sort, a literal, a closure for a lambda
//! or a Π, or a neutral: a free variable or a constant applied to a spine
//! of arguments and projections) or a thunk, a term with the environment
//! and universe substitution it is to be evaluated in. Environments are
//! linked lists of values, spines are snoc lists; both are hash-consed too,
//! so the same computation reached twice is the same id, and every memo
//! keyed by a value id (forced thunk, `whnf`, type) is shared by all its
//! routes.

use hashbrown::HashTable;

use crate::env::NameList;
use crate::expr::ExprId;
use crate::hash::hash2;
use crate::level::{LevelId, LevelList};
use crate::name::NameId;
use crate::strings::StrId;

/// A value id.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct V(pub u32);

/// An environment: the values of the loose bound variables of a term,
/// innermost first. `Env::NIL` is empty.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Env(pub u32);

/// A spine of eliminations. `Sp::NIL` is empty.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Sp(pub u32);

/// A universe substitution: the universe parameters of a constant and the
/// levels it is used at. `Ls::ID` substitutes nothing.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Ls(pub u32);

impl Env {
    pub const NIL: Env = Env(0);
}

impl Sp {
    pub const NIL: Sp = Sp(0);
}

impl Ls {
    pub const ID: Ls = Ls(0);
}

pub const NONE: u32 = u32::MAX;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Val {
    Sort(LevelId),
    Nat(u32, u32),
    /// A literal of at least 2^64, an index into the arena's big literals.
    NatBig(u32),
    Str(StrId),
    /// A `Lam` term, in an environment.
    Lam(ExprId, Env, Ls),
    /// A `Pi` term, in an environment.
    Pi(ExprId, Env, Ls),
    /// The type of a `Lam` term in an environment: a Π whose codomain is
    /// the inferred type of the body.
    PiInfer(ExprId, Env, Ls),
    /// A term to be evaluated on demand.
    Thunk(ExprId, Env, Ls),
    Const(NameId, LevelList, Sp),
    FVar(u32, Sp),
}

/// A table hash from 32 stored bits, so that growing a table reads no
/// arena entries.
#[inline]
fn spread(h: u32) -> u64 {
    (h as u64 | (h as u64) << 32).wrapping_mul(0x9e37_79b9_7f4a_7c15)
}

#[inline]
fn h32(h: u64) -> u32 {
    (h >> 32) as u32 ^ h as u32
}

impl Val {
    #[inline]
    fn hash(&self) -> u32 {
        let (tag, a, b, c): (u64, u32, u32, u32) = match *self {
            Val::Sort(l) => (0, l.0, 0, 0),
            Val::Nat(lo, hi) => (1, lo, hi, 0),
            Val::NatBig(i) => (2, i, 0, 0),
            Val::Str(s) => (3, s.index() as u32, 0, 0),
            Val::Lam(e, env, ls) => (4, e.0, env.0, ls.0),
            Val::Pi(e, env, ls) => (5, e.0, env.0, ls.0),
            Val::PiInfer(e, env, ls) => (6, e.0, env.0, ls.0),
            Val::Thunk(e, env, ls) => (7, e.0, env.0, ls.0),
            Val::Const(n, l, sp) => (8, n.0, l.0, sp.0),
            Val::FVar(k, sp) => (9, k, sp.0, 0),
        };
        h32(hash2(tag | (a as u64) << 32, (b as u64) << 32 | c as u64))
    }
}

/// One elimination of a spine.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Elim {
    Arg(V),
    /// `Proj(structure, field index)`.
    Proj(NameId, u32),
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct SpNode {
    prev: Sp,
    a: u32,
    /// `NONE` for an argument, else the field index of a projection.
    b: u32,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct EnvNode {
    prev: Env,
    v: V,
}

/// A spine cell with its length and flags (`HAS_FVAR_BIT`, `HAS_PROJ_BIT`).
#[derive(Clone, Copy)]
struct SpRec {
    node: SpNode,
    len: u32,
}

/// An environment cell with its length and `HAS_FVAR_BIT`.
#[derive(Clone, Copy)]
struct EnvRec {
    node: EnvNode,
    len: u32,
}

const HAS_FVAR_BIT: u32 = 1 << 31;
const HAS_PROJ_BIT: u32 = 1 << 30;
const LEN_BITS: u32 = HAS_PROJ_BIT - 1;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct LsNode {
    pub params: NameList,
    pub levels: LevelList,
}

/// A value with what is known about it.
#[derive(Clone, Copy)]
pub struct Rec {
    pub val: Val,
    flags: u8,
    /// What a thunk evaluates to, or `NONE`; likewise the memos below.
    pub forced: u32,
    pub whnf_core: u32,
    pub whnf: u32,
    pub ty: u32,
    /// What a delta-reducible neutral unfolds to.
    pub delta: u32,
}

const HAS_FVAR: u8 = 1;
const CHECKED: u8 = 2;

/// The most values, spines or environments one declaration may build.
/// Past it the evaluating checker gives up on the declaration (by
/// unwinding with [`OutOfRoom`]) and the substituting one checks it.
const LIMIT: u32 = 1 << 23;

/// The payload of the unwind when an arena is full.
pub struct OutOfRoom;

#[cold]
#[inline(never)]
fn out_of_room() -> ! {
    std::panic::resume_unwind(Box::new(OutOfRoom))
}

/// The arena of one worker.
pub struct Arena {
    vals: Vec<Rec>,
    vtable: HashTable<(u32, u32)>,

    sps: Vec<SpRec>,
    sptable: HashTable<(u32, u32)>,
    envs: Vec<EnvRec>,
    envtable: HashTable<(u32, u32)>,
    lss: Vec<LsNode>,
    lstable: HashTable<(u32, u32)>,
    /// Recently made constants and sorts with no arguments, by a hash of
    /// their name and levels (direct-mapped, in front of `vtable`): the
    /// value of a constant is made at every occurrence.
    heads: Vec<(u32, u32, V)>,
}

/// Slots of `Arena::heads`.
const HEADS: usize = 1 << 12;

impl Default for Arena {
    fn default() -> Self {
        Self::new()
    }
}

impl Arena {
    pub fn new() -> Self {
        Arena {
            vals: Vec::new(),
            vtable: HashTable::new(),
            sps: vec![SpRec {
                node: SpNode {
                    prev: Sp::NIL,
                    a: 0,
                    b: 0,
                },
                len: 0,
            }],
            sptable: HashTable::new(),
            envs: vec![EnvRec {
                node: EnvNode {
                    prev: Env::NIL,
                    v: V(NONE),
                },
                len: 0,
            }],
            envtable: HashTable::new(),
            lss: vec![LsNode {
                params: NameList::default(),
                levels: LevelList::EMPTY,
            }],
            lstable: HashTable::new(),
            heads: vec![(NONE, NONE, V(NONE)); HEADS],
        }
    }

    pub fn len(&self) -> usize {
        self.vals.len()
    }

    /// Empty the arena, keeping its storage: refilling it then costs no
    /// growth. A large one is dropped instead.
    pub fn clear(&mut self) {
        if self.vtable.capacity() > 1 << 17
            || self.sptable.capacity() > 1 << 17
            || self.envtable.capacity() > 1 << 17
        {
            *self = Arena::new();
            return;
        }
        self.vals.clear();
        self.vtable.clear();
        self.sps.truncate(1);
        self.sptable.clear();
        self.envs.truncate(1);
        self.envtable.clear();
        self.lss.truncate(1);
        self.lstable.clear();
        self.heads.fill((NONE, NONE, V(NONE)));
    }

    pub fn is_empty(&self) -> bool {
        self.vals.is_empty()
    }

    /// Bytes held, roughly.
    pub fn heap_bytes(&self) -> usize {
        self.vals.capacity() * size_of::<Rec>()
            + self.vtable.capacity() * 9
            + self.sps.capacity() * 17
            + self.sptable.capacity() * 9
            + self.envs.capacity() * 13
            + self.envtable.capacity() * 9
    }

    // ---- values ----

    #[inline]
    pub fn get(&self, v: V) -> Val {
        self.vals[v.0 as usize].val
    }

    /// What is known about `v`.
    #[inline]
    pub fn r(&self, v: V) -> &Rec {
        &self.vals[v.0 as usize]
    }

    #[inline]
    pub fn rm(&mut self, v: V) -> &mut Rec {
        &mut self.vals[v.0 as usize]
    }

    #[inline]
    pub fn has_fvar(&self, v: V) -> bool {
        self.vals[v.0 as usize].flags & HAS_FVAR != 0
    }

    #[inline]
    pub fn checked(&self, v: V) -> bool {
        self.vals[v.0 as usize].flags & CHECKED != 0
    }

    #[inline]
    pub fn set_checked(&mut self, v: V) {
        self.vals[v.0 as usize].flags |= CHECKED;
    }

    #[inline]
    pub fn clear_checked(&mut self, v: V) {
        self.vals[v.0 as usize].flags &= !CHECKED;
    }

    /// `mk(Val::Const(n, l, Sp::NIL))`.
    #[inline]
    pub fn cnst(&mut self, n: NameId, l: LevelList) -> V {
        self.head(n.0, l.0, Val::Const(n, l, Sp::NIL))
    }

    /// `mk(Val::Sort(l))`.
    #[inline]
    pub fn sort(&mut self, l: LevelId) -> V {
        self.head(NONE - 1, l.0, Val::Sort(l))
    }

    #[inline]
    fn head(&mut self, a: u32, b: u32, val: Val) -> V {
        let i = (hash2(a as u64, b as u64) >> 52) as usize & (HEADS - 1);
        let (x, y, v) = self.heads[i];
        if x == a && y == b {
            return v;
        }
        let v = self.mk(val);
        self.heads[i] = (a, b, v);
        v
    }

    pub fn mk(&mut self, val: Val) -> V {
        let h = val.hash();
        let Self { vals, vtable, .. } = self;
        if let Some(&(id, _)) =
            vtable.find(spread(h), |&(id, k)| k == h && vals[id as usize].val == val)
        {
            return V(id);
        }
        let id = vals.len() as u32;
        if id >= LIMIT {
            out_of_room();
        }
        vals.push(Rec {
            val,
            flags: 0,
            forced: NONE,
            whnf_core: NONE,
            whnf: NONE,
            ty: NONE,
            delta: NONE,
        });
        vtable.insert_unique(spread(h), (id, h), |&(_, k)| spread(k));
        let fv = match val {
            Val::Sort(_) | Val::Nat(..) | Val::NatBig(_) | Val::Str(_) => false,
            Val::Lam(_, e, _) | Val::Pi(_, e, _) | Val::PiInfer(_, e, _) | Val::Thunk(_, e, _) => {
                self.envs[e.0 as usize].len & HAS_FVAR_BIT != 0
            }
            Val::Const(_, _, sp) => self.sps[sp.0 as usize].len & HAS_FVAR_BIT != 0,
            Val::FVar(..) => true,
        };
        if fv {
            self.vals[id as usize].flags = HAS_FVAR;
        }

        V(id)
    }

    // ---- spines ----

    #[inline]
    pub fn sp_len(&self, sp: Sp) -> u32 {
        self.sps[sp.0 as usize].len & LEN_BITS
    }

    /// Whether `sp` has a projection.
    #[inline]
    pub fn sp_has_proj(&self, sp: Sp) -> bool {
        self.sps[sp.0 as usize].len & HAS_PROJ_BIT != 0
    }

    /// The first `n` eliminations of `sp`.
    pub fn sp_prefix(&self, mut sp: Sp, n: u32) -> Sp {
        let len = self.sp_len(sp);
        for _ in n..len {
            sp = self.sps[sp.0 as usize].node.prev;
        }
        sp
    }

    /// The last elimination of a non-empty spine, and the rest.
    #[inline]
    pub fn sp_last(&self, sp: Sp) -> (Sp, Elim) {
        let n = self.sps[sp.0 as usize].node;
        let e = if n.b == NONE {
            Elim::Arg(V(n.a))
        } else {
            Elim::Proj(NameId(n.a), n.b)
        };
        (n.prev, e)
    }

    pub fn snoc(&mut self, sp: Sp, e: Elim) -> Sp {
        let (a, b) = match e {
            Elim::Arg(v) => (v.0, NONE),
            Elim::Proj(n, i) => (n.0, i),
        };
        let node = SpNode { prev: sp, a, b };
        let h = h32(hash2(sp.0 as u64 | 1 << 40, (a as u64) << 32 | b as u64));
        let Self { sps, sptable, .. } = self;
        if let Some(&(id, _)) = sptable.find(spread(h), |&(id, k)| {
            k == h && sps[id as usize].node == node
        }) {
            return Sp(id);
        }
        let id = sps.len() as u32;
        if id >= LIMIT {
            out_of_room();
        }
        let prev = self.sps[sp.0 as usize].len;
        let fv = prev & HAS_FVAR_BIT != 0
            || match e {
                Elim::Arg(v) => self.has_fvar(v),
                Elim::Proj(..) => false,
            };
        let pj = prev & HAS_PROJ_BIT != 0 || matches!(e, Elim::Proj(..));
        let len = ((prev & LEN_BITS) + 1)
            | if fv { HAS_FVAR_BIT } else { 0 }
            | if pj { HAS_PROJ_BIT } else { 0 };
        self.sps.push(SpRec { node, len });
        self.sptable
            .insert_unique(spread(h), (id, h), |&(_, k)| spread(k));
        Sp(id)
    }

    /// The eliminations of `sp`, in order.
    pub fn elims(&self, mut sp: Sp, out: &mut Vec<Elim>) {
        out.clear();
        while sp != Sp::NIL {
            let (p, e) = self.sp_last(sp);
            out.push(e);
            sp = p;
        }
        out.reverse();
    }

    /// The arguments of `sp`, if it has no projections.
    pub fn args(&self, mut sp: Sp, out: &mut Vec<V>) -> bool {
        out.clear();
        while sp != Sp::NIL {
            match self.sp_last(sp) {
                (p, Elim::Arg(v)) => {
                    out.push(v);
                    sp = p;
                }
                (_, Elim::Proj(..)) => return false,
            }
        }
        out.reverse();
        true
    }

    // ---- environments ----

    #[inline]
    pub fn env_len(&self, e: Env) -> u32 {
        self.envs[e.0 as usize].len & LEN_BITS
    }

    pub fn cons(&mut self, env: Env, v: V) -> Env {
        let node = EnvNode { prev: env, v };
        let h = h32(hash2(env.0 as u64 | 2 << 40, v.0 as u64));
        let Self { envs, envtable, .. } = self;
        if let Some(&(id, _)) = envtable.find(spread(h), |&(id, k)| {
            k == h && envs[id as usize].node == node
        }) {
            return Env(id);
        }
        let id = envs.len() as u32;
        if id >= LIMIT {
            out_of_room();
        }
        let prev = self.envs[env.0 as usize].len;
        let fv = prev & HAS_FVAR_BIT != 0 || self.has_fvar(v);
        let len = ((prev & LEN_BITS) + 1) | if fv { HAS_FVAR_BIT } else { 0 };
        self.envs.push(EnvRec { node, len });
        self.envtable
            .insert_unique(spread(h), (id, h), |&(_, k)| spread(k));
        Env(id)
    }

    #[inline]
    pub fn env_head(&self, e: Env) -> V {
        self.envs[e.0 as usize].node.v
    }

    #[inline]
    pub fn env_tail(&self, e: Env) -> Env {
        self.envs[e.0 as usize].node.prev
    }

    /// The value of bound variable `i` (0 is the innermost).
    #[inline]
    pub fn lookup(&self, mut env: Env, i: u32) -> Option<V> {
        for _ in 0..i {
            if env == Env::NIL {
                return None;
            }
            env = self.envs[env.0 as usize].node.prev;
        }
        if env == Env::NIL {
            None
        } else {
            Some(self.envs[env.0 as usize].node.v)
        }
    }

    /// The first `n` entries of `env`, innermost first.
    pub fn env_values(&self, mut env: Env, out: &mut Vec<V>) {
        out.clear();
        while env != Env::NIL {
            let n = self.envs[env.0 as usize].node;
            out.push(n.v);
            env = n.prev;
        }
    }

    // ---- universe substitutions ----

    pub fn ls(&self, l: Ls) -> LsNode {
        self.lss[l.0 as usize]
    }

    pub fn mk_ls(&mut self, params: NameList, levels: LevelList) -> Ls {
        if params.is_empty() {
            return Ls::ID;
        }
        let node = LsNode { params, levels };
        let h = h32(hash2(
            (params.start as u64) << 32 | params.len as u64,
            levels.0 as u64,
        ));
        let Self { lss, lstable, .. } = self;
        if let Some(&(id, _)) =
            lstable.find(spread(h), |&(id, k)| k == h && lss[id as usize] == node)
        {
            return Ls(id);
        }
        let id = lss.len() as u32;
        lss.push(node);
        lstable.insert_unique(spread(h), (id, h), |&(_, k)| spread(k));
        Ls(id)
    }
}
