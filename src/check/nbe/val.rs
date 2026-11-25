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
use hashbrown::hash_table::Entry;

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
struct EnvNode {
    prev: Env,
    v: V,
}

/// An environment cell with its length and `HAS_FVAR_BIT`, and a jump
/// to an outer cell: the skew-binary jump pointers of Myers, "An
/// applicative random-access stack" (1983), which find the variable at
/// depth `i` in O(log i) steps.
#[derive(Clone, Copy)]
struct EnvRec {
    node: EnvNode,
    len: u32,
    jump: Env,
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

/// The most words the spines of one declaration may take.
const SP_WORDS: usize = 8 << 23;

/// The payload of the unwind when an arena is full.
pub struct OutOfRoom;

#[cold]
#[inline(never)]
fn out_of_room() -> ! {
    std::panic::resume_unwind(Box::new(OutOfRoom))
}

/// The arena of one worker.
pub struct Arena {
    /// The values; what is known about them is in `recs`, apart, so that
    /// probing `vtable` reads only values.
    vals: Vec<Val>,
    recs: Vec<Rec>,
    vtable: HashTable<(u32, u32)>,

    /// Spines, each a header (its length and `HAS_FVAR_BIT`,
    /// `HAS_PROJ_BIT`) and then two words per elimination (an argument's
    /// id and `NONE`, or a projection's structure and field). A spine is
    /// the offset of its header; `Sp::NIL` is the empty one at 0.
    sps: Vec<u32>,
    /// Spines by content.
    sptable: HashTable<(u32, u32)>,
    /// Scratch words for building a spine.
    sp_buf: Vec<u32>,
    envs: Vec<EnvRec>,
    envtable: HashTable<(u32, u32)>,
    lss: Vec<LsNode>,
    lstable: HashTable<(u32, u32)>,
    /// Recently made constants and sorts with no arguments, by a hash of
    /// their name and levels (direct-mapped, in front of `vtable`): the
    /// value of a constant is made at every occurrence.
    heads: Vec<(u32, u32, V)>,
    /// The thunks of terms by their environment before it is trimmed
    /// (direct-mapped, in front of trimming and `vtable`): (term,
    /// environment, substitution, thunk).
    thunks: Vec<[u32; 4]>,
    /// Neutrals by head and spine contents, so that applying a neutral to
    /// arguments finds the result with one probe.
    nutable: HashTable<(u32, u32)>,
    /// Environments by their last entry and the rest (direct-mapped, in
    /// front of `envtable`): (rest, entry, environment).
    conses: Vec<[u32; 3]>,
}

/// Slots of `Arena::heads`.
const HEADS: usize = 1 << 12;

/// Slots of `Arena::conses`.
const CONSES: usize = 1 << 14;

/// Slots of `Arena::thunks`.
const THUNKS: usize = 1 << 14;

impl Default for Arena {
    fn default() -> Self {
        Self::new()
    }
}

impl Arena {
    pub fn new() -> Self {
        Arena {
            vals: Vec::new(),
            recs: Vec::new(),
            vtable: HashTable::new(),
            sps: vec![0],
            sptable: HashTable::new(),
            sp_buf: Vec::new(),
            envs: vec![EnvRec {
                node: EnvNode {
                    prev: Env::NIL,
                    v: V(NONE),
                },
                len: 0,
                jump: Env::NIL,
            }],
            envtable: HashTable::new(),
            lss: vec![LsNode {
                params: NameList::default(),
                levels: LevelList::EMPTY,
            }],
            lstable: HashTable::new(),
            heads: vec![(NONE, NONE, V(NONE)); HEADS],
            thunks: vec![[NONE; 4]; THUNKS],
            nutable: HashTable::new(),
            conses: vec![[NONE; 3]; CONSES],
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
            || self.nutable.capacity() > 1 << 17
        {
            *self = Arena::new();
            return;
        }
        self.vals.clear();
        self.recs.clear();
        self.vtable.clear();
        self.sps.truncate(1);
        self.sp_buf.clear();
        self.sptable.clear();
        self.envs.truncate(1);
        self.envtable.clear();
        self.lss.truncate(1);
        self.lstable.clear();
        self.heads.fill((NONE, NONE, V(NONE)));
        self.thunks.fill([NONE; 4]);
        self.nutable.clear();
        self.conses.fill([NONE; 3]);
    }

    pub fn is_empty(&self) -> bool {
        self.vals.is_empty()
    }

    /// Bytes held, roughly.
    pub fn heap_bytes(&self) -> usize {
        self.vals.capacity() * size_of::<Val>()
            + self.recs.capacity() * size_of::<Rec>()
            + self.vtable.capacity() * 9
            + self.sps.capacity() * 4
            + self.sptable.capacity() * 9
            + self.envs.capacity() * 17
            + self.thunks.capacity() * 16
            + self.nutable.capacity() * 9
            + self.conses.capacity() * 12
            + self.envtable.capacity() * 9
    }

    // ---- values ----

    #[inline]
    pub fn get(&self, v: V) -> Val {
        self.vals[v.0 as usize]
    }

    /// What is known about `v`.
    #[inline]
    pub fn r(&self, v: V) -> &Rec {
        &self.recs[v.0 as usize]
    }

    #[inline]
    pub fn rm(&mut self, v: V) -> &mut Rec {
        &mut self.recs[v.0 as usize]
    }

    #[inline]
    pub fn has_fvar(&self, v: V) -> bool {
        self.recs[v.0 as usize].flags & HAS_FVAR != 0
    }

    #[inline]
    pub fn checked(&self, v: V) -> bool {
        self.recs[v.0 as usize].flags & CHECKED != 0
    }

    #[inline]
    pub fn set_checked(&mut self, v: V) {
        self.recs[v.0 as usize].flags |= CHECKED;
    }

    #[inline]
    pub fn clear_checked(&mut self, v: V) {
        self.recs[v.0 as usize].flags &= !CHECKED;
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

    /// The slot of `Arena::thunks` for `e` in `env` under `ls`, and the
    /// thunk it holds for them, if it does.
    #[inline]
    pub fn thunk_slot(&self, e: ExprId, env: Env, ls: Ls) -> (usize, Option<V>) {
        let h = hash2(e.0 as u64 | (ls.0 as u64) << 32, env.0 as u64);
        let i = (h >> 50) as usize & (THUNKS - 1);
        let s = self.thunks[i];
        let hit = s[0] == e.0 && s[1] == env.0 && s[2] == ls.0;
        (i, hit.then_some(V(s[3])))
    }

    #[inline]
    pub fn set_thunk_slot(&mut self, i: usize, e: ExprId, env: Env, ls: Ls, v: V) {
        self.thunks[i] = [e.0, env.0, ls.0, v.0];
    }

    pub fn mk(&mut self, val: Val) -> V {
        if let Val::Const(_, _, sp) | Val::FVar(_, sp) = val
            && sp != Sp::NIL
        {
            let k = sp.0 as usize + 1;
            let n = self.sp_len(sp) as usize;
            return self.neutral_in(val, k, n, &[], Some(sp));
        }
        let h = val.hash();
        let Self { vals, vtable, .. } = self;
        let slot = match vtable.entry(
            spread(h),
            |&(id, k)| k == h && vals[id as usize] == val,
            |&(_, k)| spread(k),
        ) {
            Entry::Occupied(o) => return V(o.get().0),
            Entry::Vacant(slot) => slot,
        };
        let id = vals.len() as u32;
        if id >= LIMIT {
            out_of_room();
        }
        slot.insert((id, h));
        vals.push(val);
        self.recs.push(Rec {
            flags: 0,
            forced: NONE,
            whnf_core: NONE,
            whnf: NONE,
            ty: NONE,
            delta: NONE,
        });
        let fv = match val {
            Val::Sort(_) | Val::Nat(..) | Val::NatBig(_) | Val::Str(_) => false,
            Val::Lam(_, e, _) | Val::Pi(_, e, _) | Val::PiInfer(_, e, _) | Val::Thunk(_, e, _) => {
                self.envs[e.0 as usize].len & HAS_FVAR_BIT != 0
            }
            Val::Const(_, _, sp) => self.sps[sp.0 as usize] & HAS_FVAR_BIT != 0,
            Val::FVar(..) => true,
        };
        if fv {
            self.recs[id as usize].flags = HAS_FVAR;
        }

        V(id)
    }

    // ---- spines ----

    #[inline]
    pub fn sp_len(&self, sp: Sp) -> u32 {
        self.sps[sp.0 as usize] & LEN_BITS
    }

    /// Whether `sp` has a projection.
    #[inline]
    pub fn sp_has_proj(&self, sp: Sp) -> bool {
        self.sps[sp.0 as usize] & HAS_PROJ_BIT != 0
    }

    /// Elimination `i` of `sp`, from the first.
    #[inline]
    pub fn sp_elim(&self, sp: Sp, i: u32) -> Elim {
        let k = sp.0 as usize + 1 + 2 * i as usize;
        let (a, b) = (self.sps[k], self.sps[k + 1]);
        if b == NONE {
            Elim::Arg(V(a))
        } else {
            Elim::Proj(NameId(a), b)
        }
    }

    /// The last elimination of a non-empty spine.
    #[inline]
    pub fn sp_last_elim(&self, sp: Sp) -> Elim {
        self.sp_elim(sp, self.sp_len(sp) - 1)
    }

    /// The first `n` eliminations of `sp`.
    pub fn sp_prefix(&mut self, sp: Sp, n: u32) -> Sp {
        if n >= self.sp_len(sp) {
            return sp;
        }
        let mut buf = std::mem::take(&mut self.sp_buf);
        buf.clear();
        let k = sp.0 as usize + 1;
        buf.extend_from_slice(&self.sps[k..k + 2 * n as usize]);
        let r = self.intern_sp(&buf);
        self.sp_buf = buf;
        r
    }

    /// The last elimination of a non-empty spine, and the rest.
    #[inline]
    pub fn sp_last(&mut self, sp: Sp) -> (Sp, Elim) {
        let n = self.sp_len(sp);
        let e = self.sp_elim(sp, n - 1);
        (self.sp_prefix(sp, n - 1), e)
    }

    pub fn snoc(&mut self, sp: Sp, e: Elim) -> Sp {
        let (a, b) = match e {
            Elim::Arg(v) => (v.0, NONE),
            Elim::Proj(n, i) => (n.0, i),
        };
        let mut buf = self.sp_words(sp);
        buf.push(a);
        buf.push(b);
        let r = self.intern_sp(&buf);
        self.sp_buf = buf;
        r
    }

    /// The neutral `head` (a `Const` or `FVar`) with the arguments `xs`
    /// after its spine.
    pub fn neutral(&mut self, head: Val, xs: &[V]) -> V {
        let (Val::Const(_, _, base) | Val::FVar(_, base)) = head else {
            unreachable!()
        };
        if xs.is_empty() {
            return self.mk(head);
        }
        let k = base.0 as usize + 1;
        let n = self.sp_len(base) as usize;
        self.neutral_in(head, k, n, xs, None)
    }

    /// The neutral with `head`'s head and the spine of the `n` eliminations
    /// at `sps[k..]` followed by the arguments `xs`: found by its contents,
    /// else made, with `sp` as its spine if given (else a copy). Applied
    /// neutrals are made here only, so that one probe finds them.
    fn neutral_in(&mut self, head: Val, k: usize, n: usize, xs: &[V], sp: Option<Sp>) -> V {
        let (tag, a, b) = match head {
            Val::Const(n, l, _) => (0u64, n.0, l.0),
            Val::FVar(k, _) => (1u64, k, 0),
            _ => unreachable!(),
        };
        let mut h = hash2(tag | (a as u64) << 32, b as u64);
        for &w in &self.sps[k..k + 2 * n] {
            h = (h.rotate_left(5) ^ w as u64).wrapping_mul(0x517c_c1b7_2722_0a95);
        }
        for x in xs {
            h = (h.rotate_left(5) ^ x.0 as u64).wrapping_mul(0x517c_c1b7_2722_0a95);
            h = (h.rotate_left(5) ^ NONE as u64).wrapping_mul(0x517c_c1b7_2722_0a95);
        }
        let h = h32(h);
        let Self {
            vals,
            sps,
            nutable,
            recs,
            ..
        } = self;
        let slot = match nutable.entry(
            spread(h),
            |&(id, k2)| {
                k2 == h && {
                    let (same, sp) = match (vals[id as usize], head) {
                        (Val::Const(n2, l2, sp), Val::Const(n1, l1, _)) => {
                            (n1 == n2 && l1 == l2, sp)
                        }
                        (Val::FVar(k2, sp), Val::FVar(k1, _)) => (k1 == k2, sp),
                        _ => (false, Sp::NIL),
                    };
                    let i = sp.0 as usize;
                    same && (sps[i] & LEN_BITS) as usize == n + xs.len()
                        && sps[i + 1..i + 1 + 2 * n] == sps[k..k + 2 * n]
                        && xs
                            .iter()
                            .enumerate()
                            .all(|(j, x)| sps[i + 1 + 2 * (n + j)] == x.0)
                }
            },
            |&(_, k)| spread(k),
        ) {
            Entry::Occupied(o) => return V(o.get().0),
            Entry::Vacant(slot) => slot,
        };
        let sp = match sp {
            Some(sp) => sp,
            None => {
                let id = sps.len();
                if id + 1 + 2 * (n + xs.len()) >= SP_WORDS {
                    out_of_room();
                }
                let base = sps[k - 1] & (HAS_FVAR_BIT | HAS_PROJ_BIT);
                let fv = xs.iter().any(|&x| recs[x.0 as usize].flags & HAS_FVAR != 0);
                sps.push((n + xs.len()) as u32 | base | if fv { HAS_FVAR_BIT } else { 0 });
                sps.extend_from_within(k..k + 2 * n);
                for x in xs {
                    sps.push(x.0);
                    sps.push(NONE);
                }
                Sp(id as u32)
            }
        };
        let val = match head {
            Val::Const(n, l, _) => Val::Const(n, l, sp),
            Val::FVar(k, _) => Val::FVar(k, sp),
            _ => unreachable!(),
        };
        let id = vals.len() as u32;
        if id >= LIMIT {
            out_of_room();
        }
        slot.insert((id, h));
        vals.push(val);
        let fv = matches!(head, Val::FVar(..)) || sps[sp.0 as usize] & HAS_FVAR_BIT != 0;
        recs.push(Rec {
            flags: if fv { HAS_FVAR } else { 0 },
            forced: NONE,
            whnf_core: NONE,
            whnf: NONE,
            ty: NONE,
            delta: NONE,
        });
        V(id)
    }

    /// `sp` followed by the arguments `xs`.
    pub fn snoc_args(&mut self, sp: Sp, xs: &[V]) -> Sp {
        if xs.is_empty() {
            return sp;
        }
        let mut buf = self.sp_words(sp);
        for x in xs {
            buf.push(x.0);
            buf.push(NONE);
        }
        let r = self.intern_sp(&buf);
        self.sp_buf = buf;
        r
    }

    /// The scratch buffer, holding the words of `sp`'s eliminations.
    fn sp_words(&mut self, sp: Sp) -> Vec<u32> {
        let mut buf = std::mem::take(&mut self.sp_buf);
        buf.clear();
        let k = sp.0 as usize + 1;
        let n = self.sp_len(sp) as usize;
        buf.extend_from_slice(&self.sps[k..k + 2 * n]);
        buf
    }

    /// The spine of the elimination words `w`.
    fn intern_sp(&mut self, w: &[u32]) -> Sp {
        if w.is_empty() {
            return Sp::NIL;
        }
        let mut h: u64 = w.len() as u64;
        for &x in w {
            h = (h.rotate_left(5) ^ x as u64).wrapping_mul(0x517c_c1b7_2722_0a95);
        }
        let h = h32(h);
        let Self { sps, sptable, .. } = self;
        if let Some(&(id, _)) = sptable.find(spread(h), |&(id, k)| {
            k == h && {
                let i = id as usize;
                sps[i] & LEN_BITS == (w.len() / 2) as u32 && sps[i + 1..i + 1 + w.len()] == *w
            }
        }) {
            return Sp(id);
        }
        let id = sps.len() as u32;
        if sps.len() + w.len() >= SP_WORDS {
            out_of_room();
        }
        let mut fv = false;
        let mut pj = false;
        for p in w.as_chunks::<2>().0 {
            if p[1] == NONE {
                fv = fv || self.has_fvar(V(p[0]));
            } else {
                pj = true;
            }
        }
        let hdr = (w.len() / 2) as u32
            | if fv { HAS_FVAR_BIT } else { 0 }
            | if pj { HAS_PROJ_BIT } else { 0 };
        self.sps.push(hdr);
        self.sps.extend_from_slice(w);
        self.sptable
            .insert_unique(spread(h), (id, h), |&(_, k)| spread(k));
        Sp(id)
    }

    /// The eliminations of `sp`, in order.
    pub fn elims(&self, sp: Sp, out: &mut Vec<Elim>) {
        out.clear();
        for i in 0..self.sp_len(sp) {
            out.push(self.sp_elim(sp, i));
        }
    }

    /// The arguments of `sp`, if it has no projections.
    pub fn args(&self, sp: Sp, out: &mut Vec<V>) -> bool {
        out.clear();
        if self.sp_has_proj(sp) {
            return false;
        }
        let k = sp.0 as usize + 1;
        let n = self.sp_len(sp) as usize;
        out.extend(self.sps[k..k + 2 * n].iter().step_by(2).map(|&a| V(a)));
        true
    }

    // ---- environments ----

    #[inline]
    pub fn env_len(&self, e: Env) -> u32 {
        self.envs[e.0 as usize].len & LEN_BITS
    }

    #[inline]
    pub fn cons(&mut self, env: Env, v: V) -> Env {
        let h = hash2(env.0 as u64 | 2 << 40, v.0 as u64);
        let i = (h >> 50) as usize & (CONSES - 1);
        let s = self.conses[i];
        if s[0] == env.0 && s[1] == v.0 {
            return Env(s[2]);
        }
        let r = self.cons_find(env, v, h32(h));
        self.conses[i] = [env.0, v.0, r.0];
        r
    }

    /// `cons` not in its slot of `conses`.
    #[inline(never)]
    fn cons_find(&mut self, env: Env, v: V, h: u32) -> Env {
        let node = EnvNode { prev: env, v };
        let Self {
            envs,
            envtable,
            recs,
            ..
        } = self;
        let slot = match envtable.entry(
            spread(h),
            |&(id, k)| k == h && envs[id as usize].node == node,
            |&(_, k)| spread(k),
        ) {
            Entry::Occupied(o) => return Env(o.get().0),
            Entry::Vacant(slot) => slot,
        };
        let id = envs.len() as u32;
        if id >= LIMIT {
            out_of_room();
        }
        slot.insert((id, h));
        let p = envs[env.0 as usize];
        let fv = p.len & HAS_FVAR_BIT != 0 || recs[v.0 as usize].flags & HAS_FVAR != 0;
        let len = ((p.len & LEN_BITS) + 1) | if fv { HAS_FVAR_BIT } else { 0 };
        let j = envs[p.jump.0 as usize];
        let (lp, lj) = (p.len & LEN_BITS, j.len & LEN_BITS);
        let ljj = envs[j.jump.0 as usize].len & LEN_BITS;
        let jump = if lp - lj == lj - ljj { j.jump } else { env };
        envs.push(EnvRec { node, len, jump });
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
    pub fn lookup(&self, env: Env, i: u32) -> Option<V> {
        let mut r = self.envs[env.0 as usize];
        let len = r.len & LEN_BITS;
        if i >= len {
            return None;
        }
        if i < 8 {
            for _ in 0..i {
                r = self.envs[r.node.prev.0 as usize];
            }
            return Some(r.node.v);
        }
        let target = len - i;
        while r.len & LEN_BITS != target {
            let j = self.envs[r.jump.0 as usize];
            r = if j.len & LEN_BITS >= target {
                j
            } else {
                self.envs[r.node.prev.0 as usize]
            };
        }
        Some(r.node.v)
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
