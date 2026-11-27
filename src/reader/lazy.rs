//! Theorem values left unbuilt when reading an export.
//!
//! An export lists every term once, children first, and numbers its
//! expressions densely from 0; a theorem's proof comes right before its
//! declaration line. With lazy proofs on, the reader keeps one record of
//! 8 bytes per expression id, in a table indexed by that id ([`Builder`]).
//! Leaves (`bvar`, `sort`, `const`, literals) are interned at once, and
//! their record holds their arena id. A compound record holds its
//! children's export ids (an application's in the record itself, others'
//! in a side table), so a line costs one push. At a declaration line, the
//! terms its eager fields need (types, definition values, recursor rules)
//! are interned from the table ("promoted"), and their records then hold
//! their arena ids too. What is left (a theorem's proof, mostly) stays in
//! the table and is never hash-consed. A theorem's value that is not in
//! the arena is a placeholder ([`crate::env::LAZY_BASE`]) built on demand
//! by [`crate::env::Env::value_into`].
//!
//! An export whose expression ids are not dense (or that has too many for
//! the table) cannot use it: the reader then interns every record it holds
//! and goes on without lazy proofs ([`Builder::into_eager`]).

use std::cell::RefCell;

use hashbrown::HashMap;

use super::{Fail, R};
use crate::env::{Env, LAZY_BASE, LazyValues, TermSink};
use crate::expr::{BinderInfo, ExprId, ExprNode, LetBinder};
use crate::idmap::IdMap;
use crate::name::NameId;
use crate::slab::{Bits, Slab, Zeroed};
use crate::strings::Overflow;

// A record: `DONE` and an arena id in the low 32 bits, or a tag (3 bits
// at `TAG`) and its fields. An application's are its function's export id
// (at `ID_BITS`) and its argument's (at 0); a binder's, let's and
// projection's are a side table offset (low 32 bits) and their flags
// above it; an alias's (`mdata`) is the export id it stands for, which is
// not an alias itself.
const DONE: u64 = 1 << 63;
/// Set while [`Builder::promote`] has found a record needed and not yet
/// interned it.
const NEEDED: u64 = 1 << 62;
const TAG: u32 = 59;
const T_APP: u64 = 0;
const T_LAM: u64 = 1;
const T_PI: u64 = 2;
const T_LET: u64 = 3;
const T_PROJ: u64 = 4;
const T_ALIAS: u64 = 5;
/// A stored application whose children do not fit [`ID_BITS`]: they are
/// its side record (see [`Stored`]).
const T_APPS: u64 = 6;
const ID_BITS: u32 = 29;
const ID_MASK: u64 = (1 << ID_BITS) - 1;
/// The most expression ids the table takes.
const MAX_IDS: u64 = 1 << ID_BITS;

#[inline(always)]
fn tag(r: u64) -> u64 {
    r >> TAG & 7
}

fn bi_bits(bi: BinderInfo) -> u64 {
    match bi {
        BinderInfo::Default => 0,
        BinderInfo::Implicit => 1,
        BinderInfo::StrictImplicit => 2,
        BinderInfo::InstImplicit => 3,
    }
}

fn bits_bi(b: u64) -> BinderInfo {
    match b & 3 {
        0 => BinderInfo::Default,
        1 => BinderInfo::Implicit,
        2 => BinderInfo::StrictImplicit,
        _ => BinderInfo::InstImplicit,
    }
}

/// A compound record, decoded: children as export ids.
#[derive(Clone, Copy)]
enum Node {
    App(u32, u32),
    Bind {
        pi: bool,
        bi: BinderInfo,
        name: NameId,
        ty: u32,
        body: u32,
    },
    Let {
        name: NameId,
        ty: u32,
        value: u32,
        body: u32,
        nondep: bool,
    },
    Proj(NameId, u32, u32),
}

impl Node {
    #[inline(always)]
    fn kids(&self) -> ([u32; 3], usize) {
        match *self {
            Node::App(f, a) => ([f, a, 0], 2),
            Node::Bind { ty, body, .. } => ([ty, body, 0], 2),
            Node::Let {
                ty, value, body, ..
            } => ([ty, value, body], 3),
            Node::Proj(_, _, e) => ([e, 0, 0], 1),
        }
    }
}

/// Record `r` (compound, not done, not an alias), decoded.
#[inline(always)]
fn decode(side: &[u32], r: u64) -> Node {
    let t = tag(r);
    if t == T_APP {
        return Node::App((r >> ID_BITS & ID_MASK) as u32, (r & ID_MASK) as u32);
    }
    let o = r as u32 as usize;
    let flags = r >> 32;
    match t {
        T_LAM | T_PI => Node::Bind {
            pi: t == T_PI,
            bi: bits_bi(flags),
            name: NameId(side[o]),
            ty: side[o + 1],
            body: side[o + 2],
        },
        T_LET => Node::Let {
            name: NameId(side[o]),
            ty: side[o + 1],
            value: side[o + 2],
            body: side[o + 3],
            nondep: flags & 1 != 0,
        },
        _ => Node::Proj(NameId(side[o]), side[o + 1], side[o + 2]),
    }
}

/// A binder record's side record: name, type and body.
#[inline(always)]
fn binder_side(side: &[u32], r: u64) -> [u32; 3] {
    let o = r as u32 as usize;
    *side[o..].first_chunk().expect("a binder's side record")
}

/// Intern record `n` in `env`, its children's arena ids being `ids` (in
/// the order of [`Node::kids`]); its arena id.
#[inline]
fn add(env: &mut Env, append: bool, n: Node, ids: [u32; 3]) -> R<u32> {
    let e = |i: usize| ExprId(ids[i]);
    let node = match n {
        Node::App(..) => ExprNode::App(e(0), e(1)),
        Node::Bind { pi, bi, name, .. } => {
            if pi {
                ExprNode::Pi(bi, name, e(0), e(1))
            } else {
                ExprNode::Lam(bi, name, e(0), e(1))
            }
        }
        Node::Let { name, nondep, .. } => {
            let b = LetBinder {
                name,
                ty: e(0),
                value: e(1),
                nondep,
            };
            ExprNode::Let(env.exprs.intern_let(b)?, e(2))
        }
        Node::Proj(s, i, _) => ExprNode::Proj(s, i, e(0)),
    };
    add_node(env, append, node)
}

/// Add compound `node` to `env` (without hash-consing it if `append`);
/// its arena id.
#[inline(always)]
fn add_node(env: &mut Env, append: bool, node: ExprNode) -> R<u32> {
    // (Arena ids are below `slab::CAP`, so a done record's low half holds
    // one.)
    let id = if append {
        env.exprs.append_compound(node)?
    } else {
        env.exprs.intern(node, &env.levels)?.0
    };
    Ok(id.0)
}

/// The reader's side of lazy proofs: a record per expression id.
#[derive(Default)]
pub(super) struct Builder {
    /// In memory that never moves, so that views of it can be read on other
    /// threads while it grows (see [`Builder::view`]): a record is only
    /// set again through [`Slab::store_shared`].
    recs: Slab<u64>,
    side: Slab<u32>,
    /// Records from here on came after the last declaration line.
    from: usize,
    /// Per lazy value, its root's export id, and the first record of its
    /// declaration's lines (or the root, if that is older).
    roots: Vec<u32>,
    starts: Vec<u32>,
    /// Lazy values whose root is a record of an earlier declaration.
    old_roots: Vec<u32>,
    stack: Vec<u32>,
    /// For [`Builder::exprs`] (see `run`).
    ids: super::run::Ids,
    /// Its batches of records and side records.
    batch: Vec<u64>,
    side_batch: Vec<u32>,
    /// Records of earlier declarations that records use and that are not
    /// interned (yet), as records are added: what
    /// [`Builder::promote_shared`] interns.
    cands: Vec<u32>,
    /// While runs are read ahead (see [`Builder::share_done`]): a bit per
    /// record marked done, set as they are.
    done: Option<std::sync::Arc<Bits>>,
    /// Where [`Builder::exprs`] puts records (and side records) before
    /// they join `recs` (and `side`).
    fresh: Vec<u64>,
    fresh_side: Vec<u32>,
    /// Records below this are seen by views (see [`Builder::view`]).
    viewed: usize,
    /// What those records were before they were interned, for the views
    /// (see [`Undo`]), and the ones not yet handed over.
    undo: Option<std::sync::Arc<Undo>>,
    undo_new: Vec<(u32, u64)>,
}

/// Records that views see and the reader interned after the view was
/// made, as they were: a view's lazy values are built from them, not from
/// the arena ids the view has not got. (Each record is interned once, so
/// what is here never changes.)
/// How many records [`Builder::undo_new`] holds at most.
const UNDO_BATCH: usize = 1 << 12;

#[derive(Default)]
pub(crate) struct Undo(std::sync::RwLock<HashMap<u32, u64>>);

/// If `c` (a child of a record from `from` on) is a record of an earlier
/// declaration, not interned: push it to `cands` (an alias too; what it
/// stands for is looked up when the candidates are promoted).
#[inline(always)]
fn note_old(recs: &[u64], from: usize, c: u64, cands: &mut Vec<u32>) {
    if (c as usize) < from
        && let Some(&r) = recs.get(c as usize)
        && r & DONE == 0
    {
        cands.push(c as u32);
    }
}

impl Builder {
    /// A builder for an export of about `size` bytes.
    pub(super) fn with_capacity(size: u64) -> Self {
        let b = Builder::default();
        // About one expression per 56 bytes of a real export, and a side
        // record (3 words) per 8 of them; the space is only reserved, so
        // a smaller file costs nothing.
        let _ = size;
        b
    }

    /// The first record of the current declaration, for [`note_old`].
    #[inline(always)]
    fn note_from(&self) -> usize {
        self.from
    }

    /// Keep a bit per record marked done (for about `n` records), for the
    /// threads that read runs ahead to look up (see [`Runs::take`]), until
    /// [`Builder::unshare_done`].
    pub(super) fn share_done(&mut self, n: usize) -> std::sync::Arc<Bits> {
        let bits = std::sync::Arc::new(Bits::new(n));
        for (x, &r) in self.recs.iter().enumerate() {
            if r & DONE != 0 {
                bits.set(x);
            }
        }
        self.done = Some(bits.clone());
        bits
    }

    pub(super) fn unshare_done(&mut self) {
        self.done = None;
    }

    /// Record `x` is now marked done.
    #[inline(always)]
    fn mark(&self, x: usize) {
        if let Some(d) = &self.done {
            d.set(x);
        }
    }

    /// Whether `id` is the next expression id.
    #[inline(always)]
    fn next(&self, id: u64) -> bool {
        id == self.recs.len() as u64 && id < MAX_IDS
    }

    /// Whether `id` is an expression id seen so far.
    #[inline(always)]
    pub(super) fn has(&self, id: u64) -> bool {
        id < self.recs.len() as u64
    }

    /// An application record; false (and nothing added) unless `id` is
    /// the next id and the children are earlier ones.
    #[inline(always)]
    pub(super) fn app(&mut self, id: u64, f: u64, a: u64) -> bool {
        if !self.next(id) || f >= id || a >= id {
            return false;
        }
        let from = self.note_from();
        note_old(&self.recs, from, f, &mut self.cands);
        note_old(&self.recs, from, a, &mut self.cands);
        self.recs.push(T_APP << TAG | f << ID_BITS | a);
        true
    }

    /// The application and binder lines at the start of `s` (see `run`),
    /// the names below `names` mapping to themselves, and the constant
    /// lines among them that `leaf` takes (giving how many bytes each took
    /// and its arena id): how many bytes and lines it took.
    #[inline(never)]
    pub(super) fn exprs(&mut self, s: &[u8], names: u64, leaf: &mut LeafLine<'_>) -> (usize, u64) {
        let e = self.recs.len() as u64;
        // Room for as many lines as fit in `s`, at 32 bytes or more each.
        if e + s.len() as u64 / 32 >= MAX_IDS {
            return (0, 0);
        }
        if self.batch.is_empty() {
            self.batch = vec![0; BATCH];
            self.side_batch = vec![0; 3 * BATCH];
        }
        let from = self.note_from();
        let mut out = Out::<false> {
            batch: (&mut self.batch[..]).try_into().expect("a batch"),
            side_batch: (&mut self.side_batch[..]).try_into().expect("a batch"),
            sn: 0,
            o: self.side.len(),
            recs: &mut self.fresh,
            side: &mut self.fresh_side,
            names: names.min(u32::MAX as u64),
            old: &self.recs[..from],
            cands: &mut self.cands,
            first: 0,
            done: None,
            leaf: Some(leaf),
        };
        let res = super::run::all_exprs(s, e, &mut self.ids, &mut out);
        self.recs.extend_from_slice(&self.fresh);
        self.fresh.clear();
        self.side.extend_from_slice(&self.fresh_side);
        self.fresh_side.clear();
        res
    }

    /// The next expression id.
    pub(super) fn next_id(&self) -> u64 {
        self.recs.len() as u64
    }

    /// Records that [`Runs::take`] read ahead, starting at the next
    /// expression id (`side` being their side records, which they point
    /// into from `side_from` on), if their names are among the first
    /// `names` and the tables have room: whether it added them. `cands`
    /// are their children that may be of earlier declarations, in order (see
    /// [`Runs::take`]): noted here as [`Builder::exprs`] would have.
    pub(super) fn append_run(
        &mut self,
        recs: &[u64],
        side: &[u32],
        side_from: usize,
        cands: &[u32],
        max_name: u64,
        names: &IdMap,
    ) -> bool {
        let e = self.recs.len() as u64;
        let fits = e + recs.len() as u64 <= MAX_IDS
            && self.side.len() + side.len() <= u32::MAX as usize - 4;
        let names_ok = recs.is_empty() || max_name < names.identity_len().unwrap_or(0);
        if !fits || !names_ok {
            return false;
        }
        // Side offsets move from the run's table to this one.
        // (The sum stays in the low 32 bits: see `fits`.)
        let shift = (self.side.len() as u64).wrapping_sub(side_from as u64);
        self.recs.extend(recs.iter().map(|&r| {
            let t = tag(r);
            if t == T_LAM || t == T_PI {
                r.wrapping_add(shift)
            } else {
                r
            }
        }));
        self.side.extend_from_slice(side);
        // As `note_old`, but for the bits (rather than the records, which
        // are much larger): a record not marked there yet may be done by
        // now; `promote_shared` looks again.
        let from = self.note_from();
        let done = self.done.as_deref();
        for &c in cands {
            if (c as usize) < from && !done.is_some_and(|d| d.get(c as usize)) {
                self.cands.push(c);
            }
        }
        true
    }
}

/// Runs of application and binder lines read ahead of the builder (on
/// another thread), into tables of their own: see
/// [`Builder::append_run`].
#[derive(Default)]
pub(super) struct Runs {
    pub(super) recs: Vec<u64>,
    pub(super) side: Vec<u32>,
    /// The runs' children that may be of earlier declarations (see
    /// [`Out::first`]).
    pub(super) cands: Vec<u32>,
    batch: Vec<u64>,
    side_batch: Vec<u32>,
    ids: super::run::Ids,
}

impl Runs {
    /// The run at the start of `s`, its first id being `e`: how many bytes
    /// and lines it took, and the largest name id its binders use. Its
    /// children below `from` (at most `e`) go to `cands`, but those
    /// `done` says are done.
    pub(super) fn take(
        &mut self,
        s: &[u8],
        e: u64,
        from: u64,
        done: Option<&Bits>,
    ) -> (usize, u64, u64) {
        if e + s.len() as u64 / 32 >= MAX_IDS {
            return (0, 0, 0);
        }
        if self.batch.is_empty() {
            self.batch = vec![0; BATCH];
            self.side_batch = vec![0; 3 * BATCH];
        }
        let side_from = self.side.len();
        let mut out = Out::<true> {
            batch: (&mut self.batch[..]).try_into().expect("a batch"),
            side_batch: (&mut self.side_batch[..]).try_into().expect("a batch"),
            sn: 0,
            o: side_from,
            recs: &mut self.recs,
            side: &mut self.side,
            names: u32::MAX as u64,
            old: &[],
            cands: &mut self.cands,
            first: from.min(e),
            done,
            leaf: None,
        };
        let (n, m) = super::run::all_exprs(s, e, &mut self.ids, &mut out);
        // (Only binders, whose side records start with the name.)
        let max_name = self.side[side_from..].iter().step_by(3).max();
        (n, m, max_name.map_or(0, |&x| x as u64))
    }
}

impl Builder {
    /// [`note_old`] for the children of the record about to be added.
    #[inline(always)]
    fn note_kids(&mut self, kids: &[u64]) {
        let from = self.note_from();
        for &c in kids {
            note_old(&self.recs, from, c, &mut self.cands);
        }
    }

    /// Push a side record of `fields` with tag `t` and `flags`.
    #[inline(always)]
    fn with_side(&mut self, t: u64, flags: u64, fields: &[u32]) -> bool {
        let Ok(o) = u32::try_from(self.side.len()) else {
            return false;
        };
        if o > u32::MAX - 4 {
            return false;
        }
        self.side.extend_from_slice(fields);
        self.recs.push(t << TAG | flags << 32 | o as u64);
        true
    }

    /// A binder record; as [`Builder::app`].
    #[inline(always)]
    pub(super) fn binder(
        &mut self,
        id: u64,
        pi: bool,
        bi: BinderInfo,
        name: NameId,
        ty: u64,
        body: u64,
    ) -> bool {
        if !self.next(id) || ty >= id || body >= id {
            return false;
        }
        let t = if pi { T_PI } else { T_LAM };
        self.note_kids(&[ty, body]);
        self.with_side(t, bi_bits(bi), &[name.0, ty as u32, body as u32])
    }

    /// A let record; as [`Builder::app`].
    pub(super) fn let_in(
        &mut self,
        id: u64,
        name: NameId,
        [ty, value, body]: [u64; 3],
        nondep: bool,
    ) -> bool {
        if !self.next(id) || ty >= id || value >= id || body >= id {
            return false;
        }
        let f = [name.0, ty as u32, value as u32, body as u32];
        self.note_kids(&[ty, value, body]);
        self.with_side(T_LET, nondep as u64, &f)
    }

    /// A projection record; as [`Builder::app`].
    pub(super) fn proj(&mut self, id: u64, s: NameId, i: u32, e: u64) -> bool {
        if !self.next(id) || e >= id {
            return false;
        }
        self.note_kids(&[e]);
        self.with_side(T_PROJ, 0, &[s.0, i, e as u32])
    }

    /// A leaf, interned as `arena`; as [`Builder::app`].
    #[inline(always)]
    pub(super) fn leaf(&mut self, id: u64, arena: u32) -> bool {
        if !self.next(id) {
            return false;
        }
        self.mark(self.recs.len());
        self.recs.push(DONE | arena as u64);
        true
    }

    /// An `mdata` record, standing for `inner`; as [`Builder::app`].
    pub(super) fn alias(&mut self, id: u64, inner: u64) -> bool {
        if !self.next(id) || inner >= id {
            return false;
        }
        let r = self.recs[inner as usize];
        self.recs.push(if r & DONE != 0 || tag(r) == T_ALIAS {
            r
        } else {
            T_ALIAS << TAG | inner
        });
        true
    }

    /// `id`, or the id it stands for if it is an alias.
    #[inline(always)]
    fn real(&self, id: u32) -> u32 {
        let r = self.recs[id as usize];
        // (An alias is never marked done or needed.)
        if r >> TAG == T_ALIAS {
            (r & ID_MASK) as u32
        } else {
            id
        }
    }

    /// The arena id of expression `id`, if it is interned.
    #[inline(always)]
    fn known(&self, id: u32) -> Option<u32> {
        let r = self.recs[self.real(id) as usize];
        (r & DONE != 0).then_some(r as u32)
    }

    /// Intern expression `id` (and what it needs) in `env`.
    pub(super) fn promote(&mut self, env: &mut Env, append: bool, id: u64) -> R<ExprId> {
        let i = self.real(id as u32);
        if let Some(a) = self.known(i) {
            return Ok(ExprId(a));
        }
        if i as usize >= self.from {
            return self.promote_recent(env, append, i as usize);
        }
        self.promote_old(env, append, i)
    }

    /// [`Builder::promote`] for a record since the last declaration line.
    /// Records come children first, so this needs no stack: a pass down
    /// from `i` marks the recent records it needs (until none is left to
    /// find), and a pass up interns them. (What an alias it needs stands
    /// for is marked; the alias is unmarked as it is passed.)
    fn promote_recent(&mut self, env: &mut Env, append: bool, i: usize) -> R<ExprId> {
        let from = self.from;
        let recs = &mut self.recs;
        recs.store_shared(i, recs[i] | NEEDED);
        // Records marked and not yet passed.
        let mut left = 1usize;
        // Mark record `c` if it is recent and not yet marked or done:
        // how many it marked.
        let mark = |recs: &mut Slab<u64>, c: u32| -> usize {
            let c = c as usize;
            if c >= from && recs[c] & (DONE | NEEDED) == 0 {
                recs.store_shared(c, recs[c] | NEEDED);
                1
            } else {
                0
            }
        };
        let mut j = i;
        loop {
            let r = recs[j];
            if r & NEEDED != 0 {
                left -= 1;
                match tag(r) {
                    T_APP => {
                        left += mark(recs, (r >> ID_BITS & ID_MASK) as u32);
                        left += mark(recs, (r & ID_MASK) as u32);
                    }
                    T_ALIAS => {
                        left += mark(recs, (r & ID_MASK) as u32);
                        // Not interned itself: the pass up skips it.
                        recs.store_shared(j, r & !NEEDED);
                    }
                    T_LAM | T_PI => {
                        let [_, ty, body] = binder_side(&self.side, r);
                        left += mark(recs, ty);
                        left += mark(recs, body);
                    }
                    _ => {
                        let (kids, k) = decode(&self.side, r).kids();
                        for &c in &kids[..k] {
                            left += mark(recs, c);
                        }
                    }
                }
                if left == 0 {
                    break;
                }
            }
            // A marked record is left, below `j`.
            j -= 1;
        }
        for x in j..=i {
            let r = self.recs[x];
            if r & NEEDED == 0 {
                continue;
            }
            let r = r & !NEEDED;
            let id = match tag(r) {
                T_APP => {
                    let f = self.arena_id(env, append, (r >> ID_BITS & ID_MASK) as u32)?;
                    let a = self.arena_id(env, append, (r & ID_MASK) as u32)?;
                    add_node(env, append, ExprNode::App(ExprId(f), ExprId(a)))?
                }
                t @ (T_LAM | T_PI) => {
                    let [name, ty, body] = binder_side(&self.side, r);
                    let ty = ExprId(self.arena_id(env, append, ty)?);
                    let body = ExprId(self.arena_id(env, append, body)?);
                    let (bi, name) = (bits_bi(r >> 32), NameId(name));
                    add_node(
                        env,
                        append,
                        if t == T_PI {
                            ExprNode::Pi(bi, name, ty, body)
                        } else {
                            ExprNode::Lam(bi, name, ty, body)
                        },
                    )?
                }
                _ => {
                    let n = decode(&self.side, r);
                    let (kids, k) = n.kids();
                    let mut ids = [0u32; 3];
                    for (&c, id) in kids[..k].iter().zip(&mut ids) {
                        *id = self.arena_id(env, append, c)?;
                    }
                    add(env, append, n, ids)?
                }
            };
            self.recs.store_shared(x, DONE | id as u64);
            self.mark(x);
        }
        Ok(ExprId(self.recs[i] as u32))
    }

    /// The arena id of expression `c` (interned by now if it is recent,
    /// else interned here).
    #[inline(always)]
    fn arena_id(&mut self, env: &mut Env, append: bool, c: u32) -> R<u32> {
        let mut r = self.recs[c as usize];
        if r & DONE != 0 {
            return Ok(r as u32);
        }
        let mut c = c;
        if r >> TAG == T_ALIAS {
            c = (r & ID_MASK) as u32;
            r = self.recs[c as usize];
            if r & DONE != 0 {
                return Ok(r as u32);
            }
        }
        Ok(self.promote_old(env, append, c)?.0)
    }

    /// [`Builder::promote`] for any record, with a stack.
    fn promote_old(&mut self, env: &mut Env, append: bool, i: u32) -> R<ExprId> {
        let mut stack = std::mem::take(&mut self.stack);
        stack.clear();
        stack.push(i);
        let res: R<()> = (|| {
            while let Some(&top) = stack.last() {
                let r = self.recs[top as usize];
                if r & DONE != 0 {
                    stack.pop();
                    continue;
                }
                let t = tag(r);
                let (kids, k) = match t {
                    T_APP => (
                        [(r >> ID_BITS & ID_MASK) as u32, (r & ID_MASK) as u32, 0],
                        2,
                    ),
                    T_LAM | T_PI => {
                        let [_, ty, body] = binder_side(&self.side, r);
                        ([ty, body, 0], 2)
                    }
                    _ => decode(&self.side, r).kids(),
                };
                let mut ready = true;
                let mut ids = [0u32; 3];
                for (&c, id) in kids[..k].iter().zip(&mut ids) {
                    let (mut c, mut r) = (c, self.recs[c as usize]);
                    // (An alias is never marked done.)
                    if r >> TAG == T_ALIAS {
                        c = (r & ID_MASK) as u32;
                        r = self.recs[c as usize];
                    }
                    if r & DONE != 0 {
                        *id = r as u32;
                    } else {
                        stack.push(c);
                        ready = false;
                    }
                }
                if !ready {
                    continue;
                }
                let e = |i: usize| ExprId(ids[i]);
                let id = match t {
                    T_APP => add_node(env, append, ExprNode::App(e(0), e(1)))?,
                    T_LAM | T_PI => {
                        let (bi, name) = (bits_bi(r >> 32), NameId(binder_side(&self.side, r)[0]));
                        add_node(
                            env,
                            append,
                            if t == T_PI {
                                ExprNode::Pi(bi, name, e(0), e(1))
                            } else {
                                ExprNode::Lam(bi, name, e(0), e(1))
                            },
                        )?
                    }
                    _ => add(env, append, decode(&self.side, r), ids)?,
                };
                if (top as usize) < self.viewed {
                    self.undo_new.push((top, r));
                    if self.undo_new.len() >= UNDO_BATCH {
                        self.hand_over_undo();
                    }
                }
                self.recs.store_shared(top as usize, DONE | id as u64);
                self.mark(top as usize);
                stack.pop();
            }
            Ok(())
        })();
        self.stack = stack;
        res?;
        Ok(ExprId(self.recs[i as usize] as u32))
    }

    /// A theorem's value: its arena id if it is interned, else a lazy
    /// placeholder.
    pub(super) fn value(&mut self, id: u64) -> R<ExprId> {
        let i = self.real(id as u32);
        if let Some(a) = self.known(i) {
            return Ok(ExprId(a));
        }
        let k = self.roots.len() as u32;
        if k >= u32::MAX - LAZY_BASE {
            return Err(Fail::from(Overflow("too many theorems")));
        }
        self.roots.push(i);
        self.starts.push(i.min(self.from as u32));
        if (i as usize) < self.from {
            self.old_roots.push(i);
        }
        Ok(ExprId(LAZY_BASE + k))
    }

    /// At the end of a declaration.
    #[inline(always)]
    pub(super) fn decl_done(&mut self) {
        self.from = self.recs.len();
    }

    /// Intern every record, and give each expression id's arena id (in
    /// order) and each lazy value's.
    pub(super) fn into_eager(mut self, env: &mut Env, append: bool) -> R<(Vec<u32>, Vec<u32>)> {
        // Children come first, so one pass in order does.
        for x in 0..self.recs.len() {
            let r = self.recs[x];
            if r & DONE != 0 {
                continue;
            }
            if tag(r) == T_ALIAS {
                self.recs.store_shared(x, self.recs[(r & ID_MASK) as usize]);
                continue;
            }
            let n = decode(&self.side, r);
            let (kids, k) = n.kids();
            let mut ids = [0u32; 3];
            for (&c, id) in kids[..k].iter().zip(&mut ids) {
                *id = self.recs[c as usize] as u32;
            }
            let id = add(env, append, n, ids)?;
            self.recs.store_shared(x, DONE | id as u64);
        }
        let ids: Vec<u32> = self.recs.iter().map(|&r| r as u32).collect();
        let roots = self.roots.iter().map(|&i| ids[i as usize]).collect();
        Ok((ids, roots))
    }

    /// Intern the records that a later declaration's records use (and
    /// the roots of values older than their declarations), so that each
    /// record left is used by its own declaration's value alone: built
    /// once here, not again for every value that uses it.
    fn promote_shared(&mut self, env: &mut Env, append: bool) -> R<()> {
        // Noted as the records were added, in order.
        for c in std::mem::take(&mut self.cands) {
            let c = self.real(c);
            if self.recs[c as usize] & DONE == 0 {
                self.promote_old(env, append, c)?;
            }
        }
        self.promote_old_roots(env, append)
    }

    fn promote_old_roots(&mut self, env: &mut Env, append: bool) -> R<()> {
        for i in std::mem::take(&mut self.old_roots) {
            if self.recs[i as usize] & DONE == 0 {
                self.promote_old(env, append, i)?;
            }
        }
        Ok(())
    }

    /// Intern the shared terms (see `promote_shared`): the first part of
    /// putting the lazy values together, which views (and their values)
    /// survive; [`Builder::finish_stored`] is the rest.
    pub(super) fn finish_shared(&mut self, env: &mut Env, append: bool) -> R<()> {
        if !self.roots.is_empty() {
            self.promote_shared(env, append)?;
            self.hand_over_undo();
            crate::trace::phase("promote_shared");
        }
        Ok(())
    }

    /// The rest, once the views are gone.
    pub(super) fn finish_stored(
        self,
        env: &mut Env,
        threads: usize,
    ) -> R<Option<Box<dyn LazyValues>>> {
        if self.roots.is_empty() {
            return Ok(None);
        }
        #[cfg(test)]
        let wide_test = tests::WIDE.get();
        #[cfg(not(test))]
        let wide_test = false;
        let wide = env.exprs.len() >= 1 << ID_BITS || wide_test;
        Ok(Some(Box::new(self.into_stored(threads, wide))))
    }

    /// The records that values still need, renumbered in order (see
    /// [`Stored`]): what is interned (most records, by now) and the
    /// aliases go, and the children of what is left name an interned
    /// expression by its arena id. `wide` if an arena id may not fit an
    /// application record's field.
    ///
    /// Where each record went (a stored child reference: its arena id, or
    /// its new index) is kept in a table of its own, so that the pages of
    /// the records already passed go back to the system as the pass goes
    /// (the old and new tables would otherwise be held at once, at the
    /// peak of the read). On one thread, one pass in order does it
    /// (children come first, so where they went is known); on several, a
    /// range of records each, and the children are put right in a second
    /// pass.
    fn into_stored(self, threads: usize, wide: bool) -> Stored {
        let Builder {
            mut recs,
            mut side,
            mut roots,
            mut starts,
            ..
        } = self;
        let n = recs.len();
        // Each start, for now: the first record kept from it on (its
        // value's root, at the latest).
        for (s, &r) in starts.iter_mut().zip(&roots) {
            while *s < r && !kept(recs[*s as usize]) {
                *s += 1;
            }
        }
        let threads = threads.clamp(1, n.div_ceil(MIN_RANGE).max(1));
        let (out, out_side, fwd) = if threads == 1 {
            if wide {
                into_stored_here::<true>(recs.as_mut_slice(), side.as_mut_slice())
            } else {
                into_stored_here::<false>(recs.as_mut_slice(), side.as_mut_slice())
            }
        } else {
            into_stored_par(recs.as_mut_slice(), side.as_mut_slice(), threads, wide)
        };
        drop((recs, side));
        // An alias's target (see `into_stored_par`; it is not an alias).
        let at = |i: u32| {
            let e = fwd[i as usize];
            if e & ALIAS_REF != 0 && e & ARENA == 0 {
                fwd[(e & !ALIAS_REF) as usize]
            } else {
                e
            }
        };
        for r in &mut roots {
            *r = at(*r);
        }
        for s in &mut starts {
            *s = at(*s) & !ARENA;
        }
        drop(fwd);
        roots.shrink_to_fit();
        starts.shrink_to_fit();
        Stored {
            recs: out,
            side: out_side,
            roots,
            starts,
        }
    }
}

/// [`Builder::into_stored`] on this thread (`WIDE` as there).
fn into_stored_here<const WIDE: bool>(
    recs: &mut [u64],
    side: &mut [u32],
) -> (Zeroed<u64>, Zeroed<u32>, Zeroed<u32>) {
    let n = recs.len();
    let mut fwd: Zeroed<u32> = Zeroed::new(n);
    let mut out = Zeroed::new(n);
    let mut out_side = Zeroed::new(side.len() + if WIDE { 2 * n } else { 0 });
    let mut part = SidePart {
        words: &mut out_side,
        used: 0,
        base: 0,
    };
    let (fw, o) = (&mut fwd[..], &mut out[..]);
    let mut k = 0usize;
    // Side records come in the order of their records: those below
    // `side_done` are passed.
    let (mut side_done, mut side_from) = (0, 0);
    for lo in (0..n).step_by(RELEASE) {
        let hi = (lo + RELEASE).min(n);
        for i in lo..hi {
            let r = recs[i];
            let e = if r & DONE != 0 {
                ARENA | r as u32
            } else if tag(r) == T_ALIAS {
                fw[(r & ID_MASK) as usize]
            } else {
                let t = tag(r);
                o[k] = if t == T_APP && !WIDE {
                    let f = fw[(r >> ID_BITS & ID_MASK) as usize];
                    stored_app(f, fw[(r & ID_MASK) as usize])
                } else {
                    if t != T_APP {
                        side_done = r as u32 as usize;
                    }
                    stored(side, 0, r, WIDE, &mut part, |c| fw[c as usize])
                };
                k += 1;
                k as u32 - 1
            };
            fw[i] = e;
        }
        crate::slab::release(&mut recs[lo.saturating_sub(RELEASE_MARGIN)..hi]);
        crate::slab::release(&mut side[side_from..side_done]);
        side_from = side_done.saturating_sub(2 * RELEASE_MARGIN);
    }
    let used = part.used;
    out.truncate(k);
    out_side.truncate(used);
    (out, out_side, fwd)
}

/// Whether record `r` stays in the stored table: compound, not interned.
#[inline(always)]
fn kept(r: u64) -> bool {
    r & DONE == 0 && tag(r) != T_ALIAS
}

/// Records that [`Builder::into_stored`] passes between giving pages
/// back, and how far back it gives them again (pages that straddle the
/// boundary of the last range: 64 KiB, the largest page size).
const RELEASE: usize = 1 << 18;
const RELEASE_MARGIN: usize = (64 << 10) / 8;

/// While [`into_stored_par`] runs: an alias's reference is its target's
/// record, with this bit (never set in a record's index).
const ALIAS_REF: u32 = 1 << 30;

/// Where [`stored`] puts side records: their offset in the whole table.
trait SideOut {
    fn put(&mut self, words: &[u32]) -> u64;
}

impl SideOut for Vec<u32> {
    #[inline(always)]
    fn put(&mut self, words: &[u32]) -> u64 {
        let o = self.len() as u64;
        self.extend_from_slice(words);
        o
    }
}

/// A range's part of the side table, from offset `base` of the whole.
struct SidePart<'a> {
    words: &'a mut [u32],
    used: usize,
    base: u64,
}

impl SideOut for SidePart<'_> {
    #[inline(always)]
    fn put(&mut self, words: &[u32]) -> u64 {
        let o = self.base + self.used as u64;
        self.words[self.used..self.used + words.len()].copy_from_slice(words);
        self.used += words.len();
        o
    }
}

/// The side words that record `r` (kept) takes when stored.
#[inline(always)]
fn stored_side_words(r: u64, wide: bool) -> usize {
    match tag(r) {
        T_APP if wide => 2,
        T_APP => 0,
        T_APPS => 2,
        T_LET => 4,
        _ => 3,
    }
}

/// Record `r` (compound, not done) as a stored one, its side record (in
/// `side`, which starts at offset `side_base` of the whole) put in
/// `out_side`, its children's references given by `kid`.
#[inline(always)]
fn stored(
    side: &[u32],
    side_base: usize,
    r: u64,
    wide: bool,
    out_side: &mut impl SideOut,
    kid: impl Fn(u32) -> u32,
) -> u64 {
    let t = tag(r);
    if t == T_APP {
        let (f, a) = (
            kid((r >> ID_BITS & ID_MASK) as u32),
            kid((r & ID_MASK) as u32),
        );
        if wide {
            return T_APPS << TAG | out_side.put(&[f, a]);
        }
        return stored_app(f, a);
    }
    let from = r as u32 as usize - side_base;
    let o = match t {
        T_LET => {
            let f = &side[from..from + 4];
            out_side.put(&[f[0], kid(f[1]), kid(f[2]), kid(f[3])])
        }
        T_PROJ => {
            let f = &side[from..from + 3];
            out_side.put(&[f[0], f[1], kid(f[2])])
        }
        _ => {
            let f = &side[from..from + 3];
            out_side.put(&[f[0], kid(f[1]), kid(f[2])])
        }
    };
    r & !0xffff_ffff | o
}

/// A stored application of stored children `f` and `a` (fitting its
/// fields).
#[inline(always)]
fn stored_app(f: u32, a: u32) -> u64 {
    const _: () =
        assert!(APP_F_ARENA == (ARENA as u64) << 27 && APP_A_ARENA == (ARENA as u64) << 31);
    T_APP << TAG
        | ((f & ARENA) as u64) << 27
        | ((a & ARENA) as u64) << 31
        | ((f & !ARENA) as u64) << ID_BITS
        | (a & !ARENA) as u64
}

/// [`Builder::into_stored`] on `threads` threads, ranges of records each:
/// a pass counts each range's kept records and side words; one copies
/// them (children as export ids) into their place, notes where each
/// record went, and gives the range's pages back; one puts the children
/// right. An alias's reference is its target's record (with
/// [`ALIAS_REF`]), put right at the end.
fn into_stored_par(
    recs: &mut [u64],
    side: &mut [u32],
    threads: usize,
    wide: bool,
) -> (Zeroed<u64>, Zeroed<u32>, Zeroed<u32>) {
    let n = recs.len();
    let per = n.div_ceil(threads * 4).max(1);
    // Per range: records kept, their side words, the first one's offset.
    let mut counts = vec![(0usize, 0usize, usize::MAX); n.div_ceil(per)];
    par_each(
        threads,
        recs.chunks(per).zip(counts.iter_mut()),
        |(rs, count)| {
            for &r in rs {
                if kept(r) {
                    count.0 += 1;
                    count.1 += stored_side_words(r, wide);
                    if tag(r) != T_APP && count.2 == usize::MAX {
                        count.2 = r as u32 as usize;
                    }
                }
            }
        },
    );
    // A range's side records start where its first one does (they come
    // in the order of their records), or where the next range's do.
    let mut next = side.len();
    for c in counts.iter_mut().rev() {
        if c.2 == usize::MAX {
            c.2 = next;
        }
        next = c.2;
    }
    let mut out = Zeroed::new(counts.iter().map(|c| c.0).sum());
    let mut out_side = Zeroed::new(counts.iter().map(|c| c.1).sum());
    let mut fwd = Zeroed::new(n);
    let mut ranges = Vec::with_capacity(counts.len());
    {
        let (mut o, mut os) = (&mut out[..], &mut out_side[..]);
        let mut sd = &mut side[counts.first().map_or(0, |c| c.2)..];
        let mut fw = &mut fwd[..];
        let (mut at, mut side_at) = (0usize, 0usize);
        for (c, rs) in recs.chunks_mut(per).enumerate() {
            let (k, sw, first) = counts[c];
            let (oh, ot) = std::mem::take(&mut o).split_at_mut(k);
            let (sh, st) = std::mem::take(&mut os).split_at_mut(sw);
            let (fh, ft) = std::mem::take(&mut fw).split_at_mut(rs.len());
            let own = counts.get(c + 1).map_or(sd.len(), |c2| c2.2 - first);
            let (dh, dt) = std::mem::take(&mut sd).split_at_mut(own);
            ranges.push((rs, fh, dh, first, oh, sh, at, side_at));
            (o, os, fw, sd) = (ot, st, ft, dt);
            at += k;
            side_at += sw;
        }
    }
    par_each(
        threads,
        ranges.into_iter(),
        |(rs, fw, sd, first, o, sh, at, side_at)| {
            let mut part = SidePart {
                words: sh,
                used: 0,
                base: side_at as u64,
            };
            let mut k = 0;
            for (r, f) in rs.iter().zip(fw.iter_mut()) {
                let r = *r;
                *f = if r & DONE != 0 {
                    ARENA | r as u32
                } else if tag(r) == T_ALIAS {
                    ALIAS_REF | (r & ID_MASK) as u32
                } else {
                    o[k] = stored(sd, first, r, wide, &mut part, |c| c);
                    k += 1;
                    (at + k - 1) as u32
                };
            }
            crate::slab::release(rs);
            crate::slab::release(sd);
        },
    );
    let kid = |c: u32| {
        let e = fwd[c as usize];
        if e & ALIAS_REF != 0 && e & ARENA == 0 {
            fwd[(e & !ALIAS_REF) as usize]
        } else {
            e
        }
    };
    let mut seconds = Vec::with_capacity(counts.len());
    {
        let (mut o, mut os) = (&mut out[..], &mut out_side[..]);
        for &(k, sw, _) in &counts {
            let (oh, ot) = std::mem::take(&mut o).split_at_mut(k);
            let (sh, st) = std::mem::take(&mut os).split_at_mut(sw);
            seconds.push((oh, sh));
            (o, os) = (ot, st);
        }
    }
    par_each(threads, seconds.into_iter(), |(o, sh)| {
        let mut q = 0;
        for r in o.iter_mut() {
            let fields: &[usize] = match tag(*r) {
                T_APP => {
                    *r = stored_app(
                        kid((*r >> ID_BITS & ID_MASK) as u32),
                        kid((*r & ID_MASK) as u32),
                    );
                    continue;
                }
                T_APPS => &[0, 1],
                T_LET => &[1, 2, 3],
                T_PROJ => &[2],
                _ => &[1, 2],
            };
            for &f in fields {
                sh[q + f] = kid(sh[q + f]);
            }
            q += stored_side_words(*r, true);
        }
    });
    (out, out_side, fwd)
}

/// The fewest records per thread that [`Builder::into_stored`] uses
/// (fewer in the tests, so that small exports take several ranges).
#[cfg(not(test))]
const MIN_RANGE: usize = 1 << 18;
#[cfg(test)]
const MIN_RANGE: usize = 1 << 10;

/// `f` on each item of `items`, on `threads` threads (taking the next
/// item as each is done).
fn par_each<T: Send>(threads: usize, items: impl Iterator<Item = T> + Send, f: impl Fn(T) + Sync) {
    if threads <= 1 {
        items.for_each(f);
        return;
    }
    let items = std::sync::Mutex::new(items);
    std::thread::scope(|s| {
        for _ in 0..threads {
            s.spawn(|| {
                loop {
                    let Some(x) = items.lock().expect("items").next() else {
                        return;
                    };
                    f(x);
                }
            });
        }
    });
}

/// Node `n` in `sink`, its children being `ids` (in [`Node::kids`]'s
/// order); `owned` if no other value or interned term uses it (see
/// [`TermSink::expr_owned`]); `keep` if the sink keeps shared names
/// ([`TermSink::keeps_shared`]).
#[inline(always)]
fn make<S: TermSink + ?Sized>(
    sink: &mut S,
    n: Node,
    ids: [ExprId; 3],
    owned: bool,
    keep: bool,
) -> ExprId {
    let shared_name = |sink: &mut S, n| if keep { n } else { sink.shared_name(n) };
    let expr = |sink: &mut S, node| {
        if owned {
            sink.expr_owned(node)
        } else {
            sink.expr(node)
        }
    };
    match n {
        Node::App(..) => expr(sink, ExprNode::App(ids[0], ids[1])),
        Node::Bind { pi, bi, name, .. } => {
            let name = shared_name(sink, name);
            let (t, b) = (ids[0], ids[1]);
            let node = if pi {
                ExprNode::Pi(bi, name, t, b)
            } else {
                ExprNode::Lam(bi, name, t, b)
            };
            expr(sink, node)
        }
        Node::Let { name, nondep, .. } => {
            let name = shared_name(sink, name);
            let binder = LetBinder {
                name,
                ty: ids[0],
                value: ids[1],
                nondep,
            };
            sink.let_in(binder, ids[2])
        }
        Node::Proj(s, i, _) => {
            let s = shared_name(sink, s);
            expr(sink, ExprNode::Proj(s, i, ids[0]))
        }
    }
}

/// What [`Builder::exprs`] hands a constant line to: given its expected
/// id and the input from it, how many bytes it took and its arena id.
pub(super) type LeafLine<'a> = dyn FnMut(u64, &[u8]) -> Option<(usize, u32)> + 'a;

/// Lines in a batch of [`Builder::exprs`].
const BATCH: usize = super::run::BATCH as usize;

/// Where [`Builder::exprs`] puts records: a batch at a time, to `recs`
/// and `side`.
struct Out<'a, const AHEAD: bool> {
    /// Records by id (modulo the batch's length).
    batch: &'a mut [u64; BATCH],
    side_batch: &'a mut [u32; 3 * BATCH],
    /// Side records in the batch.
    sn: usize,
    /// The side table's length with the batch.
    o: usize,
    recs: &'a mut Vec<u64>,
    side: &'a mut Vec<u32>,
    /// The names that map to themselves; binders with other names (in an
    /// export whose names are not so) take the slow way.
    names: u64,
    /// The records of earlier declarations, for [`note_old`] (not in
    /// `recs`, so that the compiler knows that they stay put).
    old: &'a [u64],
    /// With `AHEAD` (a run read ahead, see [`Runs::take`]): every child
    /// below `first`, for [`Builder::append_run`] to note as [`note_old`]
    /// would have.
    cands: &'a mut Vec<u32>,
    /// With `AHEAD`: children below this are candidates (at most the run's
    /// first id, and at least where its declaration's expressions start).
    first: u64,
    /// With `AHEAD`: records known to be done, not candidates.
    done: Option<&'a Bits>,
    /// For constant lines (see [`Builder::exprs`]).
    leaf: Option<&'a mut LeafLine<'a>>,
}

impl<const AHEAD: bool> Out<'_, AHEAD> {
    /// A child `c` of a record: see [`note_old`], and `cands`.
    #[inline(always)]
    fn note(&mut self, c: u64) {
        if AHEAD {
            if c < self.first && !self.done.is_some_and(|d| d.get(c as usize)) {
                self.cands.push(c as u32);
            }
        } else {
            note_old(self.old, self.old.len(), c, self.cands);
        }
    }
}

impl<const AHEAD: bool> super::run::Records for Out<'_, AHEAD> {
    #[inline(always)]
    fn app(&mut self, id: u64, f: u64, a: u64) -> bool {
        if f >= id || a >= id {
            return false;
        }
        self.note(f);
        self.note(a);
        self.batch[id as usize % BATCH] = T_APP << TAG | f << ID_BITS | a;
        true
    }

    #[inline(always)]
    fn binder(&mut self, id: u64, pi: bool, bi: BinderInfo, name: u64, ty: u64, body: u64) -> bool {
        let o = self.o;
        if name >= self.names || ty >= id || body >= id || o > u32::MAX as usize - 4 {
            return false;
        }
        self.note(ty);
        self.note(body);
        let side = &mut self.side_batch.as_chunks_mut::<3>().0[self.sn % BATCH];
        *side = [name as u32, ty as u32, body as u32];
        self.sn += 1;
        self.o = o + 3;
        let t = if pi { T_PI } else { T_LAM };
        self.batch[id as usize % BATCH] = t << TAG | bi_bits(bi) << 32 | o as u64;
        true
    }

    #[inline(always)]
    fn leaf(&mut self, id: u64, s: &[u8]) -> Option<usize> {
        let (n, e) = self.leaf.as_mut()?(id, s)?;
        self.batch[id as usize % BATCH] = DONE | e as u64;
        Some(n)
    }

    fn flush(&mut self, ids: std::ops::Range<u64>) {
        // At most a batch, from `ids.start` on (modulo its length).
        let (from, n) = (ids.start as usize % BATCH, (ids.end - ids.start) as usize);
        let first = n.min(BATCH - from);
        self.recs.extend_from_slice(&self.batch[from..from + first]);
        self.recs.extend_from_slice(&self.batch[..n - first]);
        self.side.extend_from_slice(&self.side_batch[..3 * self.sn]);
        self.sn = 0;
    }
}

/// In a stored record, a child that is an interned expression: its arena
/// id, with this bit (else it is a record's index).
const ARENA: u32 = 1 << 31;
/// In a stored application: its function, or its argument, is an arena id
/// (the bits `NEEDED` and the one below `TAG` are free once read).
const APP_F_ARENA: u64 = 1 << 58;
const APP_A_ARENA: u64 = NEEDED;

/// Stored record `r`, decoded: its children are records' indices or (with
/// [`ARENA`]) arena ids.
#[inline(always)]
fn decode_stored(side: &[u32], r: u64) -> Node {
    match tag(r) {
        T_APP => {
            const _: () =
                assert!(APP_F_ARENA == (ARENA as u64) << 27 && APP_A_ARENA == (ARENA as u64) << 31);
            Node::App(
                (r >> ID_BITS & ID_MASK) as u32 | (r >> 27) as u32 & ARENA,
                (r & ID_MASK) as u32 | (r >> 31) as u32 & ARENA,
            )
        }
        T_APPS => {
            let o = r as u32 as usize;
            Node::App(side[o], side[o + 1])
        }
        _ => decode(side, r),
    }
}

/// Theorem values of an export: the records they need, in the export's
/// order but numbered densely (no interned record, alias or record that
/// no value reaches), compound all; children as [`decode_stored`] says.
/// A root is a record's index, or an arena id (with [`ARENA`]); a start,
/// the index of the first record of its value's declaration.
struct Stored {
    recs: Zeroed<u64>,
    side: Zeroed<u32>,
    roots: Vec<u32>,
    starts: Vec<u32>,
}

/// Each thread's working space for [`Stored::decode`].
#[derive(Default)]
struct Scratch {
    /// Per record of the value's own range, from its start: the sink's
    /// id.
    own: Vec<u32>,
    /// Older records (from other declarations): the sink's ids, and the
    /// stack that builds them.
    memo: HashMap<u32, ExprId>,
    stack: Vec<u32>,
}

thread_local! {
    static SCRATCH: RefCell<Scratch> = RefCell::default();
}

impl LazyValues for Stored {
    fn decode(&self, _env: &Env, k: u32, sink: &mut dyn TermSink) -> Result<ExprId, String> {
        self.decode_in(k, sink)
    }

    fn decode_store(
        &self,
        _env: &Env,
        k: u32,
        sink: &mut crate::check::store::Store<'_>,
    ) -> Result<ExprId, String> {
        self.decode_in(k, sink)
    }

    fn count(&self) -> usize {
        self.roots.len()
    }

    fn heap_bytes(&self) -> usize {
        self.recs.len() * 8
            + self.side.len() * 4
            + (self.roots.capacity() + self.starts.capacity()) * 4
    }
}

impl Stored {
    /// Value `k`, built in `sink`.
    fn decode_in<S: TermSink + ?Sized>(&self, k: u32, sink: &mut S) -> Result<ExprId, String> {
        let (Some(&root), Some(&start)) = (self.roots.get(k as usize), self.starts.get(k as usize))
        else {
            return Err("internal: no such lazy value".into());
        };
        SCRATCH.with(|s| {
            let s = &mut *s.borrow_mut();
            s.memo.clear();
            s.stack.clear();
            self.build_own(root, start, sink, s)
        })
    }

    /// Value `root`, whose own records are those from `start` on: built
    /// in order (children first). Every one of them is part of the value:
    /// what else its declaration's lines held is interned or gone (see
    /// [`Builder::into_stored`]), and a declaration has one value. (Were
    /// one not, it would only be built for nothing.) Older records are
    /// built by [`Stored::build`].
    fn build_own<S: TermSink + ?Sized>(
        &self,
        root: u32,
        start: u32,
        sink: &mut S,
        s: &mut Scratch,
    ) -> Result<ExprId, String> {
        if root & ARENA != 0 {
            return Ok(sink.shared_expr(ExprId(root & !ARENA)));
        }
        let (recs, side) = (&self.recs, &self.side);
        let keep = sink.keeps_shared();
        s.own.clear();
        let kid = |c, sink: &mut S, s: &mut Scratch| self.own_kid(c, start, keep, sink, s);
        // Records of the value's own declaration are taken as used by it
        // alone (one that a later value uses too is built there again, by
        // `build`, hash-consed).
        for &r in &recs[start as usize..=root as usize] {
            let id = match decode_stored(side, r) {
                Node::App(f, a) => {
                    let (f, a) = (kid(f, sink, s)?, kid(a, sink, s)?);
                    sink.expr_owned(ExprNode::App(f, a))
                }
                n => {
                    let (kids, k) = n.kids();
                    let mut ids = [ExprId(0); 3];
                    for (&c, id) in kids[..k].iter().zip(&mut ids) {
                        *id = kid(c, sink, s)?;
                    }
                    make(sink, n, ids, true, keep)
                }
            };
            s.own.push(id.0);
        }
        Ok(ExprId(*s.own.last().expect("the root")))
    }

    /// The sink's id for child `c` of a record in [`Stored::build_own`]
    /// (its value's records being from `start` on).
    #[inline(always)]
    fn own_kid<S: TermSink + ?Sized>(
        &self,
        c: u32,
        start: u32,
        keep: bool,
        sink: &mut S,
        s: &mut Scratch,
    ) -> Result<ExprId, String> {
        if c & ARENA != 0 {
            let a = ExprId(c & !ARENA);
            Ok(if keep { a } else { sink.shared_expr(a) })
        } else if c >= start {
            Ok(ExprId(s.own[(c - start) as usize]))
        } else {
            self.build(c, sink, &mut s.memo, &mut s.stack)
        }
    }

    fn build<S: TermSink + ?Sized>(
        &self,
        root: u32,
        sink: &mut S,
        memo: &mut HashMap<u32, ExprId>,
        stack: &mut Vec<u32>,
    ) -> Result<ExprId, String> {
        let (recs, side) = (&self.recs, &self.side);
        // The sink's id for child `c`, if known.
        let done = |memo: &HashMap<u32, ExprId>, sink: &mut S, c: u32| {
            if c & ARENA != 0 {
                return Some(sink.shared_expr(ExprId(c & !ARENA)));
            }
            memo.get(&c).copied()
        };
        stack.push(root);
        while let Some(&top) = stack.last() {
            if done(memo, sink, top).is_some() {
                stack.pop();
                continue;
            }
            let n = decode_stored(side, recs[top as usize]);
            let (kids, k) = n.kids();
            let mut ready = true;
            for &c in &kids[..k] {
                if done(memo, sink, c).is_none() {
                    stack.push(c);
                    ready = false;
                }
            }
            if !ready {
                continue;
            }
            let mut ids = [ExprId(0); 3];
            for (&c, id) in kids[..k].iter().zip(&mut ids) {
                *id = done(memo, sink, c).expect("built");
            }
            let keep = sink.keeps_shared();
            let id = make(sink, n, ids, false, keep);
            memo.insert(top, id);
            stack.pop();
        }
        done(memo, sink, root).ok_or_else(|| "internal: unresolved value".into())
    }
}

/// Theorem values read from the records as they are while the read goes
/// on (see [`Builder::view`]): those of the declarations read so far. A
/// value is built as [`Stored`] builds it, but for the records the read
/// interns after the view was made, which it builds too (as their terms,
/// not as arena ids). A value that needs an arena id the view does not
/// have (one interned after it was made) is not built: an error.
pub(crate) struct Live {
    recs: crate::slab::AtomicView,
    side: Slab<u32>,
    roots: Vec<u32>,
    starts: Vec<u32>,
    /// The view's expressions: arena ids below this.
    exprs: u32,
    undo: std::sync::Arc<Undo>,
}

/// Why [`Live`] did not build a value.
pub(crate) const LIVE_LATER: &str = "the value needs terms read after the view";

thread_local! {
    static LIVE_SCRATCH: RefCell<Scratch> = RefCell::default();
}

impl Builder {
    /// The values of the declarations read so far, for other threads to
    /// build while the read goes on; arena ids below `exprs` are theirs.
    pub(super) fn view(&mut self, exprs: u32) -> Live {
        let n = self.from;
        self.viewed = n;
        self.hand_over_undo();
        Live {
            recs: self.recs.atomic_alias(n),
            side: self.side.alias(self.side.len()),
            roots: self.roots.clone(),
            starts: self.starts.clone(),
            exprs,
            undo: self.undo.get_or_insert_with(Default::default).clone(),
        }
    }

    /// Hand the records interned since the last call to the views (every
    /// so often while they are made: until then, the views cannot build
    /// values that need them).
    pub(super) fn hand_over_undo(&mut self) {
        if let Some(u) = &self.undo
            && !self.undo_new.is_empty()
        {
            u.0.write()
                .unwrap_or_else(|e| e.into_inner())
                .extend(self.undo_new.drain(..));
        }
    }

    /// No more views (they are gone): stop keeping records for them.
    pub(super) fn end_views(&mut self) {
        self.viewed = 0;
        self.undo = None;
        self.undo_new = Vec::new();
    }
}

impl LazyValues for Live {
    fn decode(&self, _env: &Env, k: u32, sink: &mut dyn TermSink) -> Result<ExprId, String> {
        self.decode_in(k, sink)
    }

    fn decode_store(
        &self,
        _env: &Env,
        k: u32,
        sink: &mut crate::check::store::Store<'_>,
    ) -> Result<ExprId, String> {
        self.decode_in(k, sink)
    }

    fn count(&self) -> usize {
        self.roots.len()
    }

    fn heap_bytes(&self) -> usize {
        (self.roots.capacity() + self.starts.capacity()) * 4
    }
}

impl Live {
    /// Record `x`, if the view has it: as it was if the reader has since
    /// interned it as a term the view has not got.
    #[inline(always)]
    fn rec(&self, x: u32) -> Result<u64, String> {
        if (x as usize) >= self.recs.len() {
            return Err("internal: a record past the view".into());
        }
        let r = self.recs.load(x as usize);
        if r & DONE == 0 || (r as u32) < self.exprs {
            return Ok(r);
        }
        self.undo
            .0
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .get(&x)
            .copied()
            .ok_or_else(|| LIVE_LATER.into())
    }

    /// The arena id of done record `r`, if the view has it.
    #[inline(always)]
    fn arena(&self, r: u64) -> Result<ExprId, String> {
        let id = r as u32;
        if id < self.exprs {
            Ok(ExprId(id))
        } else {
            Err(LIVE_LATER.into())
        }
    }

    fn decode_in<S: TermSink + ?Sized>(&self, k: u32, sink: &mut S) -> Result<ExprId, String> {
        let (Some(&root), Some(&start)) = (self.roots.get(k as usize), self.starts.get(k as usize))
        else {
            return Err("internal: no such lazy value".into());
        };
        LIVE_SCRATCH.with(|s| {
            let s = &mut *s.borrow_mut();
            s.memo.clear();
            s.stack.clear();
            s.own.clear();
            let keep = sink.keeps_shared();
            // As in `Stored::build_own`: the records of the value's own
            // declaration are taken as its own.
            for x in start..=root {
                let r = self.rec(x)?;
                let id = if r & DONE != 0 {
                    let a = self.arena(r)?;
                    if keep { a } else { sink.shared_expr(a) }
                } else if tag(r) == T_ALIAS {
                    let t = (r & ID_MASK) as u32;
                    if t >= start {
                        ExprId(s.own[(t - start) as usize])
                    } else {
                        self.build(t, sink, &mut s.memo, &mut s.stack)?
                    }
                } else {
                    let n = decode(&self.side, r);
                    let (kids, k) = n.kids();
                    let mut ids = [ExprId(0); 3];
                    for (&c, id) in kids[..k].iter().zip(&mut ids) {
                        *id = if c >= start {
                            ExprId(s.own[(c - start) as usize])
                        } else {
                            self.build(c, sink, &mut s.memo, &mut s.stack)?
                        };
                    }
                    make(sink, n, ids, true, keep)
                };
                s.own.push(id.0);
            }
            Ok(ExprId(*s.own.last().expect("the root")))
        })
    }

    /// Record `root` (of another declaration) in `sink`, hash-consed, as
    /// [`Stored::build`] does.
    fn build<S: TermSink + ?Sized>(
        &self,
        root: u32,
        sink: &mut S,
        memo: &mut HashMap<u32, ExprId>,
        stack: &mut Vec<u32>,
    ) -> Result<ExprId, String> {
        if let Some(&e) = memo.get(&root) {
            return Ok(e);
        }
        stack.clear();
        stack.push(root);
        while let Some(&top) = stack.last() {
            if memo.contains_key(&top) {
                stack.pop();
                continue;
            }
            let r = self.rec(top)?;
            let id = if r & DONE != 0 {
                let a = self.arena(r)?;
                if sink.keeps_shared() {
                    a
                } else {
                    sink.shared_expr(a)
                }
            } else if tag(r) == T_ALIAS {
                let t = (r & ID_MASK) as u32;
                match memo.get(&t) {
                    Some(&e) => e,
                    None => {
                        stack.push(t);
                        continue;
                    }
                }
            } else {
                let n = decode(&self.side, r);
                let (kids, k) = n.kids();
                let mut ready = true;
                for &c in &kids[..k] {
                    if !memo.contains_key(&c) {
                        stack.push(c);
                        ready = false;
                    }
                }
                if !ready {
                    continue;
                }
                let mut ids = [ExprId(0); 3];
                for (&c, id) in kids[..k].iter().zip(&mut ids) {
                    *id = memo[&c];
                }
                let keep = sink.keeps_shared();
                make(sink, n, ids, false, keep)
            };
            memo.insert(top, id);
            stack.pop();
        }
        Ok(memo[&root])
    }
}

#[cfg(test)]
mod tests {
    use crate::reader::{Options, read_file_with};

    thread_local! {
        /// Store applications as if arena ids did not fit their fields.
        pub(super) static WIDE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    }

    /// The kernel tests' exports and the prefix of `Init`'s (if `xz` can
    /// unpack it), read with lazy proofs (stored either way, on one
    /// thread or several), give the environment that reading them eagerly
    /// gives.
    #[test]
    fn lazy_values_match_eager() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
        let mut paths: Vec<_> = std::fs::read_dir(root.join("tests/kernel/exports"))
            .expect("exports")
            .map(|e| e.expect("entry").path())
            .collect();
        let prefix =
            std::env::temp_dir().join(format!("init-prefix-{}.ndjson", std::process::id()));
        let unpacked = std::fs::File::create(&prefix).ok().is_some_and(|f| {
            std::process::Command::new("xz")
                .arg("-dc")
                .arg(root.join("bench/arena/pgo/init-prefix.ndjson.xz"))
                .stdout(f)
                .status()
                .is_ok_and(|s| s.success())
        });
        if unpacked {
            paths.push(prefix.clone());
        } else {
            eprintln!("xz cannot unpack the Init prefix: checking the small exports only");
        }
        let mut lazy_values = 0;
        for path in &paths {
            let Ok((eager, _)) = read_file_with(path, &Options::default()) else {
                continue;
            };
            for (wide, threads) in [(false, 1), (true, 1), (false, 4), (true, 4)] {
                WIDE.set(wide);
                let opts = Options {
                    lazy_proofs: true,
                    threads,
                };
                let (lazy, _) = read_file_with(path, &opts).expect("reads lazily too");
                WIDE.set(false);
                lazy_values += lazy.lazy_values();
                let d = crate::compare::compare(&eager, &lazy);
                assert!(
                    d.only_a.is_empty() && d.only_b.is_empty() && d.differ.is_empty(),
                    "{}, wide {wide}, {threads} threads: {:?}",
                    path.display(),
                    &d.differ[..d.differ.len().min(5)]
                );
            }
        }
        let _ = std::fs::remove_file(&prefix);
        assert!(lazy_values > 0, "some values are lazy");
    }

    /// Views made while reading (see [`crate::reader::Views`]) hold the
    /// declarations read so far as reading them eagerly does, values that
    /// a view cannot build aside.
    #[test]
    fn views_match_eager() {
        use crate::reader::{Views, read_file_viewed};
        struct Collect<'a> {
            eager: &'a crate::env::Env,
            views: std::sync::Mutex<Vec<crate::env::Env>>,
            checked: std::sync::atomic::AtomicUsize,
        }
        impl Views for Collect<'_> {
            fn wanted(&self, _: u64, _: u64) -> bool {
                true
            }
            fn publish(&self, env: crate::env::Env) {
                self.views.lock().unwrap().push(env);
            }
            fn wanted_last(&self) -> bool {
                true
            }
            fn drain(&self) {
                for mut v in self.views.lock().unwrap().drain(..) {
                    let t = v.names.new_index().expect("distinct names");
                    v.names.set_index(t);
                    v.exprs.index(1).expect("distinct expressions");
                    // (`compare` builds the second one's lazy values.)
                    // Values that need terms read after the view are
                    // not compared (the view reports them as later).
                    let mut later = std::collections::HashSet::new();
                    for d in &v.decls {
                        let mut st = crate::check::store::Store::new(&v);
                        if let Err(e) = v.value_into_store(d, &mut st) {
                            assert_eq!(e, super::LIVE_LATER);
                            later.insert(v.names.display(d.name).to_string());
                        }
                    }
                    let d = crate::compare::compare(self.eager, &v);
                    let differ: Vec<_> = d
                        .differ
                        .iter()
                        .filter(|(n, why)| !(*why == "value" && later.contains(n)))
                        .collect();
                    assert!(
                        d.only_b.is_empty() && differ.is_empty() && d.common == v.decls.len(),
                        "{} of {} declarations: {:?} {:?}",
                        v.decls.len(),
                        self.eager.decls.len(),
                        &d.only_b[..d.only_b.len().min(5)],
                        &differ[..differ.len().min(5)]
                    );
                    self.checked
                        .fetch_add(d.common - later.len(), std::sync::atomic::Ordering::Relaxed);
                }
            }
        }
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
        let prefix =
            std::env::temp_dir().join(format!("init-prefix-views-{}.ndjson", std::process::id()));
        let unpacked = std::fs::File::create(&prefix).ok().is_some_and(|f| {
            std::process::Command::new("xz")
                .arg("-dc")
                .arg(root.join("bench/arena/pgo/init-prefix.ndjson.xz"))
                .stdout(f)
                .status()
                .is_ok_and(|s| s.success())
        });
        if !unpacked {
            eprintln!("xz cannot unpack the Init prefix: skipped");
            return;
        }
        let (eager, _) = read_file_with(&prefix, &Options::default()).expect("reads");
        let c = Collect {
            eager: &eager,
            views: Default::default(),
            checked: Default::default(),
        };
        let opts = Options {
            lazy_proofs: true,
            threads: 4,
        };
        let (env, _, same) = read_file_viewed(&prefix, &opts, &c).expect("reads with views");
        let _ = std::fs::remove_file(&prefix);
        assert!(same);
        assert_eq!(env.decls.len(), eager.decls.len());
        assert!(c.checked.into_inner() > 0, "some views");
    }

    /// With `NITROLEAN_EXPORT` set to an export file: reading it with lazy
    /// proofs gives the same environment as reading it eagerly (every
    /// lazily built value included).
    #[test]
    fn lazy_export_matches_eager() {
        let Some(path) = std::env::var_os("NITROLEAN_EXPORT") else {
            return;
        };
        let path = std::path::Path::new(&path);
        let (eager, _) = read_file_with(path, &Options::default()).expect("reads");
        let lazy_opts = Options {
            lazy_proofs: true,
            ..Options::default()
        };
        let (lazy, _) = read_file_with(path, &lazy_opts).expect("reads");
        assert!(lazy.lazy_values() > 0);
        let d = crate::compare::compare(&eager, &lazy);
        assert!(
            d.only_a.is_empty() && d.only_b.is_empty(),
            "same declarations"
        );
        assert!(
            d.differ.is_empty(),
            "differences: {:?}",
            &d.differ[..d.differ.len().min(5)]
        );
        assert_eq!(d.common, eager.decls.len());
    }
}
