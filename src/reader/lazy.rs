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
    recs: Vec<u64>,
    side: Vec<u32>,
    /// Records from here on came after the last declaration line.
    from: usize,
    /// Per lazy value, its root's export id, and the first record of its
    /// declaration's lines (or the root, if that is older).
    roots: Vec<u32>,
    starts: Vec<u32>,
    /// Lazy values whose root is a record of an earlier declaration.
    old_roots: Vec<u32>,
    /// Where each declaration's records start (but the last's).
    bounds: Vec<u32>,
    stack: Vec<u32>,
    /// For [`Builder::exprs`] (see `run`).
    ids: super::run::Ids,
    /// Its batches of records and side records.
    batch: Vec<u64>,
    side_batch: Vec<u32>,
    /// Records of earlier declarations that records use and that are not
    /// interned (yet), as records are added: what
    /// [`Builder::promote_shared`] interns. Unless `scan_at_end`, when it
    /// finds them in one pass at the end instead (the records read ahead
    /// on other threads are added without looking).
    cands: Vec<u32>,
    scan_at_end: bool,
    /// Where [`Builder::exprs`] puts records before they join `recs`.
    fresh: Vec<u64>,
}

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
        let mut b = Builder::default();
        // About one expression per 56 bytes of a real export, and a side
        // record (3 words) per 8 of them; the space is only reserved, so
        // a smaller file costs nothing.
        b.recs.reserve((size / 56).min(MAX_IDS) as usize);
        b.side.reserve((size / 120).min(u32::MAX as u64) as usize);
        b
    }

    /// Have [`Builder::promote_shared`] scan all records at the end (for a
    /// read that adds records without [`note_old`]).
    pub(super) fn scan_at_end(&mut self) {
        self.scan_at_end = true;
    }

    /// The first record of the current declaration, for [`note_old`] (0,
    /// so that it notes nothing, when scanning at the end).
    #[inline(always)]
    fn note_from(&self) -> usize {
        if self.scan_at_end { 0 } else { self.from }
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
        let mut out = Out {
            batch: (&mut self.batch[..]).try_into().expect("a batch"),
            side_batch: (&mut self.side_batch[..]).try_into().expect("a batch"),
            sn: 0,
            o: self.side.len(),
            recs: &mut self.fresh,
            side: &mut self.side,
            names: names.min(u32::MAX as u64),
            old: &self.recs[..from],
            cands: &mut self.cands,
            leaf: Some(leaf),
        };
        let res = super::run::all_exprs(s, e, &mut self.ids, &mut out);
        self.recs.extend_from_slice(&self.fresh);
        self.fresh.clear();
        res
    }

    /// The next expression id.
    pub(super) fn next_id(&self) -> u64 {
        self.recs.len() as u64
    }

    /// Records that [`Runs::take`] read ahead, starting at the next
    /// expression id (`side` being their side records, which they point
    /// into from `side_from` on), if their names are among the first
    /// `names` and the tables have room: whether it added them.
    pub(super) fn append_run(
        &mut self,
        recs: &[u64],
        side: &[u32],
        side_from: usize,
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
    batch: Vec<u64>,
    side_batch: Vec<u32>,
    ids: super::run::Ids,
}

impl Runs {
    /// The run at the start of `s`, its first id being `e`: how many bytes
    /// and lines it took, and the largest name id its binders use.
    pub(super) fn take(&mut self, s: &[u8], e: u64) -> (usize, u64, u64) {
        if e + s.len() as u64 / 32 >= MAX_IDS {
            return (0, 0, 0);
        }
        if self.batch.is_empty() {
            self.batch = vec![0; BATCH];
            self.side_batch = vec![0; 3 * BATCH];
        }
        let side_from = self.side.len();
        let mut out = Out {
            batch: (&mut self.batch[..]).try_into().expect("a batch"),
            side_batch: (&mut self.side_batch[..]).try_into().expect("a batch"),
            sn: 0,
            o: side_from,
            recs: &mut self.recs,
            side: &mut self.side,
            names: u32::MAX as u64,
            old: &[],
            cands: &mut Vec::new(),
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
        recs[i] |= NEEDED;
        // Records marked and not yet passed.
        let mut left = 1usize;
        // Mark record `c` if it is recent and not yet marked or done:
        // how many it marked.
        let mark = |recs: &mut [u64], c: u32| -> usize {
            let c = c as usize;
            if c >= from && recs[c] & (DONE | NEEDED) == 0 {
                recs[c] |= NEEDED;
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
                        recs[j] = r & !NEEDED;
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
            self.recs[x] = DONE | id as u64;
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
                self.recs[top as usize] = DONE | id as u64;
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
        if self.from != self.recs.len() {
            self.bounds.push(self.from as u32);
        }
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
                self.recs[x] = self.recs[(r & ID_MASK) as usize];
                continue;
            }
            let n = decode(&self.side, r);
            let (kids, k) = n.kids();
            let mut ids = [0u32; 3];
            for (&c, id) in kids[..k].iter().zip(&mut ids) {
                *id = self.recs[c as usize] as u32;
            }
            self.recs[x] = DONE | add(env, append, n, ids)? as u64;
        }
        let ids: Vec<u32> = self.recs.iter().map(|&r| r as u32).collect();
        let roots = self.roots.iter().map(|&i| ids[i as usize]).collect();
        Ok((ids, roots))
    }

    /// Intern the records that a later declaration's records use (and
    /// the roots of values older than their declarations), so that each
    /// record left is used by its own declaration's value alone: built
    /// once here, not again for every value that uses it.
    fn promote_shared(&mut self, env: &mut Env, append: bool, threads: usize) -> R<()> {
        if !self.scan_at_end {
            // Noted as the records were added, in order.
            for c in std::mem::take(&mut self.cands) {
                let c = self.real(c);
                if self.recs[c as usize] & DONE == 0 {
                    self.promote_old(env, append, c)?;
                }
            }
            return self.promote_old_roots(env, append);
        }
        self.bounds.push(self.from as u32);
        let bounds = std::mem::take(&mut self.bounds);
        // The records to intern, found on `threads` threads (a group of
        // declarations each at a time), then interned in order.
        let decls = bounds.len().saturating_sub(1);
        const GROUP: usize = 4096;
        let groups = decls.div_ceil(GROUP);
        let found: Vec<std::sync::Mutex<Vec<u32>>> = (0..groups)
            .map(|_| std::sync::Mutex::new(Vec::new()))
            .collect();
        let next = std::sync::atomic::AtomicUsize::new(0);
        let (recs, side) = (&self.recs, &self.side);
        let scan = || {
            let mut out = Vec::new();
            loop {
                let g = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                if g >= groups {
                    return;
                }
                let hi = ((g + 1) * GROUP).min(decls);
                for w in bounds[g * GROUP..=hi].windows(2) {
                    let (lo, hi) = (w[0], w[1]);
                    for x in lo..hi {
                        let r = recs[x as usize];
                        if r & DONE != 0 || tag(r) == T_ALIAS {
                            continue;
                        }
                        let (kids, k) = decode(side, r).kids();
                        for &c in &kids[..k] {
                            if c < lo {
                                let r = recs[c as usize];
                                let c = if r & DONE == 0 && tag(r) == T_ALIAS {
                                    (r & ID_MASK) as u32
                                } else {
                                    c
                                };
                                if recs[c as usize] & DONE == 0 {
                                    out.push(c);
                                }
                            }
                        }
                    }
                }
                *found[g].lock().expect("group") = std::mem::take(&mut out);
            }
        };
        let threads = threads.clamp(1, groups.max(1));
        if threads == 1 {
            scan();
        } else {
            std::thread::scope(|s| {
                for _ in 0..threads {
                    s.spawn(scan);
                }
            });
        }
        for g in found {
            for c in g.into_inner().expect("group") {
                if self.recs[c as usize] & DONE == 0 {
                    self.promote_old(env, append, c)?;
                }
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

    /// The source of the lazy values, once the read is done.
    pub(super) fn finish(
        mut self,
        env: &mut Env,
        append: bool,
        threads: usize,
    ) -> R<Option<Box<dyn LazyValues>>> {
        if self.roots.is_empty() {
            return Ok(None);
        }
        self.promote_shared(env, append, threads)?;
        // Interned records stay where they are, marked `DONE`; building
        // a value takes their arena ids from there.
        self.recs.shrink_to_fit();
        self.side.shrink_to_fit();
        self.roots.shrink_to_fit();
        self.starts.shrink_to_fit();
        Ok(Some(Box::new(Stored {
            recs: self.recs,
            side: self.side,
            roots: self.roots,
            starts: self.starts,
        })))
    }
}

/// Node `n` in `sink`, its children being `ids` (in [`Node::kids`]'s
/// order); `owned` if no other value or interned term uses it (see
/// [`TermSink::expr_owned`]).
fn make(sink: &mut dyn TermSink, n: Node, ids: [ExprId; 3], owned: bool) -> ExprId {
    let expr = |sink: &mut dyn TermSink, node| {
        if owned {
            sink.expr_owned(node)
        } else {
            sink.expr(node)
        }
    };
    match n {
        Node::App(..) => expr(sink, ExprNode::App(ids[0], ids[1])),
        Node::Bind { pi, bi, name, .. } => {
            let name = sink.shared_name(name);
            let (t, b) = (ids[0], ids[1]);
            let node = if pi {
                ExprNode::Pi(bi, name, t, b)
            } else {
                ExprNode::Lam(bi, name, t, b)
            };
            expr(sink, node)
        }
        Node::Let { name, nondep, .. } => {
            let name = sink.shared_name(name);
            let binder = LetBinder {
                name,
                ty: ids[0],
                value: ids[1],
                nondep,
            };
            sink.let_in(binder, ids[2])
        }
        Node::Proj(s, i, _) => {
            let s = sink.shared_name(s);
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
struct Out<'a> {
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
    cands: &'a mut Vec<u32>,
    /// For constant lines (see [`Builder::exprs`]).
    leaf: Option<&'a mut LeafLine<'a>>,
}

impl super::run::Records for Out<'_> {
    #[inline(always)]
    fn app(&mut self, id: u64, f: u64, a: u64) -> bool {
        if f >= id || a >= id {
            return false;
        }
        note_old(self.old, self.old.len(), f, self.cands);
        note_old(self.old, self.old.len(), a, self.cands);
        self.batch[id as usize % BATCH] = T_APP << TAG | f << ID_BITS | a;
        true
    }

    #[inline(always)]
    fn binder(&mut self, id: u64, pi: bool, bi: BinderInfo, name: u64, ty: u64, body: u64) -> bool {
        let o = self.o;
        if name >= self.names || ty >= id || body >= id || o > u32::MAX as usize - 4 {
            return false;
        }
        note_old(self.old, self.old.len(), ty, self.cands);
        note_old(self.old, self.old.len(), body, self.cands);
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

/// Theorem values of an export: the records, by expression id.
struct Stored {
    recs: Vec<u64>,
    side: Vec<u32>,
    roots: Vec<u32>,
    starts: Vec<u32>,
}

/// Each thread's working space for [`Stored::decode`].
#[derive(Default)]
struct Scratch {
    /// Per record of the value's own range, from its start: [`UNSEEN`],
    /// [`WANTED`] or the sink's id.
    own: Vec<u32>,
    /// Older records (from other declarations): the sink's ids, and the
    /// stack that builds them.
    memo: HashMap<u32, ExprId>,
    stack: Vec<u32>,
}

/// Marks in [`Scratch::own`] (never ids: those are below [`LAZY_BASE`]).
const UNSEEN: u32 = u32::MAX;
const WANTED: u32 = u32::MAX - 1;

thread_local! {
    static SCRATCH: RefCell<Scratch> = RefCell::default();
}

impl LazyValues for Stored {
    fn decode(&self, _env: &Env, k: u32, sink: &mut dyn TermSink) -> Result<ExprId, String> {
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

    fn count(&self) -> usize {
        self.roots.len()
    }

    fn heap_bytes(&self) -> usize {
        self.recs.capacity() * 8
            + self.side.capacity() * 4
            + (self.roots.capacity() + self.starts.capacity()) * 4
    }
}

impl Stored {
    /// The record an id stands for (an alias's target).
    #[inline(always)]
    fn real(&self, i: u32) -> u32 {
        let r = self.recs[i as usize];
        if r & DONE == 0 && tag(r) == T_ALIAS {
            (r & ID_MASK) as u32
        } else {
            i
        }
    }

    /// Value `root` (a real record), whose own records are those from
    /// `start` on: in two passes over them, as the reader adds recent
    /// records (see `Builder::promote_recent`). One down marks the records
    /// it needs, one up builds them in order (children first). Older
    /// records are built by [`Stored::build`].
    fn build_own(
        &self,
        root: u32,
        start: u32,
        sink: &mut dyn TermSink,
        s: &mut Scratch,
    ) -> Result<ExprId, String> {
        let recs = &self.recs;
        if recs[root as usize] & DONE != 0 {
            return Ok(sink.shared_expr(ExprId(recs[root as usize] as u32)));
        }
        let n = (root - start) as usize + 1;
        s.own.clear();
        s.own.resize(n, UNSEEN);
        s.own[n - 1] = WANTED;
        let mut left = 1usize;
        let mut j = root;
        loop {
            if s.own[(j - start) as usize] == WANTED {
                left -= 1;
                let (kids, k) = decode(&self.side, recs[j as usize]).kids();
                for &c in &kids[..k] {
                    let c = self.real(c);
                    if c >= start && recs[c as usize] & DONE == 0 {
                        let m = &mut s.own[(c - start) as usize];
                        if *m == UNSEEN {
                            *m = WANTED;
                            left += 1;
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
        for x in j..=root {
            if s.own[(x - start) as usize] != WANTED {
                continue;
            }
            let n = decode(&self.side, recs[x as usize]);
            let (kids, k) = n.kids();
            let mut ids = [ExprId(0); 3];
            for (&c, id) in kids[..k].iter().zip(&mut ids) {
                let c = self.real(c);
                let r = recs[c as usize];
                *id = if r & DONE != 0 {
                    sink.shared_expr(ExprId(r as u32))
                } else if c >= start {
                    ExprId(s.own[(c - start) as usize])
                } else {
                    self.build(c, sink, &mut s.memo, &mut s.stack)?
                };
            }
            // Records of the value's own declaration are taken as used by
            // it alone (one that a later value uses too is built there
            // again, by `build`, hash-consed).
            s.own[(x - start) as usize] = make(sink, n, ids, true).0;
        }
        Ok(ExprId(s.own[n - 1]))
    }

    fn build(
        &self,
        root: u32,
        sink: &mut dyn TermSink,
        memo: &mut HashMap<u32, ExprId>,
        stack: &mut Vec<u32>,
    ) -> Result<ExprId, String> {
        let (recs, side) = (&self.recs, &self.side);
        let real = |i: u32| self.real(i);
        // The sink's id for expression `i`, if known.
        let done = |memo: &HashMap<u32, ExprId>, sink: &mut dyn TermSink, i: u32| {
            let r = recs[real(i) as usize];
            if r & DONE != 0 {
                return Some(sink.shared_expr(ExprId(r as u32)));
            }
            memo.get(&real(i)).copied()
        };
        stack.push(root);
        while let Some(&top) = stack.last() {
            if done(memo, sink, top).is_some() {
                stack.pop();
                continue;
            }
            let top = real(top);
            let n = decode(side, recs[top as usize]);
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
            let id = make(sink, n, ids, false);
            memo.insert(top, id);
            stack.pop();
        }
        done(memo, sink, root).ok_or_else(|| "internal: unresolved value".into())
    }
}

#[cfg(test)]
mod tests {
    use crate::reader::{Options, read_file_with};

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
