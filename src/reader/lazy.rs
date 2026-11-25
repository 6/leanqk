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
    let id = if append {
        env.exprs.append_compound(node)?
    } else {
        env.exprs.intern(node, &env.levels)?.0
    };
    // (Checkers' own ids start at 2^31.)
    if id.0 >= 1 << 31 {
        return Err(Fail::from(Overflow("too many expressions")));
    }
    Ok(id.0)
}

/// The reader's side of lazy proofs: a record per expression id.
#[derive(Default)]
pub(super) struct Builder {
    recs: Vec<u64>,
    side: Vec<u32>,
    /// Records from here on came after the last declaration line.
    from: usize,
    /// Per lazy value, its root's export id.
    roots: Vec<u32>,
    stack: Vec<u32>,
    /// For [`Builder::exprs`] (see `run`).
    digits: (u32, u64),
}

impl Builder {
    /// A builder for an export of about `size` bytes.
    pub(super) fn with_capacity(size: u64) -> Self {
        let mut b = Builder {
            digits: (1, 10),
            ..Builder::default()
        };
        // About one expression per 56 bytes of a real export, and a side
        // record (3 words) per 8 of them; the space is only reserved, so
        // a smaller file costs nothing.
        b.recs.reserve((size / 56).min(MAX_IDS) as usize);
        b.side.reserve((size / 150).min(u32::MAX as u64) as usize);
        b
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
        self.recs.push(T_APP << TAG | f << ID_BITS | a);
        true
    }

    /// The application and binder lines at the start of `s` (see `run`),
    /// with the names' ids mapped by `names`: how many bytes and lines it
    /// took.
    #[inline(never)]
    pub(super) fn exprs(&mut self, s: &[u8], names: &IdMap) -> (usize, u64) {
        let e = self.recs.len() as u64;
        // Room for as many lines as fit in `s`, at 32 bytes or more each.
        if e + s.len() as u64 / 32 >= MAX_IDS {
            return (0, 0);
        }
        // Local vectors, which the loop can keep in registers.
        let mut out = Out {
            recs: std::mem::take(&mut self.recs),
            side: std::mem::take(&mut self.side),
            names,
        };
        let r = super::run::all_exprs(s, e, &mut self.digits, &mut out);
        self.recs = out.recs;
        self.side = out.side;
        r
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
        self.with_side(T_LET, nondep as u64, &f)
    }

    /// A projection record; as [`Builder::app`].
    pub(super) fn proj(&mut self, id: u64, s: NameId, i: u32, e: u64) -> bool {
        if !self.next(id) || e >= id {
            return false;
        }
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
    /// find), and a pass up interns them.
    fn promote_recent(&mut self, env: &mut Env, append: bool, i: usize) -> R<ExprId> {
        let from = self.from;
        self.recs[i] |= NEEDED;
        // Records marked and not yet passed.
        let mut left = 1usize;
        let mut j = i;
        loop {
            let r = self.recs[j];
            if r & NEEDED != 0 {
                left -= 1;
                let (kids, k) = if tag(r) == T_APP {
                    (
                        [(r >> ID_BITS & ID_MASK) as u32, (r & ID_MASK) as u32, 0],
                        2,
                    )
                } else {
                    decode(&self.side, r).kids()
                };
                for &c in &kids[..k] {
                    let c = self.real(c) as usize;
                    if c >= from && self.recs[c] & (DONE | NEEDED) == 0 {
                        self.recs[c] |= NEEDED;
                        left += 1;
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
            if tag(r) == T_APP {
                let f = self.known_or_old(env, append, (r >> ID_BITS & ID_MASK) as u32)?;
                let a = self.known_or_old(env, append, (r & ID_MASK) as u32)?;
                let id = add_node(env, append, ExprNode::App(ExprId(f), ExprId(a)))?;
                self.recs[x] = DONE | id as u64;
                continue;
            }
            let n = decode(&self.side, r);
            let (kids, k) = n.kids();
            let mut ids = [0u32; 3];
            for (&c, id) in kids[..k].iter().zip(&mut ids) {
                *id = self.known_or_old(env, append, c)?;
            }
            self.recs[x] = DONE | add(env, append, n, ids)? as u64;
        }
        Ok(ExprId(self.recs[i] as u32))
    }

    /// The arena id of `c`, interned by now if it is recent.
    #[inline(always)]
    fn known_or_old(&mut self, env: &mut Env, append: bool, c: u32) -> R<u32> {
        match self.known(c) {
            Some(v) => Ok(v),
            None => Ok(self.promote_old(env, append, self.real(c))?.0),
        }
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
                let n = decode(&self.side, r);
                let (kids, k) = n.kids();
                let mut ready = true;
                let mut ids = [0u32; 3];
                for (&c, id) in kids[..k].iter().zip(&mut ids) {
                    let c = self.real(c);
                    let r = self.recs[c as usize];
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
                self.recs[top as usize] = DONE | add(env, append, n, ids)? as u64;
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

    /// The source of the lazy values, once the read is done.
    pub(super) fn finish(mut self) -> Option<Box<dyn LazyValues>> {
        if self.roots.is_empty() {
            return None;
        }
        // Interned records stay where they are, marked `DONE`; building
        // a value takes their arena ids from there.
        self.recs.shrink_to_fit();
        self.side.shrink_to_fit();
        self.roots.shrink_to_fit();
        Some(Box::new(Stored {
            recs: self.recs,
            side: self.side,
            roots: self.roots,
        }))
    }
}

/// Where [`Builder::exprs`] puts records.
struct Out<'a> {
    recs: Vec<u64>,
    side: Vec<u32>,
    names: &'a IdMap,
}

impl super::run::Records for Out<'_> {
    #[inline(always)]
    fn app(&mut self, id: u64, f: u64, a: u64) -> bool {
        if f >= id || a >= id {
            return false;
        }
        self.recs.push(T_APP << TAG | f << ID_BITS | a);
        true
    }

    #[inline(always)]
    fn binder(&mut self, id: u64, pi: bool, bi: BinderInfo, name: u64, ty: u64, body: u64) -> bool {
        let Some(name) = self.names.get(name) else {
            return false;
        };
        let o = self.side.len();
        if ty >= id || body >= id || o > u32::MAX as usize - 4 {
            return false;
        }
        self.side.extend_from_slice(&[name, ty as u32, body as u32]);
        let t = if pi { T_PI } else { T_LAM };
        self.recs.push(t << TAG | bi_bits(bi) << 32 | o as u64);
        true
    }
}

/// Theorem values of an export: the records, by expression id.
struct Stored {
    recs: Vec<u64>,
    side: Vec<u32>,
    roots: Vec<u32>,
}

thread_local! {
    /// Each thread's memo (expression id to the sink's id) and stack.
    static SCRATCH: RefCell<(HashMap<u32, ExprId>, Vec<u32>)> = RefCell::default();
}

impl LazyValues for Stored {
    fn decode(&self, _env: &Env, k: u32, sink: &mut dyn TermSink) -> Result<ExprId, String> {
        let &root = self
            .roots
            .get(k as usize)
            .ok_or("internal: no such lazy value")?;
        SCRATCH.with(|s| {
            let (memo, stack) = &mut *s.borrow_mut();
            memo.clear();
            stack.clear();
            self.build(root, sink, memo, stack)
        })
    }

    fn count(&self) -> usize {
        self.roots.len()
    }

    fn heap_bytes(&self) -> usize {
        self.recs.capacity() * 8 + self.side.capacity() * 4 + self.roots.capacity() * 4
    }
}

impl Stored {
    fn build(
        &self,
        root: u32,
        sink: &mut dyn TermSink,
        memo: &mut HashMap<u32, ExprId>,
        stack: &mut Vec<u32>,
    ) -> Result<ExprId, String> {
        // The sink's id for expression `i`, if known.
        let (recs, side) = (&self.recs, &self.side);
        let real = |i: u32| {
            let r = recs[i as usize];
            if r & DONE == 0 && tag(r) == T_ALIAS {
                (r & ID_MASK) as u32
            } else {
                i
            }
        };
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
            let mut e = |c: u32| done(memo, sink, c).expect("built");
            let id = match n {
                Node::App(f, a) => {
                    let (f, a) = (e(f), e(a));
                    sink.expr(ExprNode::App(f, a))
                }
                Node::Bind {
                    pi,
                    bi,
                    name,
                    ty,
                    body,
                } => {
                    let (t, b) = (e(ty), e(body));
                    let name = sink.shared_name(name);
                    sink.expr(if pi {
                        ExprNode::Pi(bi, name, t, b)
                    } else {
                        ExprNode::Lam(bi, name, t, b)
                    })
                }
                Node::Let {
                    name,
                    ty,
                    value,
                    body,
                    nondep,
                } => {
                    let (t, v, b) = (e(ty), e(value), e(body));
                    let name = sink.shared_name(name);
                    sink.let_in(
                        LetBinder {
                            name,
                            ty: t,
                            value: v,
                            nondep,
                        },
                        b,
                    )
                }
                Node::Proj(s, i, x) => {
                    let x = e(x);
                    let s = sink.shared_name(s);
                    sink.expr(ExprNode::Proj(s, i, x))
                }
            };
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
