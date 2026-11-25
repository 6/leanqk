//! Theorem values left unbuilt when reading an export.
//!
//! An export lists every term once, children first, and a theorem's proof
//! right before its declaration line. With lazy proofs on, the reader
//! interns leaves (`bvar`, `sort`, `const`, literals) at once, but keeps
//! the other expression records of the current declaration *pending*.
//! At the declaration line, the terms its eager fields need (types,
//! definition values, recursor rules) are interned from there; what is
//! left (a theorem's proof, mostly) moves to a compact store of words
//! that is never hash-consed. A later declaration that needs a stored
//! term interns it then ("promotes" it). A theorem's value that is not in
//! the arena is a placeholder ([`crate::env::LAZY_BASE`]) built on
//! demand by [`crate::env::Env::value_into`].
//!
//! References are `u32`s: an arena id below [`PEND`], a pending record
//! (`PEND | index`), or a stored one (`STORED | word offset`).

use std::cell::RefCell;

use hashbrown::HashMap;

use super::{Fail, R, bad};
use crate::env::{Env, LazyValues, TermSink};
use crate::expr::{BinderInfo, ExprId, ExprNode, LetBinder};
use crate::idmap::IdMap;
use crate::name::NameId;
use crate::strings::Overflow;

/// A reference to a pending record.
pub(super) const PEND: u32 = 1 << 30;
/// A reference to a stored record.
pub(super) const STORED: u32 = 2 << 30;
const KIND: u32 = 3 << 30;
const NONE: u32 = u32::MAX;
/// A pending record's arena id while [`Builder::promote`] has found it
/// needed and not yet interned it.
const NEEDED: u32 = u32::MAX - 1;

/// A compound expression record, with references as above.
#[derive(Clone, Copy)]
pub(super) enum Node {
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

    fn map(self, mut f: impl FnMut(u32) -> u32) -> Node {
        match self {
            Node::App(a, b) => Node::App(f(a), f(b)),
            Node::Bind {
                pi,
                bi,
                name,
                ty,
                body,
            } => Node::Bind {
                pi,
                bi,
                name,
                ty: f(ty),
                body: f(body),
            },
            Node::Let {
                name,
                ty,
                value,
                body,
                nondep,
            } => Node::Let {
                name,
                ty: f(ty),
                value: f(value),
                body: f(body),
                nondep,
            },
            Node::Proj(n, i, e) => Node::Proj(n, i, f(e)),
        }
    }
}

// Word layout of a stored record: a head word (tag in the low 3 bits,
// then binder info or the let's `nondep`), then the fields.
const T_APP: u32 = 0;
const T_LAM: u32 = 1;
const T_PI: u32 = 2;
const T_LET: u32 = 3;
const T_PROJ: u32 = 4;
/// Set in the head word of a stored record once it is interned; its
/// arena id then replaces the record's second word.
const DONE: u32 = 1 << 31;

fn bi_bits(bi: BinderInfo) -> u32 {
    match bi {
        BinderInfo::Default => 0,
        BinderInfo::Implicit => 1,
        BinderInfo::StrictImplicit => 2,
        BinderInfo::InstImplicit => 3,
    }
}

fn bits_bi(b: u32) -> BinderInfo {
    match b & 3 {
        0 => BinderInfo::Default,
        1 => BinderInfo::Implicit,
        2 => BinderInfo::StrictImplicit,
        _ => BinderInfo::InstImplicit,
    }
}

#[inline(always)]
fn push_node(words: &mut Vec<u32>, n: Node) {
    match n {
        Node::App(f, a) => words.extend([T_APP, f, a]),
        Node::Bind {
            pi,
            bi,
            name,
            ty,
            body,
        } => words.extend([
            if pi { T_PI } else { T_LAM } | bi_bits(bi) << 3,
            name.0,
            ty,
            body,
        ]),
        Node::Let {
            name,
            ty,
            value,
            body,
            nondep,
        } => words.extend([T_LET | (nondep as u32) << 3, name.0, ty, value, body]),
        Node::Proj(n, i, e) => words.extend([T_PROJ, n.0, i, e]),
    }
}

fn read_node(words: &[u32], off: u32) -> Node {
    let w = &words[off as usize..];
    match w[0] & 7 {
        T_APP => Node::App(w[1], w[2]),
        T_LAM | T_PI => Node::Bind {
            pi: w[0] & 7 == T_PI,
            bi: bits_bi(w[0] >> 3),
            name: NameId(w[1]),
            ty: w[2],
            body: w[3],
        },
        T_LET => Node::Let {
            name: NameId(w[1]),
            ty: w[2],
            value: w[3],
            body: w[4],
            nondep: w[0] >> 3 & 1 != 0,
        },
        _ => Node::Proj(NameId(w[1]), w[2], w[3]),
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
    let id = if append {
        env.exprs.append(node, &env.levels)?
    } else {
        env.exprs.intern(node, &env.levels)?.0
    };
    if id.0 >= PEND {
        return Err(Fail::from(Overflow("too many expressions")));
    }
    Ok(id.0)
}

/// The reader's side of lazy proofs.
#[derive(Default)]
pub(super) struct Builder {
    words: Vec<u32>,
    /// The records since the last declaration line: export id, record.
    pending: Vec<(u64, Node)>,
    /// The arena id of each pending record, once interned.
    pend_ids: Vec<u32>,
    /// `mdata` records among them: export id, the reference it stands for.
    aliases: Vec<(u64, u32)>,
    /// Per lazy value, its root reference (pending until the flush).
    roots: Vec<u32>,
    /// Roots added since the last flush start here.
    roots_from: usize,
    stack: Vec<u32>,
}

impl Builder {
    /// A builder for an export of about `size` bytes.
    pub(super) fn with_capacity(size: u64) -> Self {
        let mut b = Builder::default();
        // About two thirds of a real export's lines are compound
        // expressions left stored, at about 3.5 words each; the space is
        // only reserved, so a smaller file costs nothing.
        b.words.reserve((size / 24).min(PEND as u64) as usize);
        b
    }

    /// Add a pending record; its reference.
    #[inline(always)]
    pub(super) fn pend(&mut self, id: u64, n: Node) -> R<u32> {
        let i = self.pending.len() as u32;
        if i >= PEND {
            return bad("too many expressions before one declaration");
        }
        self.pending.push((id, n));
        self.pend_ids.push(NONE);
        Ok(PEND | i)
    }

    pub(super) fn alias(&mut self, id: u64, r: u32) {
        self.aliases.push((id, r));
    }

    /// The arena id of reference `r`, if it is interned.
    fn known(&self, r: u32) -> Option<u32> {
        match r & KIND {
            0 => Some(r),
            PEND => {
                let v = self.pend_ids[(r & !KIND) as usize];
                (v != NONE).then_some(v)
            }
            _ => {
                let off = (r & !KIND) as usize;
                (self.words[off] & DONE != 0).then(|| self.words[off + 1])
            }
        }
    }

    fn node(&self, r: u32) -> Node {
        if r & KIND == PEND {
            self.pending[(r & !KIND) as usize].1
        } else {
            read_node(&self.words, r & !KIND)
        }
    }

    /// Intern the term `r` refers to (and what it needs) in `env`.
    pub(super) fn promote(&mut self, env: &mut Env, append: bool, r: u32) -> R<ExprId> {
        if let Some(id) = self.known(r) {
            return Ok(ExprId(id));
        }
        if r & KIND == PEND {
            return self.promote_pending(env, append, (r & !KIND) as usize);
        }
        self.promote_stored(env, append, r)
    }

    /// [`Builder::promote`] for pending record `i`. Pending records come
    /// children first, so this needs no stack: a pass down from `i` marks
    /// the records it needs (until none is left to find), and a pass up
    /// interns them.
    fn promote_pending(&mut self, env: &mut Env, append: bool, i: usize) -> R<ExprId> {
        let p = &mut self.pend_ids;
        p[i] = NEEDED;
        // Records marked and not yet passed.
        let mut left = 1usize;
        let mut j = i;
        loop {
            if p[j] == NEEDED {
                left -= 1;
                let (kids, k) = self.pending[j].1.kids();
                for &c in &kids[..k] {
                    if c & KIND == PEND {
                        let c = (c & !KIND) as usize;
                        if p[c] == NONE {
                            p[c] = NEEDED;
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
        for x in j..=i {
            if self.pend_ids[x] != NEEDED {
                continue;
            }
            let n = self.pending[x].1;
            let (kids, k) = n.kids();
            let mut ids = [0u32; 3];
            for (&c, id) in kids[..k].iter().zip(&mut ids) {
                *id = match c & KIND {
                    0 => c,
                    // Marked, so interned by now.
                    PEND => self.pend_ids[(c & !KIND) as usize],
                    _ => match self.known(c) {
                        Some(v) => v,
                        None => self.promote_stored(env, append, c)?.0,
                    },
                };
            }
            self.pend_ids[x] = add(env, append, n, ids)?;
        }
        Ok(ExprId(self.pend_ids[i]))
    }

    /// [`Builder::promote`] for a stored record (which refers to nothing
    /// pending).
    fn promote_stored(&mut self, env: &mut Env, append: bool, r: u32) -> R<ExprId> {
        let mut stack = std::mem::take(&mut self.stack);
        stack.clear();
        stack.push(r);
        let res: R<()> = (|| {
            while let Some(&top) = stack.last() {
                if self.known(top).is_some() {
                    stack.pop();
                    continue;
                }
                let n = self.node(top);
                let (kids, k) = n.kids();
                let mut ready = true;
                let mut ids = [0u32; 3];
                for (&c, id) in kids[..k].iter().zip(&mut ids) {
                    match self.known(c) {
                        Some(i) => *id = i,
                        None => {
                            stack.push(c);
                            ready = false;
                        }
                    }
                }
                if !ready {
                    continue;
                }
                let id = add(env, append, n, ids)?;
                if top & KIND == PEND {
                    self.pend_ids[(top & !KIND) as usize] = id;
                } else {
                    let off = (top & !KIND) as usize;
                    self.words[off] |= DONE;
                    self.words[off + 1] = id;
                }
                stack.pop();
            }
            Ok(())
        })();
        self.stack = stack;
        res?;
        Ok(ExprId(self.known(r).expect("interned")))
    }

    /// A theorem's value: its arena id if it is interned, else a lazy
    /// placeholder.
    pub(super) fn value(&mut self, r: u32) -> R<ExprId> {
        if let Some(id) = self.known(r) {
            return Ok(ExprId(id));
        }
        let k = self.roots.len() as u32;
        if k >= u32::MAX - crate::env::LAZY_BASE {
            return Err(Fail::from(Overflow("too many theorems")));
        }
        self.roots.push(r);
        Ok(ExprId(crate::env::LAZY_BASE + k))
    }

    /// At the end of a declaration: store what is still pending, and
    /// rebind each pending export id in `ids` to its new reference.
    pub(super) fn flush(&mut self, ids: &mut IdMap) -> R<()> {
        // Each pending record's new reference replaces its entry in
        // `pend_ids`; records only refer to earlier ones, which are done.
        let n = self.pending.len();
        if self.words.len() + 5 * n >= PEND as usize {
            return Err(Fail::from(Overflow("too many stored expressions")));
        }
        self.words.reserve(5 * n);
        let refs = &mut self.pend_ids;
        let words = &mut self.words;
        let tr = |refs: &[u32], r: u32| -> u32 {
            if r & KIND == PEND {
                refs[(r & !KIND) as usize]
            } else {
                r
            }
        };
        for (i, &(id, node)) in self.pending.iter().enumerate() {
            let mut r = refs[i];
            if r == NONE {
                r = STORED | words.len() as u32;
                match node {
                    Node::App(f, a) => words.extend([T_APP, tr(refs, f), tr(refs, a)]),
                    node => push_node(words, node.map(|c| tr(refs, c))),
                }
                refs[i] = r;
            }
            ids.rebind(id, r);
        }
        for &(id, r) in &self.aliases {
            ids.rebind(id, tr(refs, r));
        }
        for k in self.roots_from..self.roots.len() {
            self.roots[k] = tr(refs, self.roots[k]);
        }
        self.pending.clear();
        self.pend_ids.clear();
        self.aliases.clear();
        self.roots_from = self.roots.len();
        Ok(())
    }

    /// The source of the lazy values, once the read is done.
    pub(super) fn finish(mut self) -> Option<Box<dyn LazyValues>> {
        if self.roots.is_empty() {
            return None;
        }
        // Stored records interned since stay where they are, marked
        // `DONE`; building a value takes their arena ids from there.
        self.words.shrink_to_fit();
        self.roots.shrink_to_fit();
        Some(Box::new(Stored {
            words: self.words,
            roots: self.roots,
        }))
    }
}

/// Theorem values of an export, kept as stored records (which refer to
/// interned terms by their arena ids, or are themselves interned and
/// marked [`DONE`]).
struct Stored {
    words: Vec<u32>,
    roots: Vec<u32>,
}

thread_local! {
    /// Each thread's memo (word offset to the sink's id) and stack.
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
        self.words.capacity() * 4 + self.roots.capacity() * 4
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
        // The sink's id for `r`, if known.
        let words = &self.words;
        let done = |memo: &HashMap<u32, ExprId>, sink: &mut dyn TermSink, r: u32| {
            if r & KIND == 0 {
                return Some(sink.shared_expr(ExprId(r)));
            }
            let off = (r & !KIND) as usize;
            if words[off] & DONE != 0 {
                return Some(sink.shared_expr(ExprId(words[off + 1])));
            }
            memo.get(&(off as u32)).copied()
        };
        stack.push(root);
        while let Some(&top) = stack.last() {
            let off = top & !KIND;
            if done(memo, sink, top).is_some() {
                stack.pop();
                continue;
            }
            let n = read_node(&self.words, off);
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
            memo.insert(off, id);
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
