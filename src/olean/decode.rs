//! Decoding a module's compacted objects into a [`Tape`]: its names,
//! levels, expressions and constants with module-local ids, children
//! before parents. Decoding touches no shared state, so modules decode in
//! parallel; [`super::build`] then interns tapes into the [`crate::env::Env`].
//!
//! Object layouts are in `docs/olean-format.md`. Lean's cached data (the
//! hashes in `Name`, `Level.data`, `Expr.data`) is never read: the arenas
//! recompute what the checker uses when the nodes are interned.
//!
//! Every walk is iterative, and [`Heap::get`] only follows pointers to lower
//! addresses, so no input can overflow the stack or loop.

use num_bigint::BigUint;

use super::Fail;
use super::obj::{Heap, NatVal, Obj, Val};
use crate::env::{Decl, DeclKind, Hints, NameList, QuotKind, RecRule, RuleList, Safety};
use crate::expr::{BigId, BinderInfo, ExprData, ExprId, ExprNode, LetBinder, LetId};
use crate::level::{LevelId, LevelList, LevelNode};
use crate::name::{NameId, NameNode};
use crate::strings::{StrId, StrPool};

/// A module's kernel data, with local ids. Id 0 is the anonymous name and
/// the zero level; level list 0 is the empty list.
#[derive(Default)]
pub struct Tape {
    pub strs: StrPool,
    pub names: Vec<NameNode>,
    pub levels: Vec<LevelNode>,
    pub level_pool: Vec<LevelId>,
    /// Ends of the level lists in `level_pool`; list `i` is
    /// `level_pool[ends[i-1]..ends[i]]`.
    pub level_ends: Vec<u32>,
    pub exprs: Vec<ExprNode>,
    pub lets: Vec<LetBinder>,
    pub bigs: Vec<BigUint>,
    pub name_pool: Vec<NameId>,
    pub rules: Vec<RecRule>,
    pub decls: Vec<Decl>,
    /// Direct imports (local name ids), for the main part only.
    pub imports: Vec<NameId>,
    pub is_module: bool,
    /// The names by depth (components), and the expressions by height.
    pub name_order: Layers,
    pub expr_order: Layers,
}

/// Indices grouped into layers: layer `d` is `order[ends[d-1]..ends[d]]`.
#[derive(Default)]
pub struct Layers {
    pub order: Vec<u32>,
    pub ends: Vec<u32>,
}

impl Layers {
    /// Counting sort of the indices `0..keys.len()` by key.
    fn new(keys: &[u32]) -> Layers {
        let mut ends: Vec<u32> = Vec::new();
        for &k in keys {
            if k as usize >= ends.len() {
                ends.resize(k as usize + 1, 0);
            }
            ends[k as usize] += 1;
        }
        let mut next = Vec::with_capacity(ends.len());
        let mut acc = 0u32;
        for e in ends.iter_mut() {
            next.push(acc);
            acc += *e;
            *e = acc;
        }
        let mut order = vec![0u32; keys.len()];
        for (i, &k) in keys.iter().enumerate() {
            order[next[k as usize] as usize] = i as u32;
            next[k as usize] += 1;
        }
        Layers { order, ends }
    }
}

/// The local id already decoded for an object, by address: a dense array
/// with one entry per 8 bytes of the module's data, valid where its bit is
/// set (so it never needs clearing beyond the bits). An entry holds the id
/// and, in its top two bits, what kind of value it is, so an object read
/// as two kinds (in a malformed file) is decoded once per kind rather than
/// confused.
#[derive(Default)]
pub struct Memo {
    bits: Vec<u64>,
    vals: Vec<u32>,
    /// (first address, end address, first entry) of each part.
    parts: Vec<(u64, u64, usize)>,
}

#[derive(Clone, Copy)]
#[repr(u32)]
enum Kind {
    Name = 0,
    Level = 1,
    List = 2,
    Expr = 3,
}

/// Local ids are below this, so the kind fits above them.
const MAX_LOCAL: u32 = 1 << 30;

impl Memo {
    /// Reset for `heap`, keeping the allocations.
    pub fn reset(&mut self, heap: &Heap<'_>) {
        self.parts.clear();
        let mut n = 0usize;
        for (lo, hi) in heap.ranges() {
            self.parts.push((lo, hi, n));
            n += ((hi - lo) / 8) as usize;
        }
        self.bits.clear();
        self.bits.resize(n / 64 + 1, 0);
        if self.vals.len() < n {
            self.vals.resize(n, 0);
        }
    }

    #[inline]
    fn slot(&self, addr: u64) -> Option<usize> {
        // Most objects are in the last part.
        for &(lo, hi, first) in self.parts.iter().rev() {
            if addr >= lo {
                return (addr < hi).then(|| first + ((addr - lo) / 8) as usize);
            }
        }
        None
    }

    #[inline]
    fn get(&self, kind: Kind, addr: u64) -> Option<u32> {
        let k = self.slot(addr)?;
        if self.bits[k / 64] >> (k % 64) & 1 == 0 {
            return None;
        }
        let v = self.vals[k];
        (v >> 30 == kind as u32).then_some(v & (MAX_LOCAL - 1))
    }

    #[inline]
    fn insert(&mut self, kind: Kind, addr: u64, id: u32) {
        debug_assert!(id < MAX_LOCAL);
        if let Some(k) = self.slot(addr) {
            self.bits[k / 64] |= 1 << (k % 64);
            self.vals[k] = (kind as u32) << 30 | id;
        }
    }
}

pub struct Decoder<'h, 'a> {
    heap: &'h Heap<'a>,
    pub tape: Tape,
    memo: Memo,
    stack: Vec<(u64, u64, bool)>,
    estack: Vec<(Obj<'a>, bool)>,
    lvl_buf: Vec<LevelId>,
}

fn too_many(what: &str) -> Fail {
    Fail::malformed(format!("too many {what} in one module"))
}

fn idx(len: usize, what: &str) -> Result<u32, Fail> {
    u32::try_from(len)
        .ok()
        .filter(|&n| n < MAX_LOCAL)
        .ok_or_else(|| too_many(what))
}

impl<'h, 'a> Decoder<'h, 'a> {
    pub fn new(heap: &'h Heap<'a>) -> Self {
        Self::with_memo(heap, Memo::default())
    }

    /// A decoder that reuses `memo`'s allocations.
    pub fn with_memo(heap: &'h Heap<'a>, mut memo: Memo) -> Self {
        memo.reset(heap);
        let mut tape = Tape::default();
        tape.names.push(NameNode::Anon);
        tape.levels.push(LevelNode::Zero);
        tape.level_ends.push(0);
        Decoder {
            heap,
            tape,
            memo,
            stack: Vec::new(),
            estack: Vec::new(),
            lvl_buf: Vec::new(),
        }
    }

    fn obj(&self, ptr: u64, holder: u64, what: &str) -> Result<Obj<'a>, Fail> {
        match self.heap.get(ptr, holder)? {
            Val::Obj(o) => Ok(o),
            Val::Scalar(_) => Err(Fail::malformed(format!("expected {what}, found a scalar"))),
        }
    }

    fn small_nat(&self, ptr: u64, holder: u64, what: &str) -> Result<u64, Fail> {
        match self.heap.nat(self.heap.get(ptr, holder)?)? {
            NatVal::Small(n) => Ok(n),
            NatVal::Big(_) => Err(Fail::malformed(format!("{what} is too large"))),
        }
    }

    fn nat_u32(&self, ptr: u64, holder: u64, what: &str) -> Result<u32, Fail> {
        let n = self.small_nat(ptr, holder, what)?;
        u32::try_from(n).map_err(|_| Fail::malformed(format!("{what} is too large")))
    }

    /// The module data at the root: imports, constants and the module flag.
    pub fn module(&mut self, root: u64, want_imports: bool, want_consts: bool) -> Result<(), Fail> {
        let m = self.obj(root, u64::MAX, "module data")?;
        m.ctor(0, 5, 1, "module data")?;
        self.tape.is_module = m.bool_at(0)?;
        if want_imports {
            let imps = self.obj(m.field(0), m.addr, "imports")?;
            for p in imps.array()? {
                let i = self.obj(p, imps.addr, "import")?;
                i.ctor(0, 1, 3, "import")?;
                let n = self.name(i.field(0), i.addr)?;
                self.tape.imports.push(n);
            }
        }
        if want_consts {
            let cs = self.obj(m.field(2), m.addr, "constants")?;
            for p in cs.array()? {
                let d = self.constant(p, cs.addr)?;
                self.tape.decls.push(d);
            }
        }
        Ok(())
    }

    /// A `Name`. Iterative: collect the components up to a known prefix.
    pub fn name(&mut self, ptr: u64, holder: u64) -> Result<NameId, Fail> {
        let mut chain: Vec<(u64, NameNode)> = Vec::new();
        let (mut p, mut h) = (ptr, holder);
        let mut base = loop {
            match self.heap.get(p, h)? {
                Val::Scalar(0) => break NameId::ANON,
                Val::Scalar(_) => return Err(Fail::malformed("bad name")),
                Val::Obj(o) => {
                    if let Some(id) = self.memo.get(Kind::Name, o.addr) {
                        break NameId(id);
                    }
                    let node = match o.tag {
                        1 => {
                            o.ctor(1, 2, 8, "name")?;
                            let s = self.obj(o.field(1), o.addr, "name component")?.string()?;
                            let s = self.tape.strs.intern(s).map_err(|_| too_many("strings"))?;
                            NameNode::Str(NameId::ANON, s)
                        }
                        2 => {
                            o.ctor(2, 2, 8, "name")?;
                            NameNode::Num(
                                NameId::ANON,
                                self.small_nat(o.field(1), o.addr, "name component")?,
                            )
                        }
                        _ => return Err(Fail::malformed("bad name")),
                    };
                    chain.push((o.addr, node));
                    (p, h) = (o.field(0), o.addr);
                }
            }
        };
        while let Some((addr, node)) = chain.pop() {
            let node = match node {
                NameNode::Str(_, s) => NameNode::Str(base, s),
                NameNode::Num(_, n) => NameNode::Num(base, n),
                NameNode::Anon => NameNode::Anon,
            };
            let id = idx(self.tape.names.len(), "names")?;
            self.tape.names.push(node);
            self.memo.insert(Kind::Name, addr, id);
            base = NameId(id);
        }
        Ok(base)
    }

    /// A `Level`, with an explicit stack.
    fn level(&mut self, ptr: u64, holder: u64) -> Result<LevelId, Fail> {
        let start = self.stack.len();
        self.stack.push((ptr, holder, false));
        let mut last = LevelId::ZERO;
        while self.stack.len() > start {
            let (p, h, expanded) = *self.stack.last().expect("nonempty");
            let o = match self.heap.get(p, h)? {
                Val::Scalar(0) => {
                    // `Level.zero` may also appear boxed.
                    self.stack.pop();
                    last = LevelId::ZERO;
                    continue;
                }
                Val::Scalar(_) => return Err(Fail::malformed("bad universe level")),
                Val::Obj(o) => o,
            };
            if let Some(id) = self.memo.get(Kind::Level, o.addr) {
                self.stack.pop();
                last = LevelId(id);
                continue;
            }
            let get = |d: &Self, i: usize| -> Result<Option<LevelId>, Fail> {
                match d.heap.get(o.field(i), o.addr)? {
                    Val::Scalar(0) => Ok(Some(LevelId::ZERO)),
                    Val::Scalar(_) => Err(Fail::malformed("bad universe level")),
                    Val::Obj(c) => Ok(d.memo.get(Kind::Level, c.addr).map(LevelId)),
                }
            };
            let nkids = match o.tag {
                0 => 0,
                1 => 1,
                2 | 3 => 2,
                4 => 0,
                5 => return Err(Fail::malformed("universe metavariable in a declaration")),
                t => return Err(Fail::malformed(format!("bad universe level tag {t}"))),
            };
            o.ctor(
                o.tag,
                if o.tag == 4 { 1 } else { nkids },
                8,
                "universe level",
            )?;
            if !expanded && nkids > 0 {
                self.stack.last_mut().expect("nonempty").2 = true;
                for i in (0..nkids as usize).rev() {
                    if get(self, i)?.is_none() {
                        self.stack.push((o.field(i), o.addr, false));
                    }
                }
                continue;
            }
            let kid = |d: &Self, i| -> Result<LevelId, Fail> {
                get(d, i)?.ok_or_else(|| Fail::malformed("internal: unresolved level"))
            };
            let node = match o.tag {
                0 => LevelNode::Zero,
                1 => LevelNode::Succ(kid(self, 0)?),
                2 => LevelNode::Max(kid(self, 0)?, kid(self, 1)?),
                3 => LevelNode::IMax(kid(self, 0)?, kid(self, 1)?),
                _ => LevelNode::Param(self.name(o.field(0), o.addr)?),
            };
            let id = if node == LevelNode::Zero {
                0
            } else {
                let id = idx(self.tape.levels.len(), "levels")?;
                self.tape.levels.push(node);
                id
            };
            self.memo.insert(Kind::Level, o.addr, id);
            self.stack.pop();
            last = LevelId(id);
        }
        Ok(last)
    }

    fn level_list(&mut self, ptr: u64, holder: u64) -> Result<LevelList, Fail> {
        if ptr == 1 {
            return Ok(LevelList::EMPTY);
        }
        if let Some(id) = self.memo.get(Kind::List, ptr) {
            return Ok(LevelList(id));
        }
        let mut buf = std::mem::take(&mut self.lvl_buf);
        buf.clear();
        let res = (|| {
            let (mut p, mut h) = (ptr, holder);
            loop {
                match self.heap.get(p, h)? {
                    Val::Scalar(0) => break,
                    Val::Scalar(_) => return Err(Fail::malformed("bad level list")),
                    Val::Obj(c) => {
                        c.ctor(1, 2, 0, "level list")?;
                        buf.push(self.level(c.field(0), c.addr)?);
                        (p, h) = (c.field(1), c.addr);
                    }
                }
            }
            Ok(())
        })();
        let out = res.and_then(|()| {
            let id = idx(self.tape.level_ends.len(), "level lists")?;
            self.tape.level_pool.extend_from_slice(&buf);
            let end = idx(self.tape.level_pool.len(), "levels")?;
            self.tape.level_ends.push(end);
            self.memo.insert(Kind::List, ptr, id);
            Ok(LevelList(id))
        });
        self.lvl_buf = buf;
        out
    }

    /// The memoized id of the expression at `ptr`, following `mdata`.
    fn expr_done(&self, ptr: u64) -> Option<ExprId> {
        self.memo.get(Kind::Expr, ptr).map(ExprId)
    }

    /// An `Expr`, with an explicit stack.
    pub fn expr(&mut self, ptr: u64, holder: u64) -> Result<ExprId, Fail> {
        if let Some(e) = self.expr_done(ptr) {
            return Ok(e);
        }
        let root = self.obj(ptr, holder, "an expression")?;
        let mut stack = std::mem::take(&mut self.estack);
        stack.clear();
        stack.push((root, false));
        let res = self.expr_walk(&mut stack);
        self.estack = stack;
        res?;
        self.expr_done(ptr)
            .ok_or_else(|| Fail::malformed("internal: unresolved expression"))
    }

    /// Decode the expressions on `stack` (resolved objects, and whether
    /// their children have been pushed).
    fn expr_walk(&mut self, stack: &mut Vec<(Obj<'a>, bool)>) -> Result<(), Fail> {
        while let Some(&(o, expanded)) = stack.last() {
            // (object fields, scalar bytes, expression children)
            let (nobjs, scalars, kids): (u8, usize, &[usize]) = match o.tag {
                0 => (1, 8, &[]),
                1 => return Err(Fail::malformed("free variable in a declaration")),
                2 => return Err(Fail::malformed("metavariable in a declaration")),
                3 => (1, 8, &[]),
                4 => (2, 8, &[]),
                5 => (2, 8, &[0, 1]),
                6 | 7 => (3, 9, &[1, 2]),
                8 => (4, 9, &[1, 2, 3]),
                9 => (1, 8, &[]),
                10 => (2, 8, &[1]),
                11 => (3, 8, &[2]),
                t => return Err(Fail::malformed(format!("bad expression tag {t}"))),
            };
            if !expanded {
                o.ctor(o.tag, nobjs, scalars, "expression")?;
                stack.last_mut().expect("nonempty").1 = true;
                let mut pushed = false;
                for &i in kids.iter().rev() {
                    let c = o.field(i);
                    if self.expr_done(c).is_none() {
                        // Resolving the child checks that it lies below
                        // its holder, so the walk only goes down.
                        let co = self.obj(c, o.addr, "an expression")?;
                        stack.push((co, false));
                        pushed = true;
                    }
                }
                if pushed {
                    continue;
                }
            } else if self.expr_done(o.addr).is_some() {
                // Reached twice through shared children before it was done.
                stack.pop();
                continue;
            }
            let kid = |d: &Self, i: usize| {
                d.expr_done(o.field(i))
                    .ok_or_else(|| Fail::malformed("internal: unresolved expression"))
            };
            let node = match o.tag {
                0 => {
                    let i = self.small_nat(o.field(0), o.addr, "bound variable index")?;
                    match u32::try_from(i) {
                        Ok(i) if i < ExprData::MAX_RANGE => ExprNode::BVar(i),
                        _ => return Err(Fail::malformed(format!("bvar index {i} is too large"))),
                    }
                }
                3 => ExprNode::Sort(self.level(o.field(0), o.addr)?),
                4 => ExprNode::Const(
                    self.name(o.field(0), o.addr)?,
                    self.level_list(o.field(1), o.addr)?,
                ),
                5 => ExprNode::App(kid(self, 0)?, kid(self, 1)?),
                6 | 7 => {
                    let bi = match o.u8_at(8)? {
                        0 => BinderInfo::Default,
                        1 => BinderInfo::Implicit,
                        2 => BinderInfo::StrictImplicit,
                        3 => BinderInfo::InstImplicit,
                        b => return Err(Fail::malformed(format!("bad binder info {b}"))),
                    };
                    let n = self.name(o.field(0), o.addr)?;
                    let (t, b) = (kid(self, 1)?, kid(self, 2)?);
                    if o.tag == 6 {
                        ExprNode::Lam(bi, n, t, b)
                    } else {
                        ExprNode::Pi(bi, n, t, b)
                    }
                }
                8 => {
                    let b = LetBinder {
                        name: self.name(o.field(0), o.addr)?,
                        ty: kid(self, 1)?,
                        value: kid(self, 2)?,
                        nondep: o.bool_at(8)?,
                    };
                    let l = idx(self.tape.lets.len(), "let binders")?;
                    self.tape.lets.push(b);
                    ExprNode::Let(LetId(l), kid(self, 3)?)
                }
                9 => {
                    let lit = self.obj(o.field(0), o.addr, "a literal")?;
                    match lit.tag {
                        0 => {
                            lit.ctor(0, 1, 0, "literal")?;
                            match self.heap.nat(self.heap.get(lit.field(0), lit.addr)?)? {
                                NatVal::Small(v) => ExprNode::NatSmall(v as u32, (v >> 32) as u32),
                                NatVal::Big(d) => {
                                    let n = BigUint::from_slice(&d);
                                    if let Ok(v) = u64::try_from(&n) {
                                        ExprNode::NatSmall(v as u32, (v >> 32) as u32)
                                    } else {
                                        let i = idx(self.tape.bigs.len(), "literals")?;
                                        self.tape.bigs.push(n);
                                        ExprNode::NatBig(BigId(i))
                                    }
                                }
                            }
                        }
                        1 => {
                            lit.ctor(1, 1, 0, "literal")?;
                            let s = self.obj(lit.field(0), lit.addr, "a string")?.string()?;
                            ExprNode::Str(
                                self.tape.strs.intern(s).map_err(|_| too_many("strings"))?,
                            )
                        }
                        _ => return Err(Fail::malformed("bad literal")),
                    }
                }
                10 => {
                    // `mdata` is kernel-transparent: alias its inner term.
                    let inner = kid(self, 1)?;
                    self.memo.insert(Kind::Expr, o.addr, inner.0);
                    stack.pop();
                    continue;
                }
                _ => ExprNode::Proj(
                    self.name(o.field(0), o.addr)?,
                    self.nat_u32(o.field(1), o.addr, "projection index")?,
                    kid(self, 2)?,
                ),
            };
            let id = idx(self.tape.exprs.len(), "expressions")?;
            self.tape.exprs.push(node);
            self.memo.insert(Kind::Expr, o.addr, id);
            stack.pop();
        }
        Ok(())
    }

    fn name_list(&mut self, ptr: u64, holder: u64) -> Result<NameList, Fail> {
        let start = idx(self.tape.name_pool.len(), "names")?;
        let (mut p, mut h) = (ptr, holder);
        loop {
            match self.heap.get(p, h)? {
                Val::Scalar(0) => break,
                Val::Scalar(_) => return Err(Fail::malformed("bad name list")),
                Val::Obj(c) => {
                    c.ctor(1, 2, 0, "name list")?;
                    let n = self.name(c.field(0), c.addr)?;
                    self.tape.name_pool.push(n);
                    (p, h) = (c.field(1), c.addr);
                }
            }
        }
        let len = idx(self.tape.name_pool.len(), "names")? - start;
        Ok(NameList { start, len })
    }

    /// A `ConstantInfo`.
    fn constant(&mut self, ptr: u64, holder: u64) -> Result<Decl, Fail> {
        let ci = self.obj(ptr, holder, "a constant")?;
        if ci.tag > 7 {
            return Err(Fail::malformed(format!("bad constant tag {}", ci.tag)));
        }
        ci.ctor(ci.tag, 1, 0, "constant")?;
        let v = self.obj(ci.field(0), ci.addr, "a constant")?;
        // (object fields, scalar bytes) of each `*Val` structure.
        let (nobjs, scalars) = match ci.tag {
            0 => (1, 1),
            1 => (4, 1),
            2 => (3, 0),
            3 => (3, 1),
            4 => (1, 1),
            5 => (6, 3),
            6 => (5, 1),
            _ => (7, 2),
        };
        v.ctor(0, nobjs, scalars, "constant")?;
        let cv = self.obj(v.field(0), v.addr, "a constant")?;
        cv.ctor(0, 3, 0, "constant header")?;
        let name = self.name(cv.field(0), cv.addr)?;
        let level_params = self.name_list(cv.field(1), cv.addr)?;
        let ty = self.expr(cv.field(2), cv.addr)?;
        let f = |i: usize| v.field(i);
        let kind = match ci.tag {
            0 => DeclKind::Axiom {
                is_unsafe: v.bool_at(0)?,
            },
            1 => {
                let value = self.expr(f(1), v.addr)?;
                let hints = match self.heap.get(f(2), v.addr)? {
                    Val::Scalar(0) => Hints::Opaque,
                    Val::Scalar(1) => Hints::Abbrev,
                    Val::Obj(h) if h.tag == 2 => {
                        h.ctor(2, 0, 4, "reducibility hints")?;
                        Hints::Regular(h.u32_at(0)?)
                    }
                    _ => return Err(Fail::malformed("bad reducibility hints")),
                };
                let safety = match v.u8_at(0)? {
                    0 => Safety::Unsafe,
                    1 => Safety::Safe,
                    2 => Safety::Partial,
                    s => return Err(Fail::malformed(format!("bad definition safety {s}"))),
                };
                DeclKind::Definition {
                    value,
                    hints,
                    safety,
                    all: self.name_list(f(3), v.addr)?,
                }
            }
            2 => DeclKind::Theorem {
                value: self.expr(f(1), v.addr)?,
                all: self.name_list(f(2), v.addr)?,
            },
            3 => DeclKind::Opaque {
                value: self.expr(f(1), v.addr)?,
                all: self.name_list(f(2), v.addr)?,
                is_unsafe: v.bool_at(0)?,
            },
            4 => DeclKind::Quot {
                kind: match v.u8_at(0)? {
                    0 => QuotKind::Type,
                    1 => QuotKind::Ctor,
                    2 => QuotKind::Lift,
                    3 => QuotKind::Ind,
                    k => return Err(Fail::malformed(format!("bad quotient kind {k}"))),
                },
            },
            5 => DeclKind::Inductive {
                num_params: self.nat_u32(f(1), v.addr, "numParams")?,
                num_indices: self.nat_u32(f(2), v.addr, "numIndices")?,
                all: self.name_list(f(3), v.addr)?,
                ctors: self.name_list(f(4), v.addr)?,
                num_nested: self.nat_u32(f(5), v.addr, "numNested")?,
                is_rec: v.bool_at(0)?,
                is_unsafe: v.bool_at(1)?,
                is_reflexive: v.bool_at(2)?,
            },
            6 => DeclKind::Constructor {
                induct: self.name(f(1), v.addr)?,
                cidx: self.nat_u32(f(2), v.addr, "cidx")?,
                num_params: self.nat_u32(f(3), v.addr, "numParams")?,
                num_fields: self.nat_u32(f(4), v.addr, "numFields")?,
                is_unsafe: v.bool_at(0)?,
            },
            _ => {
                let all = self.name_list(f(1), v.addr)?;
                let num_params = self.nat_u32(f(2), v.addr, "numParams")?;
                let num_indices = self.nat_u32(f(3), v.addr, "numIndices")?;
                let num_motives = self.nat_u32(f(4), v.addr, "numMotives")?;
                let num_minors = self.nat_u32(f(5), v.addr, "numMinors")?;
                let start = idx(self.tape.rules.len(), "recursor rules")?;
                let (mut p, mut h) = (f(6), v.addr);
                loop {
                    match self.heap.get(p, h)? {
                        Val::Scalar(0) => break,
                        Val::Scalar(_) => return Err(Fail::malformed("bad rule list")),
                        Val::Obj(c) => {
                            c.ctor(1, 2, 0, "rule list")?;
                            let r = self.obj(c.field(0), c.addr, "a recursor rule")?;
                            r.ctor(0, 3, 0, "recursor rule")?;
                            let rule = RecRule {
                                ctor: self.name(r.field(0), r.addr)?,
                                nfields: self.nat_u32(r.field(1), r.addr, "nfields")?,
                                rhs: self.expr(r.field(2), r.addr)?,
                            };
                            self.tape.rules.push(rule);
                            (p, h) = (c.field(1), c.addr);
                        }
                    }
                }
                let len = idx(self.tape.rules.len(), "recursor rules")? - start;
                DeclKind::Recursor {
                    all,
                    num_params,
                    num_indices,
                    num_motives,
                    num_minors,
                    rules: RuleList { start, len },
                    k: v.bool_at(0)?,
                    is_unsafe: v.bool_at(1)?,
                }
            }
        };
        Ok(Decl {
            name,
            level_params,
            ty,
            kind,
        })
    }

    pub fn finish(mut self) -> Tape {
        let t = &mut self.tape;
        // Name 0 (anonymous) is layer 0 and needs no interning; the rest
        // come after their prefixes.
        let mut depth: Vec<u32> = Vec::with_capacity(t.names.len());
        for n in &t.names {
            depth.push(match *n {
                NameNode::Anon => 0,
                NameNode::Str(p, _) | NameNode::Num(p, _) => depth[p.index()] + 1,
            });
        }
        let mut names = Layers::new(&depth);
        names.order.retain(|&i| i != 0);
        if let Some(e) = names.ends.first_mut() {
            *e = 0;
        }
        for e in names.ends.iter_mut().skip(1) {
            *e -= 1;
        }
        t.name_order = names;
        let mut height: Vec<u32> = Vec::with_capacity(t.exprs.len());
        for e in &t.exprs {
            let g = |x: ExprId| height[x.index()];
            height.push(match *e {
                ExprNode::App(a, b) | ExprNode::Lam(_, _, a, b) | ExprNode::Pi(_, _, a, b) => {
                    g(a).max(g(b)) + 1
                }
                ExprNode::Let(l, b) => {
                    let l = t.lets[l.0 as usize];
                    g(l.ty).max(g(l.value)).max(g(b)) + 1
                }
                ExprNode::Proj(_, _, x) => g(x) + 1,
                _ => 0,
            });
        }
        t.expr_order = Layers::new(&height);
        self.tape
    }
}

impl Tape {
    pub fn level_list(&self, l: LevelList) -> &[LevelId] {
        let i = l.0 as usize;
        let start = if i == 0 {
            0
        } else {
            self.level_ends[i - 1] as usize
        };
        &self.level_pool[start..self.level_ends[i] as usize]
    }

    pub fn str(&self, s: StrId) -> &str {
        self.strs.get(s)
    }
}
