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

use hashbrown::HashMap;
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
}

#[derive(Default)]
struct Memo {
    names: HashMap<u64, u32, Fx>,
    levels: HashMap<u64, u32, Fx>,
    lists: HashMap<u64, u32, Fx>,
    exprs: HashMap<u64, u32, Fx>,
}

/// A fast hasher for addresses (8-aligned, so the low bits carry nothing).
#[derive(Default, Clone, Copy)]
pub struct Fx;

pub struct FxHasher(u64);

impl std::hash::BuildHasher for Fx {
    type Hasher = FxHasher;
    fn build_hasher(&self) -> FxHasher {
        FxHasher(0)
    }
}

impl std::hash::Hasher for FxHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = (self.0.rotate_left(5) ^ b as u64).wrapping_mul(0x517c_c1b7_2722_0a95);
        }
    }
    fn write_u64(&mut self, n: u64) {
        let r = (n as u128).wrapping_mul(0x9e37_79b9_7f4a_7c15);
        self.0 = (r as u64) ^ ((r >> 64) as u64);
    }
}

pub struct Decoder<'h, 'a> {
    heap: &'h Heap<'a>,
    pub tape: Tape,
    memo: Memo,
    stack: Vec<(u64, u64, bool)>,
    lvl_buf: Vec<LevelId>,
}

fn too_many(what: &str) -> Fail {
    Fail::malformed(format!("too many {what} in one module"))
}

fn idx(len: usize, what: &str) -> Result<u32, Fail> {
    u32::try_from(len)
        .ok()
        .filter(|&n| n < u32::MAX - 1)
        .ok_or_else(|| too_many(what))
}

impl<'h, 'a> Decoder<'h, 'a> {
    pub fn new(heap: &'h Heap<'a>) -> Self {
        let mut tape = Tape::default();
        tape.names.push(NameNode::Anon);
        tape.levels.push(LevelNode::Zero);
        tape.level_ends.push(0);
        Decoder {
            heap,
            tape,
            memo: Memo::default(),
            stack: Vec::new(),
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
                    if let Some(&id) = self.memo.names.get(&o.addr) {
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
            self.memo.names.insert(addr, id);
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
            if let Some(&id) = self.memo.levels.get(&o.addr) {
                self.stack.pop();
                last = LevelId(id);
                continue;
            }
            let get = |d: &Self, i: usize| -> Result<Option<LevelId>, Fail> {
                match d.heap.get(o.field(i), o.addr)? {
                    Val::Scalar(0) => Ok(Some(LevelId::ZERO)),
                    Val::Scalar(_) => Err(Fail::malformed("bad universe level")),
                    Val::Obj(c) => Ok(d.memo.levels.get(&c.addr).map(|&i| LevelId(i))),
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
            self.memo.levels.insert(o.addr, id);
            self.stack.pop();
            last = LevelId(id);
        }
        Ok(last)
    }

    fn level_list(&mut self, ptr: u64, holder: u64) -> Result<LevelList, Fail> {
        if ptr == 1 {
            return Ok(LevelList::EMPTY);
        }
        if let Some(&id) = self.memo.lists.get(&ptr) {
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
            self.memo.lists.insert(ptr, id);
            Ok(LevelList(id))
        });
        self.lvl_buf = buf;
        out
    }

    /// The memoized id of the expression at `ptr`, following `mdata`.
    fn expr_done(&self, ptr: u64) -> Option<ExprId> {
        self.memo.exprs.get(&ptr).map(|&i| ExprId(i))
    }

    /// An `Expr`, with an explicit stack.
    pub fn expr(&mut self, ptr: u64, holder: u64) -> Result<ExprId, Fail> {
        let start = self.stack.len();
        self.stack.push((ptr, holder, false));
        while self.stack.len() > start {
            let (p, h, expanded) = *self.stack.last().expect("nonempty");
            if self.expr_done(p).is_some() {
                self.stack.pop();
                continue;
            }
            let o = self.obj(p, h, "an expression")?;
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
            o.ctor(o.tag, nobjs, scalars, "expression")?;
            if !expanded && !kids.is_empty() {
                self.stack.last_mut().expect("nonempty").2 = true;
                for &i in kids.iter().rev() {
                    let c = o.field(i);
                    if self.expr_done(c).is_none() {
                        // Check the bound now so the stack only holds
                        // pointers that go down.
                        self.obj(c, o.addr, "an expression")?;
                        self.stack.push((c, o.addr, false));
                    }
                }
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
                    self.memo.exprs.insert(o.addr, inner.0);
                    self.stack.pop();
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
            self.memo.exprs.insert(o.addr, id);
            self.stack.pop();
        }
        self.expr_done(ptr)
            .ok_or_else(|| Fail::malformed("internal: unresolved expression"))
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

    pub fn finish(self) -> Tape {
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
