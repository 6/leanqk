//! Values left in their `.olean` files at load time, decoded on demand
//! into a checker's store ([`crate::env::Env::value_into`]).
//!
//! The loader keeps the files of every module with such values open
//! (memory-mapped, with their pages released after loading, so they cost
//! no memory until read again) and a handle per value: the module, the
//! value's address and its holder's. Decoding a value is the loader's
//! decoding of one term, with the same checks; each thread reuses its
//! memo and buffers. The pages read are released again every so often
//! (`touched`), so the files' pages do not pile up in memory as checking
//! reads every proof.

use super::decode::{Decoder, Memo, Tape};
use super::file::OleanFile;
use super::obj::Heap;
use crate::env::{Env, LazyValues, TermSink};
use crate::expr::{ExprId, ExprNode, LetBinder};
use crate::level::{LevelId, LevelList, LevelNode};
use crate::name::{NameId, NameNode};
use crate::strings::StrId;

pub struct OleanValues {
    /// The parts of each module (by load index) that has lazy values.
    pub modules: Vec<Option<Vec<OleanFile>>>,
    /// Per value: module, address, holder.
    pub handles: Vec<(u32, u64, u64)>,
    /// Modules read since their pages were last released, and how many
    /// values were decoded since.
    pub touched: std::sync::Mutex<(Vec<u32>, u32)>,
}

/// Release the pages read after this many values.
const RELEASE_EVERY: u32 = 1024;

impl LazyValues for OleanValues {
    fn decode(&self, env: &Env, k: u32, sink: &mut dyn TermSink) -> Result<ExprId, String> {
        let &(m, ptr, holder) = self
            .handles
            .get(k as usize)
            .ok_or("internal: no such lazy value")?;
        let Some(Some(parts)) = self.modules.get(m as usize) else {
            return Err("internal: the module of a lazy value is not open".into());
        };
        let path =
            |f: &super::Fail| format!("{}: {}", parts[parts.len() - 1].path.display(), f.msg);
        let refs: Vec<&OleanFile> = parts.iter().collect();
        let heap = Heap::new(&refs).map_err(|f| path(&f))?;
        let (memo, tape) = SCRATCH
            .with(|s| s.take())
            .unwrap_or_else(|| (Memo::stamped(), Tape::default()));
        let mut d = Decoder::reusing(&heap, memo, tape);
        let res = d.expr(ptr, holder).map_err(|f| path(&f));
        let (memo, tape) = d.into_parts();
        let res = res.and_then(|root| build(env, &tape, root, sink));
        SCRATCH.with(|s| s.set(Some((memo, tape))));
        self.touch(m);
        res
    }

    fn count(&self) -> usize {
        self.handles.len()
    }

    fn heap_bytes(&self) -> usize {
        self.handles.capacity() * 24 + self.modules.capacity() * 24
    }
}

impl OleanValues {
    pub fn new(modules: Vec<Option<Vec<OleanFile>>>, handles: Vec<(u32, u64, u64)>) -> Self {
        OleanValues {
            modules,
            handles,
            touched: Default::default(),
        }
    }

    fn touch(&self, m: u32) {
        let mut t = self.touched.lock().unwrap_or_else(|e| e.into_inner());
        if !t.0.contains(&m) {
            t.0.push(m);
        }
        t.1 += 1;
        if t.1 < RELEASE_EVERY {
            return;
        }
        let ms = std::mem::take(&mut t.0);
        t.1 = 0;
        drop(t);
        for m in ms {
            if let Some(Some(parts)) = self.modules.get(m as usize) {
                parts.iter().for_each(OleanFile::release);
            }
        }
    }
}

thread_local! {
    /// Each thread's decoding buffers, reused from value to value.
    static SCRATCH: std::cell::Cell<Option<(Memo, Tape)>> = const { std::cell::Cell::new(None) };
}

/// Build a decoded value (the tape's expression `root`) in `sink`.
fn build(env: &Env, t: &Tape, root: ExprId, sink: &mut dyn TermSink) -> Result<ExprId, String> {
    {
        let strs = t.strs.len() as u32;
        let strs: Vec<StrId> = (0..strs)
            .map(|i| env.names.strings.intern_late(t.str(StrId(i))))
            .collect::<Result<_, _>>()
            .map_err(|o| o.0.to_string())?;
        let mut names = Vec::with_capacity(t.names.len());
        for n in &t.names {
            let node = match *n {
                NameNode::Anon => NameNode::Anon,
                NameNode::Str(p, s) => NameNode::Str(names[p.index()], strs[s.index()]),
                NameNode::Num(p, k) => NameNode::Num(names[p.index()], k),
            };
            names.push(if node == NameNode::Anon {
                NameId::ANON
            } else {
                sink.name(node)
            });
        }
        let mut levels = Vec::with_capacity(t.levels.len());
        for l in &t.levels {
            let g = |x: LevelId| levels[x.index()];
            let id = match *l {
                LevelNode::Zero => LevelId::ZERO,
                LevelNode::Succ(a) => sink.level(LevelNode::Succ(g(a))),
                LevelNode::Max(a, b) => sink.level(LevelNode::Max(g(a), g(b))),
                LevelNode::IMax(a, b) => sink.level(LevelNode::IMax(g(a), g(b))),
                LevelNode::Param(n) => sink.level(LevelNode::Param(names[n.index()])),
            };
            levels.push(id);
        }
        let mut lists = Vec::with_capacity(t.level_ends.len());
        let mut buf = Vec::new();
        for i in 0..t.level_ends.len() {
            if i == 0 {
                lists.push(LevelList::EMPTY);
                continue;
            }
            buf.clear();
            buf.extend(
                t.level_list(LevelList(i as u32))
                    .iter()
                    .map(|l| levels[l.index()]),
            );
            lists.push(sink.list(&buf));
        }
        let mut exprs: Vec<ExprId> = Vec::with_capacity(t.exprs.len());
        for e in &t.exprs {
            let x = |i: ExprId| exprs[i.index()];
            let n = |i: NameId| names[i.index()];
            let id = match *e {
                ExprNode::Let(l, b) => {
                    let lb = t.lets[l.0 as usize];
                    let lb = LetBinder {
                        name: n(lb.name),
                        ty: x(lb.ty),
                        value: x(lb.value),
                        nondep: lb.nondep,
                    };
                    sink.let_in(lb, x(b))
                }
                ExprNode::NatBig(b) => sink.nat_big(t.bigs[b.0 as usize].clone()),
                node => sink.expr(match node {
                    ExprNode::Sort(l) => ExprNode::Sort(levels[l.index()]),
                    ExprNode::Const(c, ls) => ExprNode::Const(n(c), lists[ls.0 as usize]),
                    ExprNode::App(f, a) => ExprNode::App(x(f), x(a)),
                    ExprNode::Lam(bi, v, ty, b) => ExprNode::Lam(bi, n(v), x(ty), x(b)),
                    ExprNode::Pi(bi, v, ty, b) => ExprNode::Pi(bi, n(v), x(ty), x(b)),
                    ExprNode::Str(s) => ExprNode::Str(strs[s.index()]),
                    ExprNode::Proj(c, i, v) => ExprNode::Proj(n(c), i, x(v)),
                    ExprNode::FVar(_) => return Err("free variable in a declaration".into()),
                    other => other,
                }),
            };
            exprs.push(id);
        }
        Ok(exprs[root.index()])
    }
}
