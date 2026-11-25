//! A fast evaluator for closed terms, used by `Tc::whnf` before its own
//! reduction loop. See `docs/kernel-compute.md` for why it is sound.
//!
//! It is an environment machine over the checker's term DAG: a term is
//! evaluated in an environment of thunks for its loose bound variables, so
//! beta reduction never substitutes into terms. Arguments are thunks,
//! evaluated at most once (call-by-need), and every closed subterm has one
//! shared thunk, so a closed term is evaluated at most once per
//! declaration. `Nat` literals are machine words or big integers, with the
//! kernel's literal arithmetic.
//!
//! Every step it takes is one of the kernel's own reduction rules (beta,
//! delta, zeta, iota, projection, quotient, `Nat` and `String` literal
//! rules), applied as `Tc::whnf` applies them, so the result is a reduct
//! of the input: definitionally equal to it, by the rules the kernel
//! itself uses. When the machine meets anything it does not handle (a
//! stuck term, an unknown constant, a size limit, too deep a recursion) it
//! gives up, and `whnf` goes on as if it had not been called.

mod nat;
mod value;

use std::rc::{Rc, Weak};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
use std::time::Instant;

use crate::env::{Decl, DeclKind, QuotKind};
use crate::expr::{ExprId, ExprNode};
use crate::level::{LevelId, LevelList};
use crate::name::NameId;

use super::ext::{ArrayOp, NatOp};
use super::store::IdMap;
use super::tc::Tc;

use nat::Nat;
use value::{ArrVal, Env, TState, Th, Thunk, V, Val};

/// Why the machine gave up. Giving up is never a verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Bail {
    /// A term the machine does not reduce (an axiom, an opaque constant,
    /// a recursor on a stuck major premise, ...).
    Stuck,
    /// The recursion got too deep for the stack.
    Deep,
    /// A `Nat` operation hit one of the kernel's limits; `whnf` reports it.
    Limit,
    /// A thunk depends on itself.
    Loop,
    /// An erased proof was needed; `whnf` evaluates again, keeping proofs.
    Erased,
}

type ER<T> = Result<T, Bail>;

#[derive(Clone, Debug)]
pub struct CtorInfo {
    pub induct: NameId,
    pub nparams: u32,
}

#[derive(Clone, Debug)]
pub struct RecInfo {
    pub major_idx: usize,
    /// `params + motives + minors`.
    pub pmm: usize,
    pub nparams: u32,
    pub induct: NameId,
    pub k: bool,
    /// Per rule: constructor, fields, right-hand side with this constant's
    /// levels.
    pub rules: Vec<(NameId, u32, ExprId)>,
}

/// What a constant (with its levels) does in the machine.
#[derive(Clone, Debug)]
enum CInfo {
    /// A definition or theorem: its value, with the levels substituted.
    Unfold(ExprId),
    /// A built-in `Nat` operation; its definition, for arguments that are
    /// not literals.
    Op(NatOp, ExprId),
    Succ,
    Ctor(Rc<CtorInfo>),
    Rec(Rc<RecInfo>),
    QuotLift,
    QuotInd,
    /// An `Array` operation run on vectors; its definition, for arrays
    /// that are not values yet.
    Arr(ArrayOp, ExprId),
    /// An inductive type, axiom, opaque constant, `Quot` or `Quot.mk`:
    /// it does not reduce.
    Neutral,
    /// Not visible, or with the wrong number of levels: let `whnf` deal.
    Bail,
}

/// Counters for `--stats`, over the whole run.
static CALLS: AtomicU64 = AtomicU64::new(0);
static HITS: AtomicU64 = AtomicU64::new(0);
static STEPS: AtomicU64 = AtomicU64::new(0);
static BAILS: [AtomicU64; 5] = [const { AtomicU64::new(0) }; 5];
static NANOS: AtomicU64 = AtomicU64::new(0);

/// Giving up on a stuck term; `LEANQK_EVAL_DEBUG=1` says where.
#[cold]
fn stuck(at: u32) -> Bail {
    static DEBUG: OnceLock<bool> = OnceLock::new();
    if *DEBUG.get_or_init(|| std::env::var_os("LEANQK_EVAL_DEBUG").is_some()) {
        eprintln!("evaluator: stuck at eval/mod.rs:{at}");
    }
    Bail::Stuck
}

/// Whether the evaluator is on (`LEANQK_EVAL=0` turns it off, to compare).
pub fn enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var("LEANQK_EVAL").map_or(true, |v| v != "0"))
}

/// One line about what the evaluator did, for `--stats`.
pub fn stats() -> String {
    let b = |i: usize| BAILS[i].load(Relaxed);
    format!(
        "evaluator: {} calls, {} answered, {} steps, {:.3} s; gave up: {} stuck, {} deep, {} limit, {} loop; {} evaluated again keeping proofs",
        CALLS.load(Relaxed),
        HITS.load(Relaxed),
        STEPS.load(Relaxed),
        NANOS.load(Relaxed) as f64 / 1e9,
        b(0),
        b(1),
        b(2),
        b(3),
        b(4)
    )
}

/// The machine's state for the declaration being checked: everything in
/// it refers to that declaration's store, so it is dropped with it.
#[derive(Default)]
pub struct State {
    consts: IdMap<ExprId, CInfo>,
    /// One thunk per closed term.
    closed: IdMap<ExprId, Th>,
    steps: u64,
    depth: u32,
    array_names: Option<Option<(NameId, NameId, NameId)>>,
    nullary: IdMap<ExprId, V>,
    /// Per constant: memo lookups and hits.
    memo: IdMap<ExprId, (u32, u32)>,
    /// Per constant: whether it is a theorem or a constructor of a
    /// proposition (see `is_proof`).
    proof_heads: IdMap<ExprId, bool>,
    /// `of_decide_eq_true` and `of_decide_eq_false`, once looked up.
    decide_lemmas: [Option<Option<ExprId>>; 2],
    /// Whether proofs keep their environment (see `thunk`).
    keep_proofs: bool,
    /// `LEANQK_EVAL_PROFILE=1`: how often each constant was reached.
    profile: Option<IdMap<ExprId, u64>>,
}

/// A constant is memoized while at least one lookup in `MEMO_RATIO` hits,
/// judged after `MEMO_TRIAL` lookups.
const MEMO_TRIAL: u32 = 256;
const MEMO_RATIO: u32 = 32;

/// How deep `origin` looks through delayed thunks.
const ORIGIN_DEPTH: u32 = 4;

/// Evaluation recurses (forcing a thunk inside a thunk): deep recursion
/// runs on extra stack segments of `SEGMENT` bytes, taken when less than
/// `RED_ZONE` is left. `MAX_DEPTH` nested evaluations (a few GB of stack)
/// is a resource limit.
const RED_ZONE: usize = 256 << 10;
const SEGMENT: usize = 64 << 20;
const MAX_DEPTH: u32 = 4_000_000;

/// There is no step limit: evaluation is as lazy as `whnf`, so it
/// terminates whenever `whnf` does. The only limits are the stack and the
/// kernel's own `Nat` limits.
struct Machine<'a, 'e> {
    tc: &'a mut Tc<'e>,
    s: &'a mut State,
}

/// The weak head normal form of the closed term `e`, if the machine
/// computes one. `None`: the caller reduces `e` itself.
pub fn whnf(tc: &mut Tc<'_>, e: ExprId) -> Option<ExprId> {
    let mut s = tc.eval.take()?;
    let t0 = Instant::now();
    s.depth = 0;
    s.steps = 0;
    if s.profile.is_none() && std::env::var_os("LEANQK_EVAL_PROFILE").is_some() {
        s.profile = Some(IdMap::default());
    }
    let mut r = run(tc, &mut s, e);
    if r == Err(Bail::Erased) {
        // A proof was needed after all (a `K`-like recursor's major
        // premise, say). Values computed without proofs are dropped, and
        // the term is evaluated again with them.
        BAILS[Bail::Erased as usize].fetch_add(1, Relaxed);
        s.closed.clear();
        s.keep_proofs = true;
        r = run(tc, &mut s, e);
        s.keep_proofs = false;
    }
    CALLS.fetch_add(1, Relaxed);
    STEPS.fetch_add(s.steps, Relaxed);
    NANOS.fetch_add(t0.elapsed().as_nanos() as u64, Relaxed);
    match r {
        Ok(_) => HITS.fetch_add(1, Relaxed),
        Err(b) => BAILS[b as usize].fetch_add(1, Relaxed),
    };
    tc.eval = Some(s);
    r.ok()
}

fn run(tc: &mut Tc<'_>, s: &mut State, e: ExprId) -> ER<ExprId> {
    let mut m = Machine { tc, s };
    let r = m.top(e);
    if m.s.steps > 1 << 20 {
        m.dump_profile();
    }
    r
}

impl<'a, 'e> Machine<'a, 'e> {
    fn top(&mut self, e: ExprId) -> ER<ExprId> {
        let v = self.eval(e, &Env::EMPTY)?;
        // A partial application of a built-in `Nat` operation is not in
        // weak head normal form (`whnf` would unfold it).
        if let Val::Pap {
            kind: Head::Op(..) | Head::Succ | Head::Arr(..),
            ..
        } = &*v
        {
            return Err(stuck(186));
        }
        // A decision: its proof can be a huge term, and is not needed.
        if let Some(r) = self.decided(e, &v) {
            return Ok(r);
        }
        let mut rb = value::Readback::default();
        let r = rb.value(self.tc, &v);
        if rb.erased {
            return Err(Bail::Erased);
        }
        Ok(r)
    }

    /// The answer `Decidable.isTrue p h` (or `isFalse`) for `e`, without
    /// reading back the proof `h` (it may be erased, or a huge term): `p`
    /// is the proposition of `e`'s type, and `h` is replaced by
    /// `of_decide_eq_true p e (Eq.refl true)` (or `of_decide_eq_false …
    /// false`). That is a proof of the same proposition, so by proof
    /// irrelevance the answer is the same up to definitional equality. The
    /// lemma is used only if its type is the expected one.
    fn decided(&mut self, e: ExprId, v: &V) -> Option<ExprId> {
        let Val::Ctor { c, args, .. } = &**v else {
            return None;
        };
        let ExprNode::Const(cn, ls) = self.tc.st.node(*c) else {
            return None;
        };
        let names = &self.tc.st.env.names;
        let is_true = if Some(cn) == names.find_dotted("Decidable.isTrue") {
            true
        } else if Some(cn) == names.find_dotted("Decidable.isFalse") {
            false
        } else {
            return None;
        };
        if args.len() != 2 || ls != LevelList::EMPTY {
            return None;
        }
        let lemma = self.decide_lemma(is_true)?;
        // The proposition, from the type of `e` (`Decidable p`): reading it
        // back from the value may meet erased proofs too.
        let t = self.tc.infer(e).ok()?;
        let t = self.tc.whnf(t).ok()?;
        let ExprNode::App(dec, p) = self.tc.st.node(t) else {
            return None;
        };
        let names = &self.tc.st.env.names;
        match self.tc.st.node(dec) {
            ExprNode::Const(n, l)
                if Some(n) == names.find_dotted("Decidable") && l == LevelList::EMPTY => {}
            _ => return None,
        }
        let (eq, bool_, b) = (
            names.find_dotted("Eq.refl")?,
            names.find_dotted("Bool")?,
            names.find_dotted(if is_true { "Bool.true" } else { "Bool.false" })?,
        );
        let one = self.tc.st.succ(LevelId::ZERO);
        let one = self.tc.st.mk_list(&[one]);
        let refl = self.tc.st.cnst(eq, one);
        let bool_ = self.tc.st.cnst(bool_, LevelList::EMPTY);
        let b = self.tc.st.cnst(b, LevelList::EMPTY);
        let refl = self.tc.st.apps(refl, &[bool_, b]);
        let h = self.tc.st.apps(lemma, &[p, e, refl]);
        Some(self.tc.st.apps(*c, &[p, h]))
    }

    /// `of_decide_eq_true` (or `of_decide_eq_false`), if it is a theorem
    /// of type `∀ {p : Prop} [inst : Decidable p], decide p = true → p`
    /// (or `… = false → ¬p`).
    fn decide_lemma(&mut self, is_true: bool) -> Option<ExprId> {
        let i = is_true as usize;
        if let Some(l) = self.s.decide_lemmas[i] {
            return l;
        }
        let l = self.find_decide_lemma(is_true);
        self.s.decide_lemmas[i] = Some(l);
        l
    }

    fn find_decide_lemma(&mut self, is_true: bool) -> Option<ExprId> {
        let names = &self.tc.st.env.names;
        let n = names.find_dotted(if is_true {
            "of_decide_eq_true"
        } else {
            "of_decide_eq_false"
        })?;
        let ns = [
            "Decidable",
            "Decidable.decide",
            "Eq",
            "Bool",
            if is_true { "Bool.true" } else { "Bool.false" },
            "Not",
        ]
        .map(|x| names.find_dotted(x));
        let [Some(dec), Some(decide), Some(eq), Some(bool_), Some(b), not] = ns else {
            return None;
        };
        let d = self.tc.find(n)?;
        if !matches!(d.kind, DeclKind::Theorem { .. }) || !d.level_params.is_empty() {
            return None;
        }
        let st = &mut self.tc.st;
        let prop = st.sort(LevelId::ZERO);
        let (b0, b1, b2) = (st.bvar(0), st.bvar(1), st.bvar(2));
        let dec = st.cnst(dec, LevelList::EMPTY);
        let dec_p = st.app(dec, b0);
        let decide = st.cnst(decide, LevelList::EMPTY);
        let decide_p = st.apps(decide, &[b1, b0]);
        let one = st.succ(LevelId::ZERO);
        let one = st.mk_list(&[one]);
        let eq = st.cnst(eq, one);
        let bool_ = st.cnst(bool_, LevelList::EMPTY);
        let b = st.cnst(b, LevelList::EMPTY);
        let eq = st.apps(eq, &[bool_, decide_p, b]);
        let concl = if is_true {
            b2
        } else {
            let not = st.cnst(not?, LevelList::EMPTY);
            st.app(not, b2)
        };
        // The binders' names and kinds do not matter.
        let mut t = d.ty;
        for want in [prop, dec_p, eq] {
            let ExprNode::Pi(_, _, dom, body) = st.node(t) else {
                return None;
            };
            if dom != want {
                return None;
            }
            t = body;
        }
        if t != concl {
            return None;
        }
        Some(st.cnst(n, LevelList::EMPTY))
    }

    /// The shared thunk of the closed term `e`.
    fn closed(&mut self, e: ExprId) -> Th {
        if let Some(t) = self.s.closed.get(&e) {
            return t.clone();
        }
        let t = match self.tc.st.node(e) {
            ExprNode::NatSmall(lo, hi) => {
                Thunk::closed_done(e, Rc::new(Val::Nat(Nat::small(lo, hi))))
            }
            ExprNode::NatBig(b) => {
                Thunk::closed_done(e, Rc::new(Val::Nat(Nat::big(self.tc.st.big(b).clone()))))
            }
            _ => Thunk::closed(e),
        };
        self.s.closed.insert(e, t.clone());
        t
    }

    /// A thunk for `e` in `env`.
    fn thunk(&mut self, e: ExprId, env: &Env) -> Th {
        let d = self.tc.st.data(e);
        if !d.has_loose_bvars() {
            return self.closed(e);
        }
        if let ExprNode::BVar(i) = self.tc.st.node(e) {
            return env.get(i).clone();
        }
        if !self.s.keep_proofs && self.is_proof(e) {
            // The proof's term, if the terms of its variables are known;
            // else it is erased.
            return match self.term_in(e, env, 0) {
                Some(r) => Thunk::closed(r),
                None => Thunk::erased(e, env),
            };
        }
        Thunk::delayed(e, env.clone())
    }

    /// Whether the inductive type `n` is a proposition (its type ends in
    /// `Prop`).
    fn is_prop_inductive(&mut self, n: NameId) -> bool {
        let Some(d) = self.tc.find(n) else {
            return false;
        };
        let mut t = d.ty;
        while let ExprNode::Pi(_, _, _, b) = self.tc.st.node(t) {
            t = b;
        }
        matches!(self.tc.st.node(t), ExprNode::Sort(l) if l == LevelId::ZERO)
    }

    /// Whether `e` is a theorem or a constructor of a proposition applied
    /// to arguments, so a proof. The machine never needs a proof's value,
    /// only its term, and only to read back an answer or to type a
    /// `K`-like recursor's major premise. But a proof kept with its
    /// environment keeps everything the proof is about alive: a decision
    /// procedure's result `isTrue h`, stored in a data structure, would
    /// keep every step of the decision. So such a thunk is erased: it keeps
    /// its environment only weakly, and where it is needed once that is
    /// gone, `whnf` evaluates again, keeping proofs.
    fn is_proof(&mut self, mut e: ExprId) -> bool {
        while let ExprNode::App(f, _) = self.tc.st.node(e) {
            e = f;
        }
        if !matches!(self.tc.st.node(e), ExprNode::Const(..)) {
            return false;
        }
        if let Some(&b) = self.s.proof_heads.get(&e) {
            return b;
        }
        let ExprNode::Const(n, _) = self.tc.st.node(e) else {
            unreachable!()
        };
        let b = match self.tc.find(n).map(|d| d.kind) {
            Some(DeclKind::Theorem { .. }) => true,
            Some(DeclKind::Constructor { induct, .. }) => self.is_prop_inductive(induct),
            _ => false,
        };
        self.s.proof_heads.insert(e, b);
        b
    }

    fn force(&mut self, t: &Th) -> ER<V> {
        let (e, env, erased) = {
            let mut b = t.0.borrow_mut();
            match &*b {
                TState::Done(v) => return Ok(v.clone()),
                TState::Busy => return Err(Bail::Loop),
                TState::Erased(_, w) if w.strong_count() == 0 => return Err(Bail::Erased),
                TState::Erased(..) | TState::Delayed(..) => {}
            }
            match std::mem::replace(&mut *b, TState::Busy) {
                TState::Delayed(e, env) => (e, env, false),
                TState::Erased(e, w) => (e, Env(w.upgrade()), true),
                _ => unreachable!(),
            }
        };
        match self.eval(e, &env) {
            Ok(v) => {
                *t.0.borrow_mut() = TState::Done(v.clone());
                Ok(v)
            }
            Err(b) => {
                *t.0.borrow_mut() = if erased {
                    TState::Erased(e, env.0.as_ref().map_or_else(Weak::new, Rc::downgrade))
                } else {
                    TState::Delayed(e, env)
                };
                Err(b)
            }
        }
    }

    fn eval(&mut self, e: ExprId, env: &Env) -> ER<V> {
        if self.s.depth >= MAX_DEPTH {
            return Err(Bail::Deep);
        }
        self.s.depth += 1;
        // Checking the stack costs; a few frames fit in the red zone.
        let r = if self.s.depth & 7 == 0 {
            stacker::maybe_grow(RED_ZONE, SEGMENT, || self.eval_here(e, env))
        } else {
            self.eval_here(e, env)
        };
        self.s.depth -= 1;
        r
    }

    fn eval_here(&mut self, e: ExprId, env: &Env) -> ER<V> {
        self.s.steps += 1;
        if self.s.steps & ((1 << 24) - 1) == 0 && self.s.profile.is_some() {
            self.dump_profile();
        }
        let node = self.tc.st.node(e);
        match node {
            ExprNode::BVar(i) => {
                let t = env.get(i).clone();
                self.force(&t)
            }
            ExprNode::NatSmall(lo, hi) => Ok(Rc::new(Val::Nat(Nat::small(lo, hi)))),
            ExprNode::NatBig(b) => Ok(Rc::new(Val::Nat(Nat::big(self.tc.st.big(b).clone())))),
            ExprNode::Str(_) => Ok(Rc::new(Val::Str(e))),
            ExprNode::FVar(_) => Err(stuck(268)),
            ExprNode::Sort(_) | ExprNode::Pi(..) => {
                // A type: in weak head normal form already.
                let t = if self.tc.st.has_loose_bvars(e) {
                    let mut rb = value::Readback::default();
                    let t = rb.inst(self.tc, e, env);
                    if rb.erased {
                        return Err(Bail::Erased);
                    }
                    t
                } else {
                    e
                };
                Ok(Rc::new(Val::Neutral {
                    head: t,
                    args: Vec::new(),
                }))
            }
            ExprNode::Lam(..) => Ok(Rc::new(Val::Clo {
                lam: e,
                env: env.clone(),
            })),
            ExprNode::Let(h, b) => {
                let v = self.tc.st.let_binder(h).value;
                let t = self.thunk(v, env);
                let env2 = env.push(t);
                self.eval(b, &env2)
            }
            ExprNode::Const(..) => self.constant(e, Vec::new()),
            ExprNode::Proj(s, i, x) => {
                let xv = self.eval(x, env)?;
                self.proj(s, i, xv)
            }
            ExprNode::App(..) => {
                if !self.tc.st.has_loose_bvars(e) && !env.is_empty() {
                    // A closed application: share its value.
                    let t = self.closed(e);
                    return self.force(&t);
                }
                let mut f = e;
                let mut n = 0;
                while let ExprNode::App(g, _) = self.tc.st.node(f) {
                    n += 1;
                    f = g;
                }
                let mut args = Vec::with_capacity(n);
                let mut g = e;
                while let ExprNode::App(h, a) = self.tc.st.node(g) {
                    args.push(self.thunk(a, env));
                    g = h;
                }
                args.reverse();
                match self.tc.st.node(f) {
                    ExprNode::Const(..) => self.constant(f, args),
                    ExprNode::Lam(..) => self.beta(f, env.clone(), args),
                    _ => {
                        let fv = self.eval(f, env)?;
                        self.apply(fv, args)
                    }
                }
            }
        }
    }

    #[cold]
    fn dump_profile(&mut self) {
        let Some(p) = self.s.profile.as_ref() else {
            return;
        };
        let mut v: Vec<(u64, ExprId)> = p.iter().map(|(&c, &n)| (n, c)).collect();
        v.sort_unstable_by(|a, b| b.cmp(a));
        eprintln!(
            "evaluator: {} steps, depth {}; most reached:",
            self.s.steps, self.s.depth
        );
        for (n, c) in v.into_iter().take(400) {
            eprintln!("  {n:>12} {}", self.tc.pp(c));
        }
    }

    /// The machine's view of the constant `c`.
    fn info(&mut self, c: ExprId) -> CInfo {
        if let Some(i) = self.s.consts.get(&c) {
            return i.clone();
        }
        let i = self.compute_info(c);
        self.s.consts.insert(c, i.clone());
        i
    }

    fn compute_info(&mut self, c: ExprId) -> CInfo {
        let ExprNode::Const(n, ls) = self.tc.st.node(c) else {
            unreachable!()
        };
        let Some(d) = self.tc.find(n) else {
            return CInfo::Bail;
        };
        if self.tc.st.list(ls).len() != d.level_params.len() {
            return CInfo::Bail;
        }
        let ext = self.tc.ext;
        if ls == LevelList::EMPTY && Some(n) == ext.nat_succ {
            return CInfo::Succ;
        }
        match d.kind {
            DeclKind::Definition { value, .. } | DeclKind::Theorem { value, .. } => {
                let v = self.inst_levels(&d, ls, value);
                if ls == LevelList::EMPTY
                    && let Some(op) = ext.nat_op(n)
                {
                    return CInfo::Op(op, v);
                }
                if let Some(&op) = ext.array_ops.get(&n) {
                    return CInfo::Arr(op, v);
                }
                CInfo::Unfold(v)
            }
            DeclKind::Constructor {
                induct, num_params, ..
            } => CInfo::Ctor(Rc::new(CtorInfo {
                induct,
                nparams: num_params,
            })),
            DeclKind::Recursor {
                num_params,
                num_indices,
                num_motives,
                num_minors,
                rules,
                k,
                ..
            } => {
                let Some(induct) = self.tc.major_induct_of(n, &d) else {
                    return CInfo::Bail;
                };
                let rs: Vec<_> = self.tc.st.rec_rules(rules).to_vec();
                let rules = rs
                    .iter()
                    .map(|r| (r.ctor, r.nfields, self.inst_levels(&d, ls, r.rhs)))
                    .collect();
                CInfo::Rec(Rc::new(RecInfo {
                    major_idx: (num_params + num_motives + num_minors + num_indices) as usize,
                    pmm: (num_params + num_motives + num_minors) as usize,
                    nparams: num_params,
                    induct,
                    k,
                    rules,
                }))
            }
            DeclKind::Quot { kind } => match kind {
                QuotKind::Lift => CInfo::QuotLift,
                QuotKind::Ind => CInfo::QuotInd,
                QuotKind::Type | QuotKind::Ctor => CInfo::Neutral,
            },
            DeclKind::Axiom { .. } | DeclKind::Opaque { .. } | DeclKind::Inductive { .. } => {
                CInfo::Neutral
            }
        }
    }

    fn inst_levels(&mut self, d: &Decl, ls: LevelList, e: ExprId) -> ExprId {
        if ls == LevelList::EMPTY {
            return e;
        }
        let ps: Vec<NameId> = self.tc.st.lparams(d).to_vec();
        let lv: Vec<LevelId> = self.tc.st.list(ls).to_vec();
        self.tc.st.instantiate_lparams(e, &ps, &lv)
    }

    /// The constant `c` applied to `args`.
    fn constant(&mut self, c: ExprId, args: Vec<Th>) -> ER<V> {
        if let Some(p) = self.s.profile.as_mut() {
            *p.entry(c).or_default() += 1;
        }
        match self.info(c) {
            CInfo::Unfold(v) => {
                let t = self.closed(v);
                let f = self.force(&t)?;
                if args.is_empty() {
                    return Ok(f);
                }
                // Arguments that are all known terms: this is the closed
                // term `c a₁ … aₙ`, whose value is shared through its id,
                // as `whnf`'s cache shares it after substitution.
                // Building the key costs a term; constants whose keys
                // rarely hit are not memoized any more.
                let st = self.s.memo.entry(c).or_default();
                if st.0 >= MEMO_TRIAL && st.1 * MEMO_RATIO < st.0 {
                    return self.apply(f, args);
                }
                st.0 += 1;
                let Some(key) = self.closed_app(c, &args) else {
                    return self.apply(f, args);
                };
                let kt = self.closed(key);
                let st = self.s.memo.entry(c).or_default();
                if let TState::Done(v) = &*kt.0.borrow() {
                    st.1 += 1;
                    return Ok(v.clone());
                }
                let v = self.apply(f, args)?;
                let mut b = kt.0.borrow_mut();
                if let TState::Delayed(..) = &*b {
                    *b = TState::Done(v.clone());
                }
                Ok(v)
            }
            CInfo::Op(op, _) => self.saturate(c, Head::Op(op), args),
            CInfo::Succ => self.saturate(c, Head::Succ, args),
            CInfo::Rec(r) => self.saturate(c, Head::Rec(r), args),
            CInfo::QuotLift => self.saturate(c, Head::QuotLift, args),
            CInfo::QuotInd => self.saturate(c, Head::QuotInd, args),
            CInfo::Arr(op, v) => self.saturate(c, Head::Arr(op, v), args),
            CInfo::Ctor(info) if args.is_empty() => {
                // One shared value per constructor constant.
                if let Some(v) = self.s.nullary.get(&c) {
                    return Ok(v.clone());
                }
                let v = Rc::new(Val::Ctor { c, info, args });
                self.s.nullary.insert(c, v.clone());
                Ok(v)
            }
            CInfo::Ctor(info) => Ok(Rc::new(Val::Ctor { c, info, args })),
            CInfo::Neutral => Ok(Rc::new(Val::Neutral { head: c, args })),
            CInfo::Bail => Err(stuck(444)),
        }
    }

    /// The term `c a₁ … aₙ`, if every argument's term is known.
    fn closed_app(&mut self, c: ExprId, args: &[Th]) -> Option<ExprId> {
        let mut r = c;
        for a in args {
            let x = self.origin(a)?;
            r = self.tc.st.app(r, x);
        }
        Some(r)
    }

    /// The closed term a thunk stands for, when it is at hand.
    fn origin(&mut self, t: &Th) -> Option<ExprId> {
        self.origin_at(t, 0)
    }

    /// `e` with its loose bound variables replaced by the terms of their
    /// thunks in `env`, if known.
    fn term_in(&mut self, e: ExprId, env: &Env, depth: u32) -> Option<ExprId> {
        let n = self.tc.st.data(e).loose_bvar_range();
        let ts: Vec<Th> = env.first(n)?.into_iter().cloned().collect();
        let mut s = Vec::with_capacity(n as usize);
        for t in &ts {
            s.push(self.origin_at(t, depth + 1)?);
        }
        Some(self.tc.st.instantiate(e, &s))
    }

    fn origin_at(&mut self, t: &Th, depth: u32) -> Option<ExprId> {
        if let Some(e) = t.1.get() {
            return Some(e);
        }
        let b = t.0.borrow();
        let v = match &*b {
            TState::Done(v) => v.clone(),
            TState::Busy => return None,
            TState::Delayed(..) | TState::Erased(..) => {
                // `e` with its variables replaced by their known terms.
                if depth >= ORIGIN_DEPTH {
                    return None;
                }
                let (e, env) = match &*b {
                    TState::Delayed(e, env) => (*e, env.clone()),
                    TState::Erased(e, w) => (*e, Env(Some(w.upgrade()?))),
                    _ => unreachable!(),
                };
                drop(b);
                let r = self.term_in(e, &env, depth)?;
                t.1.set(Some(r));
                return Some(r);
            }
        };
        drop(b);
        match &*v {
            Val::Nat(Nat::Small(x)) => Some(self.tc.st.nat_u64(*x)),
            Val::Str(e) => Some(*e),
            Val::Ctor { c, args, .. } | Val::Neutral { head: c, args } if args.is_empty() => {
                Some(*c)
            }
            _ => None,
        }
    }

    /// A head that reduces once it has `arity` arguments.
    fn saturate(&mut self, c: ExprId, kind: Head, args: Vec<Th>) -> ER<V> {
        if args.len() < kind.arity() {
            return Ok(Rc::new(Val::Pap {
                head: c,
                kind,
                args,
            }));
        }
        match kind {
            Head::Succ => {
                let mut args = args;
                let x = self.force(&args[0])?;
                let rest = args.split_off(1);
                let r = match self.nat_of(&x) {
                    Some(n) => Rc::new(Val::Nat(n.succ())),
                    None => return Err(stuck(518)),
                };
                self.apply_rest(r, rest)
            }
            Head::Op(op) => {
                let mut args = args;
                let rest = args.split_off(2);
                let x = self.force(&args[0])?;
                let y = self.force(&args[1])?;
                let r = match (self.nat_of(&x), self.nat_of(&y)) {
                    (Some(x), Some(y)) => self.nat_op(op, &x, &y)?,
                    _ => {
                        // Not literals: the operation is its definition.
                        let CInfo::Op(_, v) = self.info(c) else {
                            unreachable!()
                        };
                        let t = self.closed(v);
                        let f = self.force(&t)?;
                        self.apply(f, args)?
                    }
                };
                self.apply_rest(r, rest)
            }
            Head::Rec(r) => self.iota(&r, args),
            Head::Arr(op, def) => self.array_op(c, op, def, args),
            Head::QuotLift | Head::QuotInd => {
                let (mk_pos, arg_pos) = if matches!(kind, Head::QuotLift) {
                    (5, 3)
                } else {
                    (4, 3)
                };
                let q = self.force(&args[mk_pos])?;
                let Val::Neutral { head, args: margs } = &*q else {
                    return Err(stuck(550));
                };
                let is_mk = match (self.tc.st.node(*head), self.tc.ext.quot.as_ref()) {
                    (ExprNode::Const(n, _), Some(qn)) => n == qn.mk,
                    _ => false,
                };
                if !is_mk || margs.len() != 3 {
                    return Err(stuck(557));
                }
                let f = self.force(&args[arg_pos])?;
                let mut rest = vec![margs[2].clone()];
                rest.extend_from_slice(&args[mk_pos + 1..]);
                self.apply(f, rest)
            }
        }
    }

    fn apply_rest(&mut self, v: V, rest: Vec<Th>) -> ER<V> {
        if rest.is_empty() {
            Ok(v)
        } else {
            self.apply(v, rest)
        }
    }

    /// The value of a `Nat` (a literal or `Nat.zero`).
    fn nat_of(&self, v: &V) -> Option<Nat> {
        match &**v {
            Val::Nat(n) => Some(n.clone()),
            Val::Ctor { c, args, .. } if args.is_empty() => match self.tc.st.node(*c) {
                ExprNode::Const(n, ls)
                    if Some(n) == self.tc.ext.nat_zero && ls == LevelList::EMPTY =>
                {
                    Some(Nat::ZERO)
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn mk_bool(&mut self, b: bool) -> ER<V> {
        let n = if b {
            self.tc.ext.bool_true
        } else {
            self.tc.ext.bool_false
        };
        let Some(n) = n else {
            return Err(stuck(598));
        };
        let c = self.tc.st.cnst(n, LevelList::EMPTY);
        self.constant(c, Vec::new())
    }

    fn nat_op(&mut self, op: NatOp, x: &Nat, y: &Nat) -> ER<V> {
        match nat::op(op, x, y)? {
            nat::OpResult::Nat(n) => Ok(Rc::new(Val::Nat(n))),
            nat::OpResult::Bool(b) => self.mk_bool(b),
        }
    }

    /// Beta: the lambda `lam` (in `env`) applied to `args`.
    fn beta(&mut self, mut lam: ExprId, env: Env, mut args: Vec<Th>) -> ER<V> {
        let mut i = 0;
        while i < args.len()
            && let ExprNode::Lam(_, _, _, b) = self.tc.st.node(lam)
        {
            lam = b;
            i += 1;
        }
        if i == 0 {
            let v = self.eval(lam, &env)?;
            return self.apply(v, args);
        }
        let rest = args.split_off(i);
        let env = env.push_all(args);
        let v = self.eval(lam, &env)?;
        self.apply_rest(v, rest)
    }

    fn apply(&mut self, f: V, args: Vec<Th>) -> ER<V> {
        if args.is_empty() {
            return Ok(f);
        }
        match &*f {
            Val::Clo { lam, env } => self.beta(*lam, env.clone(), args),
            Val::Ctor { c, info, args: a0 } => {
                let mut a = a0.clone();
                a.extend(args);
                Ok(Rc::new(Val::Ctor {
                    c: *c,
                    info: info.clone(),
                    args: a,
                }))
            }
            Val::Neutral { head, args: a0 } => {
                if !a0.is_empty() || matches!(self.tc.st.node(*head), ExprNode::Const(..)) {
                    let mut a = a0.clone();
                    a.extend(args);
                    Ok(Rc::new(Val::Neutral {
                        head: *head,
                        args: a,
                    }))
                } else {
                    // A sort or a Pi applied to arguments: ill-typed.
                    Err(stuck(655))
                }
            }
            Val::Pap {
                head,
                kind,
                args: a0,
            } => {
                let mut a = a0.clone();
                a.extend(args);
                self.saturate(*head, kind.clone(), a)
            }
            Val::Nat(_) | Val::Str(_) | Val::Arr(_) => Err(stuck(667)),
        }
    }

    /// Projection `i` of the structure `s` out of `x`.
    fn proj(&mut self, s: NameId, i: u32, x: V) -> ER<V> {
        let x = match &*x {
            Val::Str(e) => {
                let e = *e;
                self.string_ctor(e)?
            }
            Val::Arr(a) => {
                let a = a.clone();
                self.array_ctor(&a)?
            }
            _ => x,
        };
        match &*x {
            Val::Ctor { info, args, .. } if info.induct == s => {
                let k = info.nparams as usize + i as usize;
                match args.get(k) {
                    Some(t) => {
                        let t = t.clone();
                        self.force(&t)
                    }
                    None => Err(stuck(688)),
                }
            }
            _ => Err(stuck(691)),
        }
    }

    /// A string literal as `String.ofList [...]`, evaluated.
    fn string_ctor(&mut self, e: ExprId) -> ER<V> {
        let x = self
            .tc
            .string_lit_to_constructor(e)
            .map_err(|_| Bail::Stuck)?;
        self.eval(x, &Env::EMPTY)
    }

    /// Iota reduction: the recursor `r` applied to `args` (at least up to
    /// its major premise).
    fn iota(&mut self, r: &RecInfo, args: Vec<Th>) -> ER<V> {
        let mut major = args[r.major_idx].clone();
        if r.k {
            // As Lean does, before reducing the major premise: if its type
            // is the type of the constructor (built from the parameters),
            // use the constructor.
            let mut rb = value::Readback::default();
            let m = rb.thunk(self.tc, &major);
            if rb.erased {
                return Err(Bail::Erased);
            }
            let c = self
                .tc
                .ctor_when_k_pub(r.induct, r.nparams, m)
                .map_err(|_| Bail::Stuck)?;
            if c != m {
                major = self.closed(c);
            }
        }
        let mut mv = self.force(&major)?;
        match &*mv {
            Val::Nat(n) => {
                mv = self.nat_ctor(n)?;
            }
            Val::Str(e) => {
                let e = *e;
                mv = self.string_ctor(e)?;
            }
            Val::Arr(a) => {
                let a = a.clone();
                mv = self.array_ctor(&a)?;
            }
            _ => {}
        }
        let Val::Ctor { c, args: margs, .. } = &*mv else {
            if std::env::var_os("LEANQK_EVAL_DEBUG").is_some() {
                let mut rb = value::Readback::default();
                let x = rb.value(self.tc, &mv);
                eprintln!(
                    "evaluator: stuck major of a recursor on {}: {}",
                    self.tc.show(r.induct),
                    self.tc.pp(x).chars().take(400).collect::<String>()
                );
            }
            return Err(stuck(734));
        };
        let ExprNode::Const(cn, _) = self.tc.st.node(*c) else {
            unreachable!()
        };
        let Some(&(_, nfields, rhs)) = r.rules.iter().find(|x| x.0 == cn) else {
            return Err(stuck(740));
        };
        let nfields = nfields as usize;
        if nfields > margs.len() {
            return Err(stuck(744));
        }
        let mut a = Vec::with_capacity(r.pmm + nfields + args.len() - r.major_idx - 1);
        a.extend_from_slice(&args[..r.pmm]);
        a.extend_from_slice(&margs[margs.len() - nfields..]);
        a.extend_from_slice(&args[r.major_idx + 1..]);
        let t = self.closed(rhs);
        let f = self.force(&t)?;
        self.apply(f, a)
    }

    /// An `Array` operation applied to (at least) its arguments: on a
    /// vector if the array is one or is `Array.mk` of a list built to its
    /// end, else by its definition.
    fn array_op(&mut self, c: ExprId, op: ArrayOp, def: ExprId, mut args: Vec<Th>) -> ER<V> {
        let n = Head::Arr(op, def).arity();
        let rest = args.split_off(n);
        let r = match self.array_arg(c, &args[1])? {
            None => None,
            Some(a) => match op {
                ArrayOp::Size => Some(Rc::new(Val::Nat(Nat::Small(a.elems.len() as u64)))),
                ArrayOp::Push => {
                    let mut a = a;
                    Rc::make_mut(&mut a).elems.push(args[2].clone());
                    Some(Rc::new(Val::Arr(a)))
                }
                ArrayOp::Get | ArrayOp::Set => {
                    let i = self.force(&args[2])?;
                    match self.nat_of(&i) {
                        Some(Nat::Small(i)) if (i as usize) < a.elems.len() => {
                            let i = i as usize;
                            if op == ArrayOp::Get {
                                let t = a.elems[i].clone();
                                Some(self.force(&t)?)
                            } else {
                                let mut a = a;
                                Rc::make_mut(&mut a).elems[i] = args[3].clone();
                                Some(Rc::new(Val::Arr(a)))
                            }
                        }
                        _ => None,
                    }
                }
            },
        };
        let r = match r {
            Some(r) => r,
            None => {
                let t = self.closed(def);
                let f = self.force(&t)?;
                self.apply(f, args)?
            }
        };
        self.apply_rest(r, rest)
    }

    /// The array `t` as a vector, if it is one or `Array.mk` of a list
    /// whose spine evaluates to its end; `c` is the operation (for the
    /// universe level).
    fn array_arg(&mut self, c: ExprId, t: &Th) -> ER<Option<Rc<ArrVal>>> {
        let v = self.force(t)?;
        let (ty, mut l) = match &*v {
            Val::Arr(a) => return Ok(Some(a.clone())),
            Val::Ctor { args, .. } if args.len() == 2 && self.is_array_mk(&v) => {
                (args[0].clone(), args[1].clone())
            }
            _ => return Ok(None),
        };
        let Some((mk, cons, nil)) = self.array_consts(c) else {
            return Ok(None);
        };
        let mut elems = Vec::new();
        loop {
            let x = self.force(&l)?;
            match &*x {
                Val::Ctor { c, args, .. } if *c == cons && args.len() == 3 => {
                    elems.push(args[1].clone());
                    l = args[2].clone();
                }
                Val::Ctor { c, args, .. } if *c == nil && args.len() == 1 => break,
                _ => return Ok(None),
            }
        }
        Ok(Some(Rc::new(ArrVal {
            mk,
            cons,
            nil,
            ty,
            elems,
        })))
    }

    fn is_array_mk(&mut self, v: &V) -> bool {
        let Val::Ctor { c, .. } = &**v else {
            return false;
        };
        match (self.tc.st.node(*c), self.array_names()) {
            (ExprNode::Const(n, _), Some((m, _, _))) => n == m,
            _ => false,
        }
    }

    /// `Array.mk`, `List.cons` and `List.nil`, if declared.
    fn array_names(&mut self) -> Option<(NameId, NameId, NameId)> {
        *self.s.array_names.get_or_insert_with(|| {
            let names = &self.tc.st.env.names;
            Some((
                names.find_dotted("Array.mk")?,
                names.find_dotted("List.cons")?,
                names.find_dotted("List.nil")?,
            ))
        })
    }

    /// `Array.mk`, `List.cons` and `List.nil` at the level of the array
    /// operation `c`.
    fn array_consts(&mut self, c: ExprId) -> Option<(ExprId, ExprId, ExprId)> {
        let ExprNode::Const(_, ls) = self.tc.st.node(c) else {
            return None;
        };
        let (m, c, n) = self.array_names()?;
        Some((
            self.tc.st.cnst(m, ls),
            self.tc.st.cnst(c, ls),
            self.tc.st.cnst(n, ls),
        ))
    }

    /// The vector `a` as the constructor application it stands for.
    fn array_ctor(&mut self, a: &ArrVal) -> ER<V> {
        let nil_info = self.ctor_info(a.nil)?;
        let cons_info = self.ctor_info(a.cons)?;
        let mk_info = self.ctor_info(a.mk)?;
        let mut l = Rc::new(Val::Ctor {
            c: a.nil,
            info: nil_info,
            args: vec![a.ty.clone()],
        });
        for e in a.elems.iter().rev() {
            l = Rc::new(Val::Ctor {
                c: a.cons,
                info: cons_info.clone(),
                args: vec![a.ty.clone(), e.clone(), Thunk::done(l)],
            });
        }
        Ok(Rc::new(Val::Ctor {
            c: a.mk,
            info: mk_info,
            args: vec![a.ty.clone(), Thunk::done(l)],
        }))
    }

    fn ctor_info(&mut self, c: ExprId) -> ER<Rc<CtorInfo>> {
        match self.info(c) {
            CInfo::Ctor(i) => Ok(i),
            _ => Err(stuck(0)),
        }
    }

    /// `n` as `Nat.zero` or `Nat.succ (n - 1)`.
    fn nat_ctor(&mut self, n: &Nat) -> ER<V> {
        let (Some(zero), Some(succ)) = (self.tc.ext.nat_zero, self.tc.ext.nat_succ) else {
            return Err(stuck(758));
        };
        match n.pred() {
            None => {
                let c = self.tc.st.cnst(zero, LevelList::EMPTY);
                self.constant(c, Vec::new())
            }
            Some(p) => {
                let c = self.tc.st.cnst(succ, LevelList::EMPTY);
                let CInfo::Succ = self.info(c) else {
                    return Err(stuck(768));
                };
                let info = Rc::new(CtorInfo {
                    induct: self.tc.ext.nat.ok_or(Bail::Stuck)?,
                    nparams: 0,
                });
                Ok(Rc::new(Val::Ctor {
                    c,
                    info,
                    args: vec![Thunk::done(Rc::new(Val::Nat(p)))],
                }))
            }
        }
    }
}

/// A head that waits for its arguments.
#[derive(Clone, Debug)]
pub enum Head {
    Op(NatOp),
    Succ,
    Rec(Rc<RecInfo>),
    QuotLift,
    QuotInd,
    /// With the operation's definition.
    Arr(ArrayOp, ExprId),
}

impl Head {
    fn arity(&self) -> usize {
        match self {
            Head::Op(_) => 2,
            Head::Succ => 1,
            Head::Rec(r) => r.major_idx + 1,
            Head::QuotLift => 6,
            Head::QuotInd => 5,
            Head::Arr(ArrayOp::Size, _) => 2,
            Head::Arr(ArrayOp::Push, _) => 3,
            Head::Arr(ArrayOp::Get, _) => 4,
            Head::Arr(ArrayOp::Set, _) => 5,
        }
    }
}
