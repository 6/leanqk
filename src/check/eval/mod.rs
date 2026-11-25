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

use super::shape::{self, CasesInfo, Head as Shape, Heads, Minor, RecInfo, Src, Tree, TreeInfo};
use std::rc::{Rc, Weak};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
use std::time::Instant;

use crate::env::{Decl, DeclKind, QuotKind};
use crate::expr::{ExprId, ExprNode};
use crate::level::{LevelId, LevelList};
use crate::name::NameId;

use super::ext::{ArrayOp, DecEqOp, IntOp, ListOp, NatOp};
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

/// What a constant (with its levels) does in the machine.
#[derive(Clone, Debug)]
enum CInfo {
    /// A definition or theorem: its value, with the levels substituted,
    /// and for a projection function (`fun p₁ … pₖ self => self.i`, as
    /// `HAdd.hAdd` or `Add.add`) its number of binders `k`, else 0.
    Unfold(ExprId, u32),
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
    /// A `List` operation run as a loop; its definition, for lists that
    /// are not values.
    List(ListOp, ExprId),
    /// A `DecidableEq` instance decided on values; its definition, for
    /// values it does not compare.
    DecEq(DecEqOp, ExprId),
    /// `instBEqProd`; its definition.
    BEqProd(ExprId),
    /// An `Int` operation run on values; its definition.
    Int(IntOp, ExprId),
    /// A definition of the shape of a `casesOn` (see `cases_shape`); its
    /// value.
    Cases(Rc<CasesInfo>, ExprId),
    /// A matcher of nested `casesOn`s (see `tree_shape`); its value.
    Tree(Rc<TreeInfo>, ExprId),
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
/// Fast paths taken: `List` operations, `DecidableEq` decisions, `==` on
/// pairs.
static FAST: [AtomicU64; 6] = [const { AtomicU64::new(0) }; 6];

/// Giving up on a stuck term; `NITROLEAN_EVAL_DEBUG=1` says where.
#[cold]
fn stuck(at: u32) -> Bail {
    static DEBUG: OnceLock<bool> = OnceLock::new();
    if *DEBUG.get_or_init(|| std::env::var_os("NITROLEAN_EVAL_DEBUG").is_some()) {
        eprintln!("evaluator: stuck at eval/mod.rs:{at}");
    }
    Bail::Stuck
}

/// Whether the evaluator is on (`NITROLEAN_EVAL=0` turns it off, to compare).
pub fn enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var("NITROLEAN_EVAL").map_or(true, |v| v != "0"))
}

/// One line about what the evaluator did, for `--stats`.
pub fn stats() -> String {
    let b = |i: usize| BAILS[i].load(Relaxed);
    format!(
        "evaluator: {} calls, {} answered, {} steps, {:.3} s; gave up: {} stuck, {} deep, {} limit, {} loop; {} evaluated again keeping proofs; fast: {} list, {} decidable-eq, {} pair ==, {} int, {} shared method, {} cases",
        CALLS.load(Relaxed),
        HITS.load(Relaxed),
        STEPS.load(Relaxed),
        NANOS.load(Relaxed) as f64 / 1e9,
        b(0),
        b(1),
        b(2),
        b(3),
        b(4),
        FAST[0].load(Relaxed),
        FAST[1].load(Relaxed),
        FAST[2].load(Relaxed),
        FAST[3].load(Relaxed),
        FAST[4].load(Relaxed),
        FAST[5].load(Relaxed)
    )
}

/// The machine's state for the declaration being checked: everything in
/// it refers to that declaration's store, so it is dropped with it.
#[derive(Default)]
pub struct State {
    consts: IdMap<ExprId, CInfo>,
    /// One thunk per closed term.
    closed: IdMap<ExprId, Th>,
    /// How to build the argument thunks of an application, per term.
    apps: IdMap<ExprId, Rc<AppPlan>>,
    /// `rule_info` per recursor rule.
    rules: IdMap<ExprId, Option<Rc<RuleInfo>>>,
    steps: u64,
    /// Fast-path hits not yet added to `FAST` (kept here so that threads
    /// do not share a counter on every hit).
    fast: [u64; 6],
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
    /// Whether proofs keep their environment (see `thunk`). Decisions of
    /// the `DecidableEq` operations then carry a proof term (see
    /// `decision`).
    keep_proofs: bool,
    /// Per `DecidableEq` operation (with its levels): the proposition
    /// `x = y` of its result type, over its arguments as `#(n-1) … #0`.
    dec_props: IdMap<ExprId, Option<ExprId>>,
    /// Per definition of `instBEqProd` (with its levels): `fun α β bα bβ
    /// => f`, where the definition is `fun α β bα bβ => BEq.mk T f`.
    beq_fields: IdMap<ExprId, Option<ExprId>>,
    /// Per projection function: the values of `c p₁ … pₖ` for the last
    /// few argument thunks it was applied to (see `method`).
    methods: IdMap<ExprId, Vec<Method>>,
    /// `NITROLEAN_EVAL_PROFILE=1`: how often each constant was reached.
    profile: Option<IdMap<ExprId, u64>>,
    /// Every array version made, to empty them when the state goes (see
    /// `Drop`).
    arrays: Vec<Weak<ArrVal>>,
}

/// The versions of a persistent array can form a cycle with what they
/// hold: a version points to the newer one it was changed into, and the
/// newer one's elements can hold the older version (a delayed `a.set! i
/// (f a[i])`, or a structure holding both). Reference counting never
/// frees such a cycle, so the arrays are emptied when the state goes, and
/// with them everything they keep. No value outlives the state: what
/// leaves it is read back first.
impl Drop for State {
    fn drop(&mut self) {
        for a in self.arrays.drain(..) {
            if let Some(a) = a.upgrade() {
                ArrVal::clear(&a);
            }
        }
    }
}

impl State {
    /// Records the array version `a` (see `Drop`). Versions already
    /// freed are forgotten whenever the record doubles.
    fn array(&mut self, a: Rc<ArrVal>) -> Rc<ArrVal> {
        if self.arrays.len() == self.arrays.capacity() && self.arrays.len() >= 64 {
            self.arrays.retain(|w| w.strong_count() > 0);
            let n = self.arrays.len();
            self.arrays.reserve(n.max(64));
        }
        self.arrays.push(Rc::downgrade(&a));
        a
    }
}

/// A constant is memoized while at least one lookup in `MEMO_RATIO` hits,
/// judged after `MEMO_TRIAL` lookups.
/// Whether a decision `Decidable.intro p b h` is answered without reading
/// back its proof `h`, as `isTrue` and `isFalse` are (`decided`).
const DECIDED_INTRO: bool = true;

/// Whether a proof's term is built when its thunk is made. Most proofs are
/// never read back (decisions are answered without theirs), and building
/// their terms by substitution cost more on Lean's own library than the
/// evaluator saved; a proof read back after its environment is gone makes
/// the run start again keeping proofs.
const EAGER_PROOF_TERMS: bool = false;

const MEMO_TRIAL: u32 = 256;
const MEMO_RATIO: u32 = 32;

/// What evaluation goes on with: a value, or a term to evaluate in place
/// of the current one (a tail call).
enum Next {
    V(V),
    Eval(ExprId, Env),
}

/// A recursor rule's minor premise (its index) and inductive hypotheses
/// (see `rule_info`).
type RuleInfo = (usize, Box<[ExprId]>);

/// The head of an application term and how each argument's thunk is made.
struct AppPlan {
    head: ExprId,
    /// The head's `info`, if it is a constant.
    info: Option<CInfo>,
    args: Box<[ArgPlan]>,
}

enum ArgPlan {
    /// A bound variable: its thunk.
    Var(u32),
    /// A closed term: its shared thunk.
    Closed(Th),
    /// A proof (see `is_proof`).
    Proof(ExprId),
    /// Any other term, delayed in the environment.
    Delayed(ExprId),
}

/// A method's argument thunks `p₁ … pₖ` and the value of `c p₁ … pₖ`.
type Method = (Box<[Th]>, V);

/// How many instances each projection function remembers (see `method`).
const METHOD_CACHE: usize = 8;

/// How deep `origin` looks through delayed thunks.
const ORIGIN_DEPTH: u32 = 4;

/// Evaluation recurses (forcing a thunk inside a thunk): deep recursion
/// runs on extra stack segments of `SEGMENT` bytes, taken when less than
/// `RED_ZONE` is left. `MAX_DEPTH` nested evaluations (a few GB of stack)
/// is a resource limit.
const RED_ZONE: usize = 256 << 10;
const SEGMENT: usize = 64 << 20;
const MAX_DEPTH: u32 = 4_000_000;

/// Evaluation is as lazy as `whnf`, so it terminates whenever `whnf` does,
/// subject to stack and `Nat` resource limits.
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
    if s.profile.is_none() && std::env::var_os("NITROLEAN_EVAL_PROFILE").is_some() {
        s.profile = Some(IdMap::default());
    }
    let mut r = run(tc, &mut s, e);
    if r == Err(Bail::Erased) {
        // A proof was needed after all (a `K`-like recursor's major
        // premise, say). Values computed without proofs are dropped, and
        // the term is evaluated again with them.
        BAILS[Bail::Erased as usize].fetch_add(1, Relaxed);
        s.closed.clear();
        s.apps.clear();
        s.keep_proofs = true;
        r = run(tc, &mut s, e);
        s.keep_proofs = false;
    }
    CALLS.fetch_add(1, Relaxed);
    STEPS.fetch_add(s.steps, Relaxed);
    for (n, f) in s.fast.iter_mut().zip(&FAST) {
        if *n > 0 {
            f.fetch_add(std::mem::take(n), Relaxed);
        }
    }
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

impl Heads for Machine<'_, '_> {
    fn st(&self) -> &super::store::Store<'_> {
        &self.tc.st
    }

    fn head(&mut self, h: ExprId) -> Shape {
        match self.info(h) {
            CInfo::Rec(r) => Shape::Rec(r),
            CInfo::Cases(ci, _) => Shape::Cases(ci),
            CInfo::Ctor(ci) => Shape::Ctor(ci.nparams),
            _ => Shape::Other,
        }
    }
}

impl<'a, 'e> Machine<'a, 'e> {
    fn top(&mut self, e: ExprId) -> ER<ExprId> {
        let v = self.eval(e, &Env::EMPTY)?;
        // A partial application of a built-in `Nat` operation is not in
        // weak head normal form (`whnf` would unfold it).
        if let Val::Pap {
            kind:
                Head::Op(..)
                | Head::Succ
                | Head::Arr(..)
                | Head::List(..)
                | Head::DecEq(..)
                | Head::BEqProd(..)
                | Head::BEqProdFn
                | Head::Int(..)
                | Head::Cases(..)
                | Head::Tree(..),
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

    /// The answer `Decidable.isTrue p h` (or `isFalse`, or `Decidable.intro
    /// p b h`) for `e`, without
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
        // `Decidable.intro p b h` (a structure since Lean v4.36): `h`
        // proves `Bool.Reflects b p`, which is `p` or `¬p` as `b` is
        // `true` or `false`.
        let intro = DECIDED_INTRO && Some(cn) == names.find_dotted("Decidable.intro");
        let is_true = if intro {
            if args.len() != 3 || ls != LevelList::EMPTY {
                return None;
            }
            let b = self.force(&args[1]).ok()?;
            let Val::Ctor { c: bc, .. } = &*b else {
                return None;
            };
            let ExprNode::Const(bn, _) = self.tc.st.node(*bc) else {
                return None;
            };
            let names = &self.tc.st.env.names;
            if Some(bn) == names.find_dotted("Bool.true") {
                true
            } else if Some(bn) == names.find_dotted("Bool.false") {
                false
            } else {
                return None;
            }
        } else if Some(cn) == names.find_dotted("Decidable.isTrue") {
            true
        } else if Some(cn) == names.find_dotted("Decidable.isFalse") {
            false
        } else {
            return None;
        };
        if !intro && (args.len() != 2 || ls != LevelList::EMPTY) {
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
        if intro {
            return Some(self.tc.st.apps(*c, &[p, b, h]));
        }
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
            return self.proof_thunk(e, env);
        }
        Thunk::delayed(e, env.clone())
    }

    /// The proof's term, if the terms of its variables are known and
    /// `EAGER_PROOF_TERMS`; else it is erased (its term is built if it is
    /// read back while its environment lives).
    #[inline(never)]
    fn proof_thunk(&mut self, e: ExprId, env: &Env) -> Th {
        if !EAGER_PROOF_TERMS {
            return Thunk::erased(e, env);
        }
        match self.term_in(e, env, 0) {
            Some(r) => Thunk::closed(r),
            None => Thunk::erased(e, env),
        }
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

    /// Evaluation of `e` in `env`, with calls in tail position (a beta
    /// step that takes all the arguments, a `let` body, a recursor's
    /// minor premise) run in this loop rather than nested, so that the
    /// stack grows only with non-tail evaluations.
    fn eval_here(&mut self, e: ExprId, env: &Env) -> ER<V> {
        let mut e = e;
        let mut owned: Option<Env> = None;
        loop {
            let next = self.step(e, owned.as_ref().unwrap_or(env))?;
            match next {
                Next::V(v) => return Ok(v),
                Next::Eval(e2, env2) => {
                    e = e2;
                    owned = Some(env2);
                }
            }
        }
    }

    fn step(&mut self, e: ExprId, env: &Env) -> ER<Next> {
        self.s.steps += 1;
        if self.s.steps & ((1 << 24) - 1) == 0 && self.s.profile.is_some() {
            self.dump_profile();
        }
        let node = self.tc.st.node(e);
        match node {
            ExprNode::BVar(i) => {
                let t = env.get(i).clone();
                self.force(&t).map(Next::V)
            }
            ExprNode::NatSmall(lo, hi) => Ok(Next::V(Rc::new(Val::Nat(Nat::small(lo, hi))))),
            ExprNode::NatBig(b) => Ok(Next::V(Rc::new(Val::Nat(Nat::big(
                self.tc.st.big(b).clone(),
            ))))),
            ExprNode::Str(_) => Ok(Next::V(Rc::new(Val::Str(e)))),
            ExprNode::FVar(_) => Err(stuck(268)),
            ExprNode::Sort(_) | ExprNode::Pi(..) => self.type_value(e, env).map(Next::V),
            ExprNode::Lam(..) => Ok(Next::V(Rc::new(Val::Clo {
                lam: e,
                env: env.clone(),
            }))),
            ExprNode::Let(h, b) => {
                let v = self.tc.st.let_binder(h).value;
                let t = self.thunk(v, env);
                let env2 = env.push(t);
                Ok(Next::Eval(b, env2))
            }
            ExprNode::Const(..) => self.constant_n(e, Vec::new()),
            ExprNode::Proj(s, i, x) => {
                let xv = self.eval(x, env)?;
                self.proj(s, i, xv).map(Next::V)
            }
            ExprNode::App(..) => {
                if !self.tc.st.has_loose_bvars(e) && !env.is_empty() {
                    // A closed application: share its value.
                    let t = self.closed(e);
                    return self.force(&t).map(Next::V);
                }
                let plan = match self.s.apps.get(&e) {
                    Some(p) => p.clone(),
                    None => self.app_plan(e),
                };
                let mut args = Vec::with_capacity(plan.args.len());
                for a in plan.args.iter() {
                    args.push(match a {
                        ArgPlan::Var(i) => env.get(*i).clone(),
                        ArgPlan::Closed(t) => t.clone(),
                        ArgPlan::Proof(a) if !self.s.keep_proofs => self.proof_thunk(*a, env),
                        ArgPlan::Proof(a) | ArgPlan::Delayed(a) => Thunk::delayed(*a, env.clone()),
                    });
                }
                let f = plan.head;
                if let Some(i) = &plan.info {
                    return self.constant_with(f, i.clone(), args);
                }
                match self.tc.st.node(f) {
                    ExprNode::Const(..) => self.constant_n(f, args),
                    ExprNode::Lam(..) => self.beta_n(f, env.clone(), args),
                    _ => {
                        let fv = self.eval(f, env)?;
                        self.apply_n(fv, args)
                    }
                }
            }
        }
    }

    /// The head of the application `e` and how to make each argument's
    /// thunk (what `thunk` does, decided once per term).
    #[inline(never)]
    fn app_plan(&mut self, e: ExprId) -> Rc<AppPlan> {
        let mut args = Vec::new();
        let mut g = e;
        while let ExprNode::App(h, a) = self.tc.st.node(g) {
            let p = if !self.tc.st.data(a).has_loose_bvars() {
                ArgPlan::Closed(self.closed(a))
            } else if let ExprNode::BVar(i) = self.tc.st.node(a) {
                ArgPlan::Var(i)
            } else if self.is_proof(a) {
                ArgPlan::Proof(a)
            } else {
                ArgPlan::Delayed(a)
            };
            args.push(p);
            g = h;
        }
        args.reverse();
        let info = match self.tc.st.node(g) {
            ExprNode::Const(..) => Some(self.info(g)),
            _ => None,
        };
        let p = Rc::new(AppPlan {
            info,
            head: g,
            args: args.into_boxed_slice(),
        });
        self.s.apps.insert(e, p.clone());
        p
    }

    /// A sort or a Pi: in weak head normal form already.
    #[inline(never)]
    fn type_value(&mut self, e: ExprId, env: &Env) -> ER<V> {
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

    #[inline(never)]
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
                let value = match self.tc.value(&d) {
                    Ok(v) => v.unwrap_or(value),
                    Err(e) => panic!("{e}"),
                };
                let v = self.inst_levels(&d, ls, value);
                if ls == LevelList::EMPTY
                    && let Some(op) = ext.nat_op(n)
                {
                    return CInfo::Op(op, v);
                }
                if let Some(&op) = ext.array_ops.get(&n) {
                    return CInfo::Arr(op, v);
                }
                if let Some(&op) = ext.list_ops.get(&n) {
                    return CInfo::List(op, v);
                }
                if let Some(&op) = ext.dec_eq_ops.get(&n) {
                    return CInfo::DecEq(op, v);
                }
                if Some(n) == ext.beq_prod {
                    return CInfo::BEqProd(v);
                }
                if let Some(&op) = ext.int_ops.get(&n) {
                    return CInfo::Int(op, v);
                }
                let k = proj_fn_arity(&self.tc.st, v);
                if k == 0
                    && let Some(ci) = shape::cases_shape(self, v)
                {
                    return CInfo::Cases(Rc::new(ci), v);
                }
                if k == 0
                    && let Some(t) = shape::tree_shape(self, v)
                {
                    return CInfo::Tree(Rc::new(t), v);
                }
                CInfo::Unfold(v, k)
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
                    single: num_motives == 1 && num_minors as usize == rs.len(),
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
        let n = self.constant_n(c, args)?;
        self.finish(n)
    }

    fn constant_n(&mut self, c: ExprId, args: Vec<Th>) -> ER<Next> {
        let i = self.info(c);
        self.constant_with(c, i, args)
    }

    /// `constant_n` with the constant's `info` at hand.
    fn constant_with(&mut self, c: ExprId, info: CInfo, args: Vec<Th>) -> ER<Next> {
        if let Some(p) = self.s.profile.as_mut() {
            *p.entry(c).or_default() += 1;
        }
        match info {
            CInfo::Unfold(v, k) => self.unfold_n(c, v, k, args),
            CInfo::Op(op, _) => self.saturate_n(c, Head::Op(op), args),
            CInfo::Succ => self.saturate_n(c, Head::Succ, args),
            CInfo::Rec(r) => self.saturate_n(c, Head::Rec(r), args),
            CInfo::QuotLift => self.saturate_n(c, Head::QuotLift, args),
            CInfo::QuotInd => self.saturate_n(c, Head::QuotInd, args),
            CInfo::Arr(op, v) => self.saturate_n(c, Head::Arr(op, v), args),
            CInfo::List(op, v) => self.saturate_n(c, Head::List(op, v), args),
            CInfo::DecEq(op, v) => self.saturate_n(c, Head::DecEq(op, v), args),
            CInfo::BEqProd(v) => self.saturate_n(c, Head::BEqProd(v), args),
            CInfo::Int(op, v) => self.saturate_n(c, Head::Int(op, v), args),
            CInfo::Cases(ci, v) => self.saturate_n(c, Head::Cases(ci, v), args),
            CInfo::Tree(t, v) => self.saturate_n(c, Head::Tree(t, v), args),
            CInfo::Ctor(info) if args.is_empty() => {
                // One shared value per constructor constant.
                if let Some(v) = self.s.nullary.get(&c) {
                    return Ok(Next::V(v.clone()));
                }
                let v = Rc::new(Val::Ctor { c, info, args });
                self.s.nullary.insert(c, v.clone());
                Ok(Next::V(v))
            }
            CInfo::Ctor(info) => Ok(Next::V(Rc::new(Val::Ctor { c, info, args }))),
            CInfo::Neutral => Ok(Next::V(Rc::new(Val::Neutral { head: c, args }))),
            CInfo::Bail => Err(stuck(444)),
        }
    }

    /// The definition `c`, of value `v`, applied to `args` (see
    /// `CInfo::Unfold`). Not inlined into `constant_n`, which is on the
    /// stack at every recursor reduction.
    #[inline(never)]
    fn unfold_n(&mut self, c: ExprId, v: ExprId, k: u32, args: Vec<Th>) -> ER<Next> {
        let k = k as usize;
        if k > 0 && args.len() > k {
            return self.method_n(c, v, k, args);
        }
        let t = self.closed(v);
        let f = self.force(&t)?;
        if args.is_empty() {
            return Ok(Next::V(f));
        }
        // Arguments that are all known terms: this is the closed
        // term `c a₁ … aₙ`, whose value is shared through its id,
        // as `whnf`'s cache shares it after substitution.
        // Building the key costs a term; constants whose keys
        // rarely hit are not memoized any more.
        let st = self.s.memo.entry(c).or_default();
        if st.0 >= MEMO_TRIAL && st.1 * MEMO_RATIO < st.0 {
            return self.apply_n(f, args);
        }
        st.0 += 1;
        self.memo_app(c, f, args)
    }

    #[inline(never)]
    fn memo_app(&mut self, c: ExprId, f: V, args: Vec<Th>) -> ER<Next> {
        let Some(key) = self.closed_app(c, &args) else {
            return self.apply_n(f, args);
        };
        let kt = self.closed(key);
        let st = self.s.memo.entry(c).or_default();
        if let TState::Done(v) = &*kt.0.borrow() {
            st.1 += 1;
            return Ok(Next::V(v.clone()));
        }
        let v = self.apply(f, args)?;
        let mut b = kt.0.borrow_mut();
        if let TState::Delayed(..) = &*b {
            *b = TState::Done(v.clone());
        }
        Ok(Next::V(v))
    }

    /// The projection function `c` (with value `v`, `fun p₁ … pₖ self =>
    /// self.i`) applied to more than `k` arguments: a class method such as
    /// `HAdd.hAdd α β γ inst x y`. The value of `c p₁ … pₖ`, the
    /// instance's field, is kept per argument thunks (the same thunks
    /// stand for the same terms), and the rest of the arguments are
    /// applied to it, as `whnf` does after unfolding `c` and projecting.
    fn method_n(&mut self, c: ExprId, v: ExprId, k: usize, mut args: Vec<Th>) -> ER<Next> {
        let rest = args.split_off(k);
        let hit = self.s.methods.get(&c).and_then(|es| {
            es.iter()
                .find(|(ps, _)| ps.iter().zip(&args).all(|(p, a)| Rc::ptr_eq(p, a)))
                .map(|(_, f)| f.clone())
        });
        let f = match hit {
            Some(f) => {
                self.s.fast[4] += 1;
                f
            }
            None => self.method_miss(c, v, args, rest.len())?,
        };
        self.apply_n(f, rest)
    }

    #[inline(never)]
    fn method_miss(&mut self, c: ExprId, v: ExprId, args: Vec<Th>, rest: usize) -> ER<V> {
        let mut f = match self.closed_app(c, &args) {
            Some(key) => {
                let t = self.closed(key);
                self.force(&t)?
            }
            None => {
                let t = self.closed(v);
                let u = self.force(&t)?;
                self.apply(u, args.clone())?
            }
        };
        for _ in 0..4 {
            match self.eta_head(&f, rest)? {
                Some(g) => f = g,
                None => break,
            }
        }
        let es = self.s.methods.entry(c).or_default();
        let e = (args.into_boxed_slice(), f.clone());
        if es.len() < METHOD_CACHE {
            es.push(e);
        } else {
            // Replace the oldest.
            es.remove(0);
            es.push(e);
        }
        Ok(f)
    }

    /// The value of `g` if `f` is `fun x₁ … xₘ => g x₁ … xₘ` where `g` does
    /// not use the `xᵢ` and `m ≤ n`: then `f` applied to `n` arguments is
    /// `g` applied to them, and `g` is evaluated as soon as `f` is. A
    /// method such as `HMul.hMul` at `instHMul` is `fun a b => Mul.mul a b`,
    /// so this goes straight to the multiplication.
    fn eta_head(&mut self, f: &V, n: usize) -> ER<Option<V>> {
        let Val::Clo { lam, env } = &**f else {
            return Ok(None);
        };
        let st = &self.tc.st;
        let mut b = *lam;
        let mut m = 0u32;
        while let ExprNode::Lam(_, _, _, body) = st.node(b) {
            m += 1;
            b = body;
        }
        if m as usize > n {
            return Ok(None);
        }
        let mut g = b;
        for j in 0..m {
            match st.node(g) {
                ExprNode::App(h, a) if matches!(st.node(a), ExprNode::BVar(i) if i == j) => g = h,
                _ => return Ok(None),
            }
        }
        if (0..m).any(|j| st.has_loose_bvar(g, j)) {
            return Ok(None);
        }
        let g = self.tc.st.lower_loose(g, m, m);
        let env = env.clone();
        let t = self.thunk(g, &env);
        Ok(Some(self.force(&t)?))
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
    fn saturate_n(&mut self, c: ExprId, kind: Head, args: Vec<Th>) -> ER<Next> {
        if args.len() >= kind.arity() {
            match &kind {
                Head::Rec(r) => {
                    let r = r.clone();
                    return self.iota_n(&r, args);
                }
                Head::Cases(ci, v) => {
                    let (ci, v) = (ci.clone(), *v);
                    return self.cases_n(&ci, v, args);
                }
                Head::Tree(t, v) => {
                    let (t, v) = (t.clone(), *v);
                    return self.tree_n(&t, v, args);
                }
                _ => {}
            }
        }
        self.saturate(c, kind, args).map(Next::V)
    }

    // Not inlined into `saturate_n`, which is on the stack at every
    // recursor reduction: its frame would be this one's size.
    #[inline(never)]
    fn saturate(&mut self, c: ExprId, kind: Head, args: Vec<Th>) -> ER<V> {
        if args.len() < kind.arity() {
            return Ok(Rc::new(Val::Pap {
                head: c,
                kind,
                args,
            }));
        }
        match kind {
            Head::Succ => self.succ_head(args),
            Head::Op(op) => self.nat_head(c, op, args),
            Head::Rec(r) => {
                let n = self.iota_n(&r, args)?;
                self.finish(n)
            }
            Head::Arr(op, def) => self.array_op(c, op, def, args),
            Head::List(op, def) => self.list_op(c, op, def, args),
            Head::DecEq(op, def) => self.dec_eq_op(c, op, def, args),
            Head::BEqProd(def) => self.beq_prod(def, args),
            Head::BEqProdFn => self.beq_prod_fn(c, args),
            Head::Int(op, def) => self.int_op(op, def, args),
            Head::QuotLift | Head::QuotInd => self.quot_head(matches!(kind, Head::QuotLift), args),
            Head::Cases(ci, v) => {
                let n = self.cases_n(&ci, v, args)?;
                self.finish(n)
            }
            Head::Tree(t, v) => {
                let n = self.tree_n(&t, v, args)?;
                self.finish(n)
            }
        }
    }

    #[inline(never)]
    fn succ_head(&mut self, args: Vec<Th>) -> ER<V> {
        let mut args = args;
        let x = self.force(&args[0])?;
        let rest = args.split_off(1);
        let r = match self.nat_of(&x) {
            Some(n) => Rc::new(Val::Nat(n.succ())),
            None => return Err(stuck(518)),
        };
        self.apply_rest(r, rest)
    }

    #[inline(never)]
    fn nat_head(&mut self, c: ExprId, op: NatOp, args: Vec<Th>) -> ER<V> {
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

    #[inline(never)]
    fn quot_head(&mut self, lift: bool, args: Vec<Th>) -> ER<V> {
        let (mk_pos, arg_pos) = if lift { (5, 3) } else { (4, 3) };
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
    /// The value of a tail call.
    fn finish(&mut self, n: Next) -> ER<V> {
        match n {
            Next::V(v) => Ok(v),
            Next::Eval(e, env) => self.eval(e, &env),
        }
    }

    fn beta_n(&mut self, mut lam: ExprId, env: Env, mut args: Vec<Th>) -> ER<Next> {
        let mut i = 0;
        while i < args.len()
            && let ExprNode::Lam(_, _, _, b) = self.tc.st.node(lam)
        {
            lam = b;
            i += 1;
        }
        if i == 0 {
            let v = self.eval(lam, &env)?;
            return self.apply_n(v, args);
        }
        let rest = args.split_off(i);
        let env = env.push_all(args);
        if rest.is_empty() {
            return Ok(Next::Eval(lam, env));
        }
        let v = self.eval(lam, &env)?;
        self.apply_n(v, rest)
    }

    fn apply(&mut self, f: V, args: Vec<Th>) -> ER<V> {
        let n = self.apply_n(f, args)?;
        self.finish(n)
    }

    fn apply_n(&mut self, f: V, args: Vec<Th>) -> ER<Next> {
        if args.is_empty() {
            return Ok(Next::V(f));
        }
        match &*f {
            Val::Clo { lam, env } => self.beta_n(*lam, env.clone(), args),
            Val::Pap {
                head,
                kind,
                args: a0,
            } => {
                let mut a = a0.clone();
                a.extend(args);
                self.saturate_n(*head, kind.clone(), a)
            }
            _ => self.apply_data(f, args).map(Next::V),
        }
    }

    /// A constructor or a neutral term applied to more arguments.
    #[inline(never)]
    fn apply_data(&mut self, f: V, args: Vec<Th>) -> ER<V> {
        match &*f {
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
            _ => Err(stuck(667)),
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
    fn iota_n(&mut self, r: &RecInfo, args: Vec<Th>) -> ER<Next> {
        let mut major = args[r.major_idx].clone();
        if r.k {
            major = self.k_major(r, major)?;
        }
        let mut mv = self.force(&major)?;
        if matches!(&*mv, Val::Nat(_) | Val::Str(_) | Val::Arr(_)) {
            mv = self.as_ctor(mv)?;
        }
        let Val::Ctor { c, args: margs, .. } = &*mv else {
            self.stuck_major(r, &mv);
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
        let fields = &margs[margs.len() - nfields..];
        if let Some(ri) = self.rule_info(rhs, r.pmm, nfields) {
            // The minor premise applied to the fields, the inductive
            // hypotheses and the rest: the rule's body, without its step.
            let f = self.force(&args[ri.0])?;
            let mut call = Vec::with_capacity(nfields + ri.1.len() + args.len() - r.major_idx - 1);
            call.extend_from_slice(fields);
            if !ri.1.is_empty() {
                let mut ts = Vec::with_capacity(r.pmm + nfields);
                ts.extend_from_slice(&args[..r.pmm]);
                ts.extend_from_slice(fields);
                let env = Env::EMPTY.push_all(ts);
                for &ih in ri.1.iter() {
                    call.push(self.thunk(ih, &env));
                }
            }
            call.extend_from_slice(&args[r.major_idx + 1..]);
            return self.apply_n(f, call);
        }
        let mut a = Vec::with_capacity(r.pmm + nfields + args.len() - r.major_idx - 1);
        a.extend_from_slice(&args[..r.pmm]);
        a.extend_from_slice(fields);
        a.extend_from_slice(&args[r.major_idx + 1..]);
        let t = self.closed(rhs);
        let f = self.force(&t)?;
        self.apply_n(f, a)
    }

    /// For a recursor rule `fun x₁ … xₙ y₁ … y_f => m y₁ … y_f ih₁ … ihᵣ`
    /// (`n` the parameters, motives and minor premises, `m` one of the
    /// minor premises): the index of `m` and the terms `ihᵢ` (in the
    /// environment of the `n + f` binders).
    fn rule_info(&mut self, rhs: ExprId, n: usize, nf: usize) -> Option<Rc<RuleInfo>> {
        if let Some(r) = self.s.rules.get(&rhs) {
            return r.clone();
        }
        let r = self.compute_rule_info(rhs, n, nf).map(Rc::new);
        self.s.rules.insert(rhs, r.clone());
        r
    }

    #[inline(never)]
    fn compute_rule_info(
        &mut self,
        rhs: ExprId,
        n: usize,
        nf: usize,
    ) -> Option<(usize, Box<[ExprId]>)> {
        let st = &self.tc.st;
        let mut e = rhs;
        for _ in 0..n + nf {
            let ExprNode::Lam(_, _, _, b) = st.node(e) else {
                return None;
            };
            e = b;
        }
        let mut a = Vec::new();
        let h = st.spine(e, &mut a);
        let ExprNode::BVar(j) = st.node(h) else {
            return None;
        };
        let m = (n + nf).checked_sub(1 + j as usize)?;
        if m >= n || a.len() < nf {
            return None;
        }
        for (f, &x) in a[..nf].iter().enumerate() {
            if !matches!(st.node(x), ExprNode::BVar(i) if i as usize == nf - 1 - f) {
                return None;
            }
        }
        Some((m, a[nf..].to_vec().into_boxed_slice()))
    }

    /// A `casesOn` applied to (at least) its arguments, with its major
    /// premise a constructor: the argument for that constructor applied to
    /// its fields (and the rest). That is what unfolding the definition and
    /// reducing the recursor give: the rule's right-hand side applied to
    /// the fields and inductive hypotheses, then the wrapper `fun fields
    /// ihs => x_m fields`. Else the definition.
    fn cases_n(&mut self, ci: &CasesInfo, v: ExprId, mut args: Vec<Th>) -> ER<Next> {
        let mut mv = self.force(&args[ci.major])?;
        if matches!(&*mv, Val::Nat(_) | Val::Str(_) | Val::Arr(_)) {
            mv = self.as_ctor(mv)?;
        }
        if let Val::Ctor { c, args: margs, .. } = &*mv
            && let ExprNode::Const(cn, _) = self.tc.st.node(*c)
            && let Some((_, nf, e, minor)) = ci.rules.iter().find(|r| r.0 == cn)
            && *nf as usize <= margs.len()
            && args.len() >= ci.arity + *e as usize
        {
            self.s.fast[5] += 1;
            let (nf, e) = (*nf as usize, *e as usize);
            let mut rest = args.split_off(ci.arity);
            let tail = rest.split_off(e);
            let (f, mut a) = match minor {
                Minor::Arg(l) => {
                    let f = self.force(&args[*l])?;
                    (f, margs[margs.len() - nf..].to_vec())
                }
                Minor::Extra(j, ts) => {
                    let f = self.force(&rest[*j as usize])?;
                    (f, ts.iter().map(|&t| self.closed(t)).collect())
                }
                Minor::Closed(t) => {
                    let t = self.closed(*t);
                    (self.force(&t)?, Vec::new())
                }
                Minor::Var(l) => (self.force(&args[*l])?, Vec::new()),
            };
            a.extend(tail);
            return self.apply_n(f, a);
        }
        let t = self.closed(v);
        let f = self.force(&t)?;
        self.apply_n(f, args)
    }

    fn src(&mut self, s: Src, args: &[Th], levels: &[(Th, Vec<Th>)]) -> Th {
        match s {
            Src::Arg(i) => args[i].clone(),
            Src::Field(l, f) => levels[l].1[f].clone(),
            Src::Major(l) => levels[l].0.clone(),
            Src::Closed(e) => self.closed(e),
        }
    }

    /// A matcher of nested `casesOn`s applied to (at least) its arguments:
    /// down the tree while the values matched are constructors of its
    /// rules, to a leaf. Else the definition.
    fn tree_n(&mut self, ti: &TreeInfo, v: ExprId, mut args: Vec<Th>) -> ER<Next> {
        let tail = args.split_off(ti.arity);
        let mut levels: Vec<(Th, Vec<Th>)> = Vec::new();
        let mut t = &ti.tree;
        loop {
            match t {
                Tree::Leaf(h, xs) => {
                    self.s.fast[5] += 1;
                    let h = self.src(*h, &args, &levels);
                    let f = self.force(&h)?;
                    let mut call = Vec::with_capacity(xs.len() + tail.len());
                    for &x in xs.iter() {
                        call.push(self.src(x, &args, &levels));
                    }
                    call.extend(tail);
                    return self.apply_n(f, call);
                }
                Tree::Case(m, rules) => {
                    let th = self.src(*m, &args, &levels);
                    let mut mv = self.force(&th)?;
                    if matches!(&*mv, Val::Nat(_) | Val::Str(_) | Val::Arr(_)) {
                        mv = self.as_ctor(mv)?;
                    }
                    let next = match &*mv {
                        Val::Ctor { c, args: margs, .. } => match self.tc.st.node(*c) {
                            ExprNode::Const(cn, _) => rules
                                .iter()
                                .find(|r| r.0 == cn && r.1 as usize <= margs.len())
                                .map(|r| (r, margs[margs.len() - r.1 as usize..].to_vec())),
                            _ => None,
                        },
                        _ => None,
                    };
                    let Some((r, fields)) = next else {
                        break;
                    };
                    levels.push((th, fields));
                    t = &r.2;
                }
            }
        }
        args.extend(tail);
        let t = self.closed(v);
        let f = self.force(&t)?;
        self.apply_n(f, args)
    }

    /// As Lean does, before reducing a `K`-like recursor's major premise:
    /// if its type is the type of the constructor (built from the
    /// parameters), use the constructor.
    #[inline(never)]
    fn k_major(&mut self, r: &RecInfo, major: Th) -> ER<Th> {
        let mut rb = value::Readback::default();
        let m = rb.thunk(self.tc, &major);
        if rb.erased {
            return Err(Bail::Erased);
        }
        let c = self
            .tc
            .ctor_when_k_pub(r.induct, r.nparams, m)
            .map_err(|_| Bail::Stuck)?;
        Ok(if c != m { self.closed(c) } else { major })
    }

    /// A literal, string or array value as a constructor application.
    #[inline(never)]
    fn as_ctor(&mut self, v: V) -> ER<V> {
        match &*v {
            Val::Nat(n) => self.nat_ctor(n),
            Val::Str(e) => {
                let e = *e;
                self.string_ctor(e)
            }
            Val::Arr(a) => {
                let a = a.clone();
                self.array_ctor(&a)
            }
            _ => Ok(v),
        }
    }

    #[cold]
    #[inline(never)]
    fn stuck_major(&mut self, r: &RecInfo, mv: &V) {
        if std::env::var_os("NITROLEAN_EVAL_DEBUG").is_some() {
            let mut rb = value::Readback::default();
            let x = rb.value(self.tc, mv);
            eprintln!(
                "evaluator: stuck major of a recursor on {}: {}",
                self.tc.show(r.induct),
                self.tc.pp(x).chars().take(400).collect::<String>()
            );
        }
    }

    /// An `Array` operation applied to (at least) its arguments: on a
    /// vector if the array is one or is `Array.mk` of a list built to its
    /// end, else by its definition.
    #[inline(never)]
    fn array_op(&mut self, c: ExprId, op: ArrayOp, def: ExprId, mut args: Vec<Th>) -> ER<V> {
        let n = Head::Arr(op, def).arity();
        let rest = args.split_off(n);
        let r = match self.array_arg(c, &args[1])? {
            None => None,
            Some(a) => match op {
                ArrayOp::Size => Some(Rc::new(Val::Nat(Nat::Small(ArrVal::len(&a) as u64)))),
                ArrayOp::Push => Some(Rc::new(Val::Arr(
                    self.s.array(ArrVal::push(&a, args[2].clone())),
                ))),
                ArrayOp::Get | ArrayOp::Set => {
                    let i = self.force(&args[2])?;
                    match self.nat_of(&i) {
                        Some(Nat::Small(i)) if op == ArrayOp::Get => {
                            match ArrVal::get(&a, i as usize) {
                                Some(t) => Some(self.force(&t)?),
                                None => None,
                            }
                        }
                        Some(Nat::Small(i)) => ArrVal::set(&a, i as usize, args[3].clone())
                            .map(|b| Rc::new(Val::Arr(self.s.array(b)))),
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
        let a = self.s.array(ArrVal::new(mk, cons, nil, ty, elems));
        // The vector stands for the same term: later operations on this
        // thunk need not walk the list again.
        if let TState::Done(_) = &*t.0.borrow() {
        } else {
            return Ok(Some(a));
        }
        *t.0.borrow_mut() = TState::Done(Rc::new(Val::Arr(a.clone())));
        Ok(Some(a))
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
    fn array_ctor(&mut self, a: &Rc<ArrVal>) -> ER<V> {
        let nil_info = self.ctor_info(a.nil)?;
        let cons_info = self.ctor_info(a.cons)?;
        let mk_info = self.ctor_info(a.mk)?;
        let mut l = Rc::new(Val::Ctor {
            c: a.nil,
            info: nil_info,
            args: vec![a.ty.clone()],
        });
        for e in ArrVal::with(a, |v| v.to_vec()).iter().rev() {
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

    /// `instBEqProd α β bα bβ`: the definition's `BEq.mk T f`, with the
    /// field `f` held as `BEqProdFn` applied to `α β bα bβ`, whose head is
    /// the term `fun α β bα bβ => f` (so it stands for `f`, by beta).
    #[inline(never)]
    fn beq_prod(&mut self, def: ExprId, mut args: Vec<Th>) -> ER<V> {
        let rest = args.split_off(4);
        let head = match self.s.beq_fields.get(&def) {
            Some(&h) => h,
            None => {
                let h = self.beq_field(def);
                self.s.beq_fields.insert(def, h);
                h
            }
        };
        let v = self.unfold_def(def, args.clone())?;
        let v = match (&*v, head) {
            (Val::Ctor { c, info, args: a }, Some(head)) if a.len() == 2 => {
                let f = Rc::new(Val::Pap {
                    head,
                    kind: Head::BEqProdFn,
                    args,
                });
                Rc::new(Val::Ctor {
                    c: *c,
                    info: info.clone(),
                    args: vec![a[0].clone(), Thunk::done(f)],
                })
            }
            _ => v,
        };
        self.apply_rest(v, rest)
    }

    /// `fun α β bα bβ => f` for the definition `fun α β bα bβ => BEq.mk T f`.
    fn beq_field(&mut self, def: ExprId) -> Option<ExprId> {
        let beq = self.tc.ext.fast?.beq?;
        let mut binders = Vec::new();
        let mut e = def;
        for _ in 0..4 {
            let ExprNode::Lam(bi, n, t, b) = self.tc.st.node(e) else {
                return None;
            };
            binders.push((bi, n, t));
            e = b;
        }
        let ExprNode::App(mk_t, f) = self.tc.st.node(e) else {
            return None;
        };
        let ExprNode::App(mk, _) = self.tc.st.node(mk_t) else {
            return None;
        };
        let ExprNode::Const(m, _) = self.tc.st.node(mk) else {
            return None;
        };
        match self.tc.find(m).map(|d| d.kind) {
            Some(DeclKind::Constructor { induct, .. }) if induct == beq => {}
            _ => return None,
        }
        let mut r = f;
        for &(bi, n, t) in binders.iter().rev() {
            r = self.tc.st.lam(bi, n, t, r);
        }
        Some(r)
    }

    /// `(a₁, b₁) == (a₂, b₂)` by `instBEqProd α β bα bβ`: `a₁ == a₂ && b₁ ==
    /// b₂`, forcing what the definition forces, in its order. `head` is
    /// the term the field stands for, used where the arguments are not
    /// pairs or the comparisons not booleans.
    #[inline(never)]
    fn beq_prod_fn(&mut self, head: ExprId, mut args: Vec<Th>) -> ER<V> {
        let rest = args.split_off(6);
        let r = match self.beq_prod_fast(&args)? {
            Some(b) => {
                self.s.fast[2] += 1;
                self.mk_bool(b)?
            }
            None => {
                let t = self.closed(head);
                let f = self.force(&t)?;
                self.apply(f, args)?
            }
        };
        self.apply_rest(r, rest)
    }

    fn beq_prod_fast(&mut self, args: &[Th]) -> ER<Option<bool>> {
        let Some(f) = self.tc.ext.fast else {
            return Ok(None);
        };
        let (Some(prod), Some(beq)) = (f.prod, f.beq) else {
            return Ok(None);
        };
        let x = self.force(&args[4])?;
        let Some(xs) = struct_fields(&x, prod) else {
            return Ok(None);
        };
        let y = self.force(&args[5])?;
        let Some(ys) = struct_fields(&y, prod) else {
            return Ok(None);
        };
        for i in 0..2 {
            // `BEq.beq bα a₁ a₂`: the instance's field, applied.
            let inst = self.force(&args[2 + i])?;
            let field = match &*inst {
                Val::Ctor { info, args: a, .. } if info.induct == beq && a.len() == 2 => {
                    a[1].clone()
                }
                _ => return Ok(None),
            };
            let g = self.force(&field)?;
            let b = self.apply(g, vec![xs[i].clone(), ys[i].clone()])?;
            match self.bool_of(&b) {
                Some(true) => {}
                Some(false) => return Ok(Some(false)),
                None => return Ok(None),
            }
        }
        Ok(Some(true))
    }

    /// An `Int` operation applied to (at least) its arguments: on values
    /// `Int.ofNat n` and `Int.negSucc n` with literal `n` (and on literals,
    /// for the `Nat` arguments), by its definition's cases; else it is its
    /// definition. It forces each argument, as the definitions' matches do,
    /// except the divisor of `emod` on `Int.ofNat m`, which the definition
    /// leaves under `Int.ofNat`; that one is forced here too.
    #[inline(never)]
    fn int_op(&mut self, op: IntOp, def: ExprId, mut args: Vec<Th>) -> ER<V> {
        let n = Head::Int(op, def).arity();
        let rest = args.split_off(n);
        let r = match self.int_fast(op, &args)? {
            Some(v) => {
                self.s.fast[3] += 1;
                v
            }
            None => self.unfold_def(def, args)?,
        };
        self.apply_rest(r, rest)
    }

    fn int_fast(&mut self, op: IntOp, args: &[Th]) -> ER<Option<V>> {
        use IntOp as I;
        // Arguments: an `Int` as (negative, n), standing for `n` or
        // `-(n + 1)`; a `Nat` as a literal.
        let nat_arg = |m: &mut Self, t: &Th| -> ER<Option<Nat>> {
            let v = m.force(t)?;
            Ok(m.nat_of(&v))
        };
        let x = match op {
            I::SubNatNat | I::NegOfNat => match nat_arg(self, &args[0])? {
                Some(n) => (false, n),
                None => return Ok(None),
            },
            _ => match self.int_arg(&args[0])? {
                Some(x) => x,
                None => return Ok(None),
            },
        };
        let y = match op {
            I::Neg | I::NegOfNat | I::NatAbs | I::ToNat => (false, Nat::ZERO),
            I::SubNatNat | I::Pow => match nat_arg(self, &args[1])? {
                Some(n) => (false, n),
                None => return Ok(None),
            },
            _ => match self.int_arg(&args[1])? {
                Some(y) => y,
                None => return Ok(None),
            },
        };
        let ((xn, a), (yn, b)) = (x, y);
        let one = Nat::Small(1);
        let r = match op {
            I::Add => self.int_add(xn, &a, yn, &b)?,
            I::Sub => {
                // `m + -n`.
                let (yn, b) = int_neg(yn, &b)?;
                self.int_add(xn, &a, yn, &b)?
            }
            I::Neg => {
                let (n, v) = int_neg(xn, &a)?;
                (n, v)
            }
            I::Mul => {
                let (a1, b1) = (int_abs(xn, &a)?, int_abs(yn, &b)?);
                let p = nat_bin(NatOp::Mul, &a1, &b1)?;
                if xn == yn { (false, p) } else { neg_of_nat(&p) }
            }
            I::Ediv => match (xn, yn) {
                (false, false) => (false, nat_bin(NatOp::Div, &a, &b)?),
                (false, true) => neg_of_nat(&nat_bin(NatOp::Div, &a, &b.succ())?),
                (true, false) if b == Nat::ZERO => (false, Nat::ZERO),
                (true, false) => (true, nat_bin(NatOp::Div, &a, &b)?),
                (true, true) => (false, nat_bin(NatOp::Div, &a, &b.succ())?.succ()),
            },
            I::Emod => {
                let m = int_abs(yn, &b)?;
                if xn {
                    // `subNatNat |n| (m % |n|).succ`.
                    let r = nat_bin(NatOp::Mod, &a, &m)?.succ();
                    sub_nat_nat(&m, &r)?
                } else {
                    (false, nat_bin(NatOp::Mod, &a, &m)?)
                }
            }
            I::Tdiv | I::Tmod => {
                let (a1, b1) = (int_abs(xn, &a)?, int_abs(yn, &b)?);
                if op == I::Tdiv {
                    let q = nat_bin(NatOp::Div, &a1, &b1)?;
                    if xn == yn { (false, q) } else { neg_of_nat(&q) }
                } else {
                    let r = nat_bin(NatOp::Mod, &a1, &b1)?;
                    if xn { neg_of_nat(&r) } else { (false, r) }
                }
            }
            I::Pow => {
                // `ofNat (m ^ n)`, or for `negSucc`: `±ofNat (|m| ^ n)` by
                // the parity of `n`.
                let p = nat_bin(NatOp::Pow, &int_abs(xn, &a)?, &b)?;
                let odd = nat_bin(NatOp::Mod, &b, &Nat::Small(2))? == one;
                if xn && odd {
                    neg_of_nat(&p)
                } else {
                    (false, p)
                }
            }
            I::SubNatNat => sub_nat_nat(&a, &b)?,
            I::NegOfNat => neg_of_nat(&a),
            I::NatAbs | I::ToNat => {
                let n = match (op, xn) {
                    (I::NatAbs, true) => a.succ(),
                    (I::ToNat, true) => Nat::ZERO,
                    _ => a,
                };
                return Ok(Some(Rc::new(Val::Nat(n))));
            }
        };
        self.mk_int(r.0, r.1).map(Some)
    }

    fn int_add(&mut self, xn: bool, a: &Nat, yn: bool, b: &Nat) -> ER<(bool, Nat)> {
        Ok(match (xn, yn) {
            (false, false) => (false, nat_bin(NatOp::Add, a, b)?),
            (false, true) => sub_nat_nat(a, &b.succ())?,
            (true, false) => sub_nat_nat(b, &a.succ())?,
            (true, true) => (true, nat_bin(NatOp::Add, a, b)?.succ()),
        })
    }

    /// The `Int` value `t` as (negative, n): `Int.ofNat n` is (false, n),
    /// `Int.negSucc n` (true, n).
    fn int_arg(&mut self, t: &Th) -> ER<Option<(bool, Nat)>> {
        let Some(f) = self.tc.ext.fast else {
            return Ok(None);
        };
        let (Some(int), Some(of_nat)) = (f.int, f.int_of_nat) else {
            return Ok(None);
        };
        let v = self.force(t)?;
        let (neg, a) = match &*v {
            Val::Ctor { c, info, args } if info.induct == int && args.len() == 1 => {
                let ExprNode::Const(n, _) = self.tc.st.node(*c) else {
                    return Ok(None);
                };
                (n != of_nat, args[0].clone())
            }
            _ => return Ok(None),
        };
        let a = self.force(&a)?;
        Ok(self.nat_of(&a).map(|a| (neg, a)))
    }

    /// `Int.ofNat n`, or `Int.negSucc n` if `neg`.
    fn mk_int(&mut self, neg: bool, n: Nat) -> ER<V> {
        let f = self.tc.ext.fast.ok_or(Bail::Stuck)?;
        let k = if neg { f.int_neg_succ } else { f.int_of_nat };
        let k = self.tc.st.cnst(k.ok_or(Bail::Stuck)?, LevelList::EMPTY);
        let info = self.ctor_info(k)?;
        Ok(Rc::new(Val::Ctor {
            c: k,
            info,
            args: vec![Thunk::done(Rc::new(Val::Nat(n)))],
        }))
    }

    /// The definition `def` of an operation applied to `args`: what the
    /// operation is when the fast path does not apply.
    fn unfold_def(&mut self, def: ExprId, args: Vec<Th>) -> ER<V> {
        let t = self.closed(def);
        let f = self.force(&t)?;
        self.apply(f, args)
    }

    /// The list value `v` as `Some((head, tail))` for a cons, `None` for
    /// nil; `Err(())` if it is neither (not a constructor of `List`).
    fn list_cell(&self, v: &V) -> Result<Option<(Th, Th)>, ()> {
        let Some(f) = self.tc.ext.fast.as_ref() else {
            return Err(());
        };
        match &**v {
            Val::Ctor { info, args, .. } if info.induct == f.list => match args.len() {
                3 => Ok(Some((args[1].clone(), args[2].clone()))),
                1 => Ok(None),
                _ => Err(()),
            },
            _ => Err(()),
        }
    }

    /// `Bool.true` or `Bool.false` as a `bool`.
    fn bool_of(&self, v: &V) -> Option<bool> {
        let Val::Ctor { c, args, .. } = &**v else {
            return None;
        };
        if !args.is_empty() {
            return None;
        }
        let ExprNode::Const(n, _) = self.tc.st.node(*c) else {
            return None;
        };
        let ext = self.tc.ext;
        if Some(n) == ext.bool_true {
            Some(true)
        } else if Some(n) == ext.bool_false {
            Some(false)
        } else {
            None
        }
    }

    /// A `List` operation applied to (at least) its arguments, as a loop
    /// over the list. Each step forces what the definition's step forces,
    /// in the same order. If the list or a test is not a value of the
    /// expected kind, the operation is its definition (from the original
    /// arguments: what was forced stays evaluated).
    #[inline(never)]
    fn list_op(&mut self, c: ExprId, op: ListOp, def: ExprId, mut args: Vec<Th>) -> ER<V> {
        let n = Head::List(op, def).arity();
        let rest = args.split_off(n);
        let r = match self.list_fast(c, op, &args)? {
            Some(v) => {
                self.s.fast[0] += 1;
                v
            }
            None => self.unfold_def(def, args)?,
        };
        self.apply_rest(r, rest)
    }

    fn list_fast(&mut self, c: ExprId, op: ListOp, args: &[Th]) -> ER<Option<V>> {
        match op {
            ListOp::Any | ListOp::All => {
                // `any [] p = false`, `any (x :: l) p = p x || any l p`;
                // `all` with `&&` and `true`.
                let stop = op == ListOp::Any;
                let mut l = args[1].clone();
                loop {
                    let lv = self.force(&l)?;
                    let Ok(cell) = self.list_cell(&lv) else {
                        return Ok(None);
                    };
                    let Some((x, t)) = cell else {
                        return self.mk_bool(!stop).map(Some);
                    };
                    let p = self.force(&args[2])?;
                    let b = self.apply(p, vec![x])?;
                    match self.bool_of(&b) {
                        Some(b) if b == stop => return self.mk_bool(b).map(Some),
                        Some(_) => l = t,
                        None => return Ok(None),
                    }
                }
            }
            ListOp::Filter => {
                // `filter p [] = []`, `filter p (x :: l) = match p x with
                // | true => x :: filter p l | false => filter p l`: up to
                // the first element kept, whose tail is `filter p l`, lazy.
                let mut l = args[2].clone();
                loop {
                    let lv = self.force(&l)?;
                    let Ok(cell) = self.list_cell(&lv) else {
                        return Ok(None);
                    };
                    let Some((x, t)) = cell else {
                        return Ok(Some(lv));
                    };
                    let p = self.force(&args[1])?;
                    let b = self.apply(p, vec![x.clone()])?;
                    match self.bool_of(&b) {
                        Some(true) => {
                            let tail = self.op_app_thunk(c, &[args[0].clone(), args[1].clone(), t]);
                            return self.list_cons(c, &args[0], x, tail).map(Some);
                        }
                        Some(false) => l = t,
                        None => return Ok(None),
                    }
                }
            }
            ListOp::ReverseAux => {
                // `reverseAux [] r = r`, `reverseAux (x :: l) r =
                // reverseAux l (x :: r)`.
                let mut l = args[1].clone();
                let mut r = args[2].clone();
                loop {
                    let lv = self.force(&l)?;
                    let Ok(cell) = self.list_cell(&lv) else {
                        return Ok(None);
                    };
                    let Some((x, t)) = cell else {
                        return self.force(&r).map(Some);
                    };
                    r = Thunk::done(self.list_cons(c, &args[0], x, r)?);
                    l = t;
                }
            }
            ListOp::Foldl => {
                // `foldl f a [] = a`, `foldl f a (x :: l) = foldl f (f a x) l`,
                // with `f a x` a thunk, as in the definition.
                let f = args[2].clone();
                let mut a = args[3].clone();
                let mut l = args[4].clone();
                let body = self.apply2_body();
                loop {
                    let lv = self.force(&l)?;
                    let Ok(cell) = self.list_cell(&lv) else {
                        return Ok(None);
                    };
                    let Some((x, t)) = cell else {
                        return self.force(&a).map(Some);
                    };
                    a = Thunk::delayed(body, Env::EMPTY.push_all(vec![f.clone(), a, x]));
                    l = t;
                }
            }
            ListOp::Elem => {
                // `elem a [] = false`, `elem a (x :: l) = match a == x with
                // | true => true | false => elem a l`.
                let mut l = args[3].clone();
                loop {
                    let lv = self.force(&l)?;
                    let Ok(cell) = self.list_cell(&lv) else {
                        return Ok(None);
                    };
                    let Some((x, t)) = cell else {
                        return self.mk_bool(false).map(Some);
                    };
                    match self.beq_with(&args[1], &args[2], &x)? {
                        Some(true) => return self.mk_bool(true).map(Some),
                        Some(false) => l = t,
                        None => return Ok(None),
                    }
                }
            }
            ListOp::EraseDupsLoop => {
                // `loop r [] bs = bs.reverse`, `loop r (a :: l) bs = match
                // bs.any (r a) with | true => loop r l bs | false => loop
                // r l (a :: bs)`.
                let mut l = args[2].clone();
                let mut kept: Vec<Th> = Vec::new();
                let acc = args[3].clone();
                // `bs` is the kept elements, last first, on top of `acc`;
                // `any` runs over `bs`.
                loop {
                    let lv = self.force(&l)?;
                    let Ok(cell) = self.list_cell(&lv) else {
                        return Ok(None);
                    };
                    let Some((a, t)) = cell else {
                        break;
                    };
                    let mut found = false;
                    for y in kept.iter().rev() {
                        let r = self.force(&args[1])?;
                        let b = self.apply(r, vec![a.clone(), y.clone()])?;
                        match self.bool_of(&b) {
                            Some(true) => {
                                found = true;
                                break;
                            }
                            Some(false) => {}
                            None => return Ok(None),
                        }
                    }
                    if !found {
                        let mut m = acc.clone();
                        loop {
                            let mv = self.force(&m)?;
                            let Ok(cell) = self.list_cell(&mv) else {
                                return Ok(None);
                            };
                            let Some((y, t)) = cell else {
                                break;
                            };
                            let r = self.force(&args[1])?;
                            let b = self.apply(r, vec![a.clone(), y])?;
                            match self.bool_of(&b) {
                                Some(true) => {
                                    found = true;
                                    break;
                                }
                                Some(false) => m = t,
                                None => return Ok(None),
                            }
                        }
                    }
                    if !found {
                        kept.push(a);
                    }
                    l = t;
                }
                // `(kept reversed ++ acc).reverse`: `acc` reversed, then
                // `kept` in order.
                let mut accs = Vec::new();
                let mut m = acc;
                loop {
                    let mv = self.force(&m)?;
                    let Ok(cell) = self.list_cell(&mv) else {
                        return Ok(None);
                    };
                    let Some((y, t)) = cell else {
                        break;
                    };
                    accs.push(y);
                    m = t;
                }
                let mut r = Thunk::done(self.list_nil(c, &args[0])?);
                for x in kept.into_iter().rev().chain(accs) {
                    r = Thunk::done(self.list_cons(c, &args[0], x, r)?);
                }
                self.force(&r).map(Some)
            }
            ListOp::Map => {
                // `map f [] = []`, `map f (a :: l) = f a :: map f l`: the
                // head and the rest, lazily.
                let lv = self.force(&args[3])?;
                let Ok(cell) = self.list_cell(&lv) else {
                    return Ok(None);
                };
                let Some((a, t)) = cell else {
                    return self.list_nil_at(c, 1, &args[1]).map(Some);
                };
                let body = self.apply1_body();
                let x = Thunk::delayed(body, Env::EMPTY.push_all(vec![args[2].clone(), a]));
                let rest =
                    self.op_app_thunk(c, &[args[0].clone(), args[1].clone(), args[2].clone(), t]);
                self.list_cons_at(c, 1, &args[1], x, rest).map(Some)
            }
            ListOp::ZipWith => {
                // `zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys`,
                // else `[]`; the second list is forced only if the first
                // is a cons.
                let xv = self.force(&args[4])?;
                let Ok(cell) = self.list_cell(&xv) else {
                    return Ok(None);
                };
                let Some((x, xs)) = cell else {
                    return self.list_nil_at(c, 2, &args[2]).map(Some);
                };
                let yv = self.force(&args[5])?;
                let Ok(cell) = self.list_cell(&yv) else {
                    return Ok(None);
                };
                let Some((y, ys)) = cell else {
                    return self.list_nil_at(c, 2, &args[2]).map(Some);
                };
                let body = self.apply2_body();
                let h = Thunk::delayed(body, Env::EMPTY.push_all(vec![args[3].clone(), x, y]));
                let mut a: Vec<Th> = args[..4].to_vec();
                a.extend([xs, ys]);
                let rest = self.op_app_thunk(c, &a);
                self.list_cons_at(c, 2, &args[2], h, rest).map(Some)
            }
            ListOp::Append => {
                // `[] ++ bs = bs`, `(a :: as) ++ bs = a :: (as ++ bs)`.
                let lv = self.force(&args[1])?;
                let Ok(cell) = self.list_cell(&lv) else {
                    return Ok(None);
                };
                let Some((a, t)) = cell else {
                    return self.force(&args[2]).map(Some);
                };
                let rest = self.op_app_thunk(c, &[args[0].clone(), t, args[2].clone()]);
                self.list_cons(c, &args[0], a, rest).map(Some)
            }
            ListOp::Length => {
                // `length [] = 0`, `length (a :: l) = length l + 1`.
                let mut l = args[1].clone();
                let mut n: u64 = 0;
                loop {
                    let lv = self.force(&l)?;
                    let Ok(cell) = self.list_cell(&lv) else {
                        return Ok(None);
                    };
                    let Some((_, t)) = cell else {
                        return Ok(Some(Rc::new(Val::Nat(Nat::Small(n)))));
                    };
                    n += 1;
                    l = t;
                }
            }
            ListOp::GetLast => {
                // `getLast [x] h = x`, `getLast (x :: y :: l) h = getLast (y :: l) _`.
                let mut l = args[1].clone();
                let lv = self.force(&l)?;
                let Ok(Some((mut x, _))) = self.list_cell(&lv) else {
                    return Ok(None);
                };
                loop {
                    let lv = self.force(&l)?;
                    let Ok(Some((_, t))) = self.list_cell(&lv) else {
                        return Ok(None);
                    };
                    let tv = self.force(&t)?;
                    match self.list_cell(&tv) {
                        Ok(None) => return self.force(&x).map(Some),
                        Ok(Some((y, _))) => {
                            x = y;
                            l = t;
                        }
                        Err(()) => return Ok(None),
                    }
                }
            }
        }
    }

    /// The term `#1 #0` (a function applied to an argument).
    fn apply1_body(&mut self) -> ExprId {
        let st = &mut self.tc.st;
        let (b0, b1) = (st.bvar(0), st.bvar(1));
        st.app(b1, b0)
    }

    /// `List.nil α`, at the universe level `i` of the operation `c`.
    fn list_nil_at(&mut self, c: ExprId, i: usize, ty: &Th) -> ER<V> {
        let ls = self.list_level(c, i)?;
        let nil = self.tc.ext.fast.as_ref().ok_or(Bail::Stuck)?.list_nil;
        let k = self.tc.st.cnst(nil, ls);
        let info = self.ctor_info(k)?;
        Ok(Rc::new(Val::Ctor {
            c: k,
            info,
            args: vec![ty.clone()],
        }))
    }

    /// The term `#2 #1 #0` (a function applied to two arguments).
    fn apply2_body(&mut self) -> ExprId {
        let st = &mut self.tc.st;
        let (b0, b1, b2) = (st.bvar(0), st.bvar(1), st.bvar(2));
        st.apps(b2, &[b1, b0])
    }

    /// A thunk for the operation `c` applied to `args`: the term
    /// `c a₁ … aₙ`, delayed.
    fn op_app_thunk(&mut self, c: ExprId, args: &[Th]) -> Th {
        let n = args.len() as u32;
        let st = &mut self.tc.st;
        let mut e = c;
        for i in (0..n).rev() {
            let b = st.bvar(i);
            e = st.app(e, b);
        }
        Thunk::delayed(e, Env::EMPTY.push_all(args.to_vec()))
    }

    /// `bα.beq a b`, evaluated: `Some` if it is a `Bool`.
    fn beq_with(&mut self, inst: &Th, a: &Th, b: &Th) -> ER<Option<bool>> {
        let Some(beq) = self.tc.ext.fast.and_then(|f| f.beq) else {
            return Ok(None);
        };
        let i = self.force(inst)?;
        let field = match &*i {
            Val::Ctor { info, args, .. } if info.induct == beq && args.len() == 2 => {
                args[1].clone()
            }
            _ => return Ok(None),
        };
        let g = self.force(&field)?;
        let v = self.apply(g, vec![a.clone(), b.clone()])?;
        Ok(self.bool_of(&v))
    }

    /// `List.nil α`, at the universe level of the list operation `c`.
    fn list_nil(&mut self, c: ExprId, ty: &Th) -> ER<V> {
        let ls = self.list_level(c, 0)?;
        let nil = self.tc.ext.fast.as_ref().ok_or(Bail::Stuck)?.list_nil;
        let k = self.tc.st.cnst(nil, ls);
        let info = self.ctor_info(k)?;
        Ok(Rc::new(Val::Ctor {
            c: k,
            info,
            args: vec![ty.clone()],
        }))
    }

    /// The universe level `i` of the operation `c`, as a list of one.
    fn list_level(&mut self, c: ExprId, i: usize) -> ER<LevelList> {
        let ExprNode::Const(_, ls) = self.tc.st.node(c) else {
            return Err(stuck(0));
        };
        let l = *self.tc.st.list(ls).get(i).ok_or(Bail::Stuck)?;
        Ok(self.tc.st.mk_list(&[l]))
    }

    /// `List.cons α x l`, at the universe level of the list operation `c`.
    fn list_cons(&mut self, c: ExprId, ty: &Th, x: Th, l: Th) -> ER<V> {
        self.list_cons_at(c, 0, ty, x, l)
    }

    /// `List.cons α x l`, at the universe level `i` of the operation `c`.
    fn list_cons_at(&mut self, c: ExprId, i: usize, ty: &Th, x: Th, l: Th) -> ER<V> {
        let ls = self.list_level(c, i)?;
        let cons = self.tc.ext.fast.as_ref().ok_or(Bail::Stuck)?.list_cons;
        let k = self.tc.st.cnst(cons, ls);
        let info = self.ctor_info(k)?;
        Ok(Rc::new(Val::Ctor {
            c: k,
            info,
            args: vec![ty.clone(), x, l],
        }))
    }

    /// A `DecidableEq` instance applied to (at least) its arguments. It
    /// compares the values as the definition does (forcing the same things
    /// in the same order) and answers `isTrue (x = y) h` or `isFalse (x =
    /// y) h` (see `decision`).
    #[inline(never)]
    fn dec_eq_op(&mut self, c: ExprId, op: DecEqOp, def: ExprId, mut args: Vec<Th>) -> ER<V> {
        let n = Head::DecEq(op, def).arity();
        let rest = args.split_off(n);
        let r = self.dec_eq_fast(op, &args)?;
        let r = match r {
            Some(b) => match self.decision(c, b, &args) {
                Some(v) => {
                    self.s.fast[1] += 1;
                    v
                }
                None => self.unfold_def(def, args)?,
            },
            None => self.unfold_def(def, args)?,
        };
        self.apply_rest(r, rest)
    }

    fn dec_eq_fast(&mut self, op: DecEqOp, args: &[Th]) -> ER<Option<bool>> {
        let Some(f) = self.tc.ext.fast else {
            return Ok(None);
        };
        match op {
            DecEqOp::Nat => {
                // `match h : n.beq m with …`: both literals.
                let x = self.force(&args[0])?;
                let y = self.force(&args[1])?;
                Ok(match (self.nat_of(&x), self.nat_of(&y)) {
                    (Some(x), Some(y)) => Some(x == y),
                    _ => None,
                })
            }
            DecEqOp::Bool => {
                // `match a, b with …`.
                let x = self.force(&args[0])?;
                let Some(x) = self.bool_of(&x) else {
                    return Ok(None);
                };
                let y = self.force(&args[1])?;
                Ok(self.bool_of(&y).map(|y| x == y))
            }
            DecEqOp::Prod | DecEqOp::Subtype => {
                // `match x, y with | (a, b), (a', b') => match decEq a a' …`
                // (then `decEq b b'` if equal), or `| ⟨a, _⟩, ⟨b, _⟩ => if
                // h : a = b then … else …`.
                let (ind, i) = if op == DecEqOp::Prod {
                    (f.prod, 4)
                } else {
                    (f.subtype, 3)
                };
                let Some(ind) = ind else {
                    return Ok(None);
                };
                let x = self.force(&args[i])?;
                let Some(xs) = struct_fields(&x, ind) else {
                    return Ok(None);
                };
                let y = self.force(&args[i + 1])?;
                let Some(ys) = struct_fields(&y, ind) else {
                    return Ok(None);
                };
                let d = self.decide_with(&args[2], &xs[0], &ys[0])?;
                if op == DecEqOp::Subtype || d != Some(true) {
                    return Ok(d);
                }
                self.decide_with(&args[3], &xs[1], &ys[1])
            }
        }
    }

    /// The instance `inst` applied to `a` and `b`, evaluated: `Some` if it
    /// is `isTrue` or `isFalse`.
    fn decide_with(&mut self, inst: &Th, a: &Th, b: &Th) -> ER<Option<bool>> {
        let i = self.force(inst)?;
        let d = self.apply(i, vec![a.clone(), b.clone()])?;
        Ok(self.decision_of(&d))
    }

    fn decision_of(&self, v: &V) -> Option<bool> {
        let f = self.tc.ext.fast.as_ref()?;
        let Val::Ctor { c, args, .. } = &**v else {
            return None;
        };
        let ExprNode::Const(n, _) = self.tc.st.node(*c) else {
            return None;
        };
        if args.len() != 2 {
            None
        } else if Some(n) == f.is_true {
            Some(true)
        } else if Some(n) == f.is_false {
            Some(false)
        } else {
            None
        }
    }

    /// `isTrue p h` (or `isFalse p h`) for the `DecidableEq` operation `c`
    /// applied to `args`, where `p` is the proposition of its type. `h` is
    /// an erased proof: a run that needs it gives up and is done again
    /// keeping proofs, and then `h` is `of_decide_eq_true p (c args)
    /// (Eq.refl true)` (or `… false`).
    fn decision(&mut self, c: ExprId, b: bool, args: &[Th]) -> Option<V> {
        let p = match self.s.dec_props.get(&c) {
            Some(&p) => p,
            None => {
                let p = self.dec_prop(c, args.len());
                self.s.dec_props.insert(c, p);
                p
            }
        }?;
        let f = self.tc.ext.fast?;
        let k = if b { f.is_true? } else { f.is_false? };
        let k = self.tc.st.cnst(k, LevelList::EMPTY);
        let info = self.ctor_info(k).ok()?;
        let env = Env::EMPTY.push_all(args.to_vec());
        let h = if self.s.keep_proofs {
            // A run that keeps proofs gets one: `of_decide_eq_true p
            // (c x₁ … xₙ) (Eq.refl true)` (or `… false`), a proof of the
            // same proposition, so the same up to proof irrelevance.
            let h = self.decision_proof(c, b, p, args.len())?;
            Thunk::delayed(h, env.clone())
        } else {
            Thunk::erased(c, &Env::EMPTY)
        };
        let p = Thunk::delayed(p, env);
        Some(Rc::new(Val::Ctor {
            c: k,
            info,
            args: vec![p, h],
        }))
    }

    /// `of_decide_eq_true p (c #(n-1) … #0) (Eq.refl true)` (or the same
    /// with `false`), for the proposition `p` over `#(n-1) … #0`.
    #[inline(never)]
    fn decision_proof(&mut self, c: ExprId, b: bool, p: ExprId, n: usize) -> Option<ExprId> {
        let lemma = self.decide_lemma(b)?;
        let names = &self.tc.st.env.names;
        let (eq, bool_, bv) = (
            names.find_dotted("Eq.refl")?,
            names.find_dotted("Bool")?,
            names.find_dotted(if b { "Bool.true" } else { "Bool.false" })?,
        );
        let st = &mut self.tc.st;
        let one = st.succ(LevelId::ZERO);
        let one = st.mk_list(&[one]);
        let refl = st.cnst(eq, one);
        let bool_ = st.cnst(bool_, LevelList::EMPTY);
        let bv = st.cnst(bv, LevelList::EMPTY);
        let refl = st.apps(refl, &[bool_, bv]);
        let mut inst = c;
        for i in (0..n as u32).rev() {
            let x = st.bvar(i);
            inst = st.app(inst, x);
        }
        Some(st.apps(lemma, &[p, inst, refl]))
    }

    /// The proposition `p` of the type `Decidable p` of `c x₁ … xₙ`, with
    /// `xᵢ` as `#(n-i)`: from `c`'s type, by `whnf` through its binders.
    fn dec_prop(&mut self, c: ExprId, n: usize) -> Option<ExprId> {
        let dec = self.tc.ext.fast?.decidable?;
        let mut t = self.tc.infer(c).ok()?;
        let mut fvars = Vec::with_capacity(n);
        for _ in 0..n {
            t = self.tc.whnf(t).ok()?;
            let ExprNode::Pi(bi, name, dom, body) = self.tc.st.node(t) else {
                return None;
            };
            let x = self.tc.push_local(name, dom, None, bi);
            t = self.tc.st.instantiate(body, &[x]);
            fvars.push(x);
        }
        let t = self.tc.whnf(t).ok()?;
        let ExprNode::App(d, p) = self.tc.st.node(t) else {
            return None;
        };
        if !matches!(self.tc.st.node(d), ExprNode::Const(m, ls) if m == dec && ls == LevelList::EMPTY)
        {
            return None;
        }
        let mut e = self.tc.mk_lambda(&fvars, p);
        for _ in 0..n {
            let ExprNode::Lam(_, _, _, b) = self.tc.st.node(e) else {
                return None;
            };
            e = b;
        }
        Some(e)
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
        self.tc.st.charge_nat_unfold(n.bits());
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

/// A `Nat` operation with a `Nat` result.
/// `k` if `v` is `fun x₁ … xₖ => xₖ.i` (a projection function), else 0.
fn proj_fn_arity(st: &super::store::Store<'_>, v: ExprId) -> u32 {
    let mut e = v;
    let mut k = 0;
    while let ExprNode::Lam(_, _, _, b) = st.node(e) {
        k += 1;
        e = b;
    }
    match st.node(e) {
        ExprNode::Proj(_, _, x) if k > 0 && matches!(st.node(x), ExprNode::BVar(0)) => k,
        _ => 0,
    }
}

fn nat_bin(op: NatOp, x: &Nat, y: &Nat) -> ER<Nat> {
    match nat::op(op, x, y)? {
        nat::OpResult::Nat(n) => Ok(n),
        nat::OpResult::Bool(_) => Err(Bail::Stuck),
    }
}

/// `Int.subNatNat m n`: `match n - m with | 0 => ofNat (m - n) | k+1 =>
/// negSucc k`.
fn sub_nat_nat(m: &Nat, n: &Nat) -> ER<(bool, Nat)> {
    let k = nat_bin(NatOp::Sub, n, m)?;
    Ok(match k.pred() {
        None => (false, nat_bin(NatOp::Sub, m, n)?),
        Some(k) => (true, k),
    })
}

/// `Int.negOfNat n`: `0` or `negSucc (n - 1)`.
fn neg_of_nat(n: &Nat) -> (bool, Nat) {
    match n.pred() {
        None => (false, Nat::ZERO),
        Some(k) => (true, k),
    }
}

/// `Int.neg`: `ofNat n` to `negOfNat n`, `negSucc n` to `ofNat (n + 1)`.
fn int_neg(neg: bool, n: &Nat) -> ER<(bool, Nat)> {
    Ok(if neg {
        (false, n.succ())
    } else {
        neg_of_nat(n)
    })
}

/// `Int.natAbs`.
fn int_abs(neg: bool, n: &Nat) -> ER<Nat> {
    Ok(if neg { n.succ() } else { n.clone() })
}

/// The fields of `v`, a constructor of the structure `ind` (whose
/// constructor has two parameters and two fields).
fn struct_fields(v: &V, ind: NameId) -> Option<[Th; 2]> {
    match &**v {
        Val::Ctor { info, args, .. } if info.induct == ind && args.len() == 4 => {
            Some([args[2].clone(), args[3].clone()])
        }
        _ => None,
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
    List(ListOp, ExprId),
    DecEq(DecEqOp, ExprId),
    BEqProd(ExprId),
    /// The `==` of `instBEqProd α β bα bβ`; the head is the closed term
    /// `fun α β bα bβ => beq-field` (see `beq_prod`).
    BEqProdFn,
    Int(IntOp, ExprId),
    Cases(Rc<CasesInfo>, ExprId),
    Tree(Rc<TreeInfo>, ExprId),
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
            Head::List(ListOp::Foldl, _) => 5,
            Head::List(ListOp::Elem | ListOp::EraseDupsLoop | ListOp::Map, _) => 4,
            Head::List(ListOp::ZipWith, _) => 6,
            Head::List(ListOp::Length, _) => 2,
            Head::List(_, _) => 3,
            Head::DecEq(DecEqOp::Nat | DecEqOp::Bool, _) => 2,
            Head::DecEq(DecEqOp::Prod, _) => 6,
            Head::DecEq(DecEqOp::Subtype, _) => 5,
            Head::BEqProd(_) => 4,
            Head::BEqProdFn => 6,
            Head::Int(IntOp::Neg | IntOp::NegOfNat | IntOp::NatAbs | IntOp::ToNat, _) => 1,
            Head::Int(_, _) => 2,
            Head::Cases(ci, _) => ci.arity,
            Head::Tree(t, _) => t.arity,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// An array version whose newer version holds it (through an element)
    /// is freed with the state, not kept by the cycle.
    #[test]
    fn dropping_the_state_frees_array_cycles() {
        let e = ExprId(0);
        let mut s = State::default();
        let ty = Thunk::closed(e);
        let a = s.array(ArrVal::new(e, e, e, ty, vec![Thunk::closed(e)]));
        let old = Thunk::done(Rc::new(Val::Arr(a.clone())));
        let b = s.array(ArrVal::set(&a, 0, old).expect("in bounds"));
        let (wa, wb) = (Rc::downgrade(&a), Rc::downgrade(&b));
        drop((a, b));
        assert!(wa.upgrade().is_some() && wb.upgrade().is_some(), "a cycle");
        drop(s);
        assert!(wa.upgrade().is_none() && wb.upgrade().is_none());
    }
}
