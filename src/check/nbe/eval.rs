//! Evaluation of terms to values, application and projection.

use crate::env::DeclKind;
use crate::expr::{ExprId, ExprNode};
use crate::level::LevelList;
use crate::name::NameId;

use super::val::{Elim, Env, Ls, Sp, V, Val};
use super::{BOTTOM, Nbe};

/// How many first-order applications inside one another an argument is
/// evaluated through before the rest is left as thunks (see `thunk`).
const EAGER_DEPTH: u32 = 16;

/// Whether `thunk` evaluates every application, projection and `let` now
/// (within `EAGER_DEPTH`), not only first-order applications: their values
/// are almost always asked for, and a value made now is found by its
/// contents where a thunk is found only by its term and environment.
const EAGER_ALL: bool = true;

/// Whether what `thunk` evaluates at once is remembered by the entries of
/// the environment the term reads (`eager`), not through a thunk.
const EAGER_MEMO: bool = true;

/// Whether `thunk` looks an application, `let` or projection up in the
/// eager front itself, before the rest (out of line).
const THUNK_EAGER_FRONT: bool = true;

/// Whether `eager` remembers in a direct-mapped table only
/// (`Nbe::eager_direct`), not a growing one.
const EAGER_DIRECT: bool = true;

/// Past this many environment entries in range, `eager` goes through a
/// thunk instead.
const EAGER_MEMO_RANGE: u32 = 32;

impl Nbe<'_> {
    /// The value of `e` with its loose bound variables given by `env` and
    /// its universe parameters substituted by `ls`. The result is a head
    /// form (never a thunk): β-redexes at the head are reduced, constants
    /// are not unfolded.
    pub fn eval(&mut self, e: ExprId, env: Env, ls: Ls) -> V {
        let d = self.st.data(e);
        let ls = if d.has_level_param() { ls } else { Ls::ID };
        // A small frame here: each kind of term is evaluated out of line.
        match self.st.node(e) {
            ExprNode::BVar(i) => match self.a.lookup(env, i) {
                Some(v) => self.force(v),
                None => self.bottom(Sp::NIL),
            },
            ExprNode::App(..) => self.eval_app(e, env, ls),
            ExprNode::Lam(..) | ExprNode::Pi(..) => self.eval_binder(e, env, ls),
            ExprNode::Const(n, lv) => self.eval_const(n, lv, ls),
            _ => self.eval_other(e, env, ls),
        }
    }

    #[inline(never)]
    fn eval_const(&mut self, n: NameId, lv: LevelList, ls: Ls) -> V {
        // Callers have already consulted the expression's universe-parameter flag.
        let lv = if ls == Ls::ID {
            lv
        } else {
            self.inst_param_list(lv, ls)
        };
        self.a.cnst(n, lv)
    }

    #[inline(never)]
    fn eval_app(&mut self, e: ExprId, env: Env, ls: Ls) -> V {
        self.ticks += 1;
        let base = self.terms.len();
        let mut f = e;
        let head = loop {
            match self.st.node(f) {
                ExprNode::App(g, a) => {
                    self.terms.push(a);
                    f = g;
                }
                n => break n,
            }
        };
        // The head as `eval` would, from its node read already.
        let h = match head {
            ExprNode::BVar(i) => match self.a.lookup(env, i) {
                Some(v) => self.force(v),
                None => self.bottom(Sp::NIL),
            },
            ExprNode::Const(n, lv) => {
                let ls = if self.st.data(f).has_level_param() {
                    ls
                } else {
                    Ls::ID
                };
                self.eval_const(n, lv, ls)
            }
            _ => self.eval(f, env, ls),
        };
        let vbase = self.vargs.len();
        for k in (base..self.terms.len()).rev() {
            let a = *super::val::at(&self.terms, k);
            let av = self.thunk(a, env, ls);
            self.vargs.push(av);
        }
        self.terms.truncate(base);
        let r = self.apply_n(h, vbase);
        self.vargs.truncate(vbase);
        r
    }

    #[inline(never)]
    fn eval_binder(&mut self, e: ExprId, env: Env, ls: Ls) -> V {
        // A front by the environment as given, before it is cut.
        let si = (crate::hash::hash_front(e.0 as u64 | (ls.0 as u64) << 32, env.0 as u64) >> 50)
            as usize
            & (super::BINDER_SLOTS - 1);
        let s = self.binder_slots[si];
        if s[0] == e.0 && s[1] == env.0 && s[2] == ls.0 {
            return V(s[3]);
        }
        let v = self.eval_binder_new(e, env, ls);
        self.binder_slots[si] = [e.0, env.0, ls.0, v.0];
        v
    }

    fn eval_binder_new(&mut self, e: ExprId, env: Env, ls: Ls) -> V {
        let d = self.st.data(e);
        let env = self.trim_prune(env, d);
        match self.st.node(e) {
            ExprNode::Lam(..) => self.a.mk(Val::Lam(e, env, ls)),
            _ => self.a.mk(Val::Pi(e, env, ls)),
        }
    }

    #[inline(never)]
    fn eval_other(&mut self, e: ExprId, env: Env, ls: Ls) -> V {
        match self.st.node(e) {
            ExprNode::Sort(l) => {
                let l = if ls == Ls::ID {
                    l
                } else {
                    self.inst_param_level(l, ls)
                };
                self.a.sort(l)
            }
            ExprNode::Let(h, b) => {
                let lb = self.st.let_binder(h);
                let v = self.thunk(lb.value, env, ls);
                let env2 = self.a.cons(env, v);
                self.eval(b, env2, ls)
            }
            ExprNode::NatSmall(lo, hi) => self.a.mk(Val::Nat(lo, hi)),
            ExprNode::NatBig(b) => {
                let n = self.st.big(b).clone();
                self.nat(n)
            }
            ExprNode::Str(s) => self.a.mk(Val::Str(s)),
            ExprNode::Proj(s, i, x) => {
                let xv = self.eval(x, env, ls);
                self.proj(xv, s, i)
            }
            ExprNode::FVar(k) => self.a.mk(Val::FVar(k, Sp::NIL)),
            _ => unreachable!(),
        }
    }

    /// `e` in `env`, unevaluated unless that is as cheap as a thunk.
    #[inline(always)]
    pub fn thunk(&mut self, e: ExprId, env: Env, ls: Ls) -> V {
        if let ExprNode::BVar(i) = self.st.node(e)
            && let Some(v) = self.a.lookup(env, i)
        {
            return v;
        }
        if THUNK_EAGER_FRONT
            && EAGER_MEMO
            && matches!(
                self.st.node(e),
                ExprNode::App(..) | ExprNode::Let(..) | ExprNode::Proj(..)
            )
            && self.eager_depth < EAGER_DEPTH
        {
            return self.eager(e, env, ls);
        }
        self.thunk_other(e, env, ls)
    }

    /// `thunk` but of a variable found: out of line, so that a variable
    /// costs no frame for the rest.
    #[inline(never)]
    fn thunk_other(&mut self, e: ExprId, env: Env, ls: Ls) -> V {
        match self.st.node(e) {
            ExprNode::BVar(_) => self.bottom(Sp::NIL),
            ExprNode::Const(n, lv) => {
                let ls = if self.st.data(e).has_level_param() {
                    ls
                } else {
                    Ls::ID
                };
                self.eval_const(n, lv, ls)
            }
            ExprNode::Lam(..) | ExprNode::Pi(..) => {
                let ls = if self.st.data(e).has_level_param() {
                    ls
                } else {
                    Ls::ID
                };
                self.eval_binder(e, env, ls)
            }
            ExprNode::Sort(_)
            | ExprNode::NatSmall(..)
            | ExprNode::NatBig(_)
            | ExprNode::Str(_)
            | ExprNode::FVar(_) => self.eval(e, env, ls),
            // Evaluated now (see `EAGER_ALL`); a first-order application
            // evaluates to a neutral without reducing anything, so that the
            // same term reached in different environments is the same value.
            _ if EAGER_MEMO && self.eager_depth < EAGER_DEPTH => self.eager(e, env, ls),
            _ => {
                let t = self.thunk_value(e, env, ls);
                let f = self.a.r(t).forced;
                if f != super::val::NONE {
                    return V(f);
                }
                if self.eager_depth < EAGER_DEPTH
                    && (EAGER_ALL
                        || matches!(self.st.node(e), ExprNode::App(..))
                            && self.neutral_head(e, env))
                {
                    // Memoized through the thunk: terms are DAGs. Only so
                    // deep, so that a long first-order term rebuilt in many
                    // environments costs its top, not all of it.
                    self.eager_depth += 1;
                    let v = self.force(t);
                    self.eager_depth -= 1;
                    return v;
                }
                t
            }
        }
    }

    /// The value of `e` in `env` under `ls`, evaluated now, remembered by
    /// the entries of `env` that `e` reads (no thunk is made, and no
    /// environment is cut).
    #[inline]
    fn eager(&mut self, e: ExprId, env: Env, ls: Ls) -> V {
        let sh = crate::hash::hash_front(e.0 as u64 | (ls.0 as u64) << 32, env.0 as u64);
        let si = (sh >> 50) as usize & (super::EAGER_SLOTS - 1);
        let s = self.eager_slots[si];
        if s[0] == e.0 && s[1] == env.0 && s[2] == ls.0 {
            return V(s[3]);
        }
        self.eager_miss(e, env, ls, si)
    }

    /// `eval`, remembered by the exact term, environment and levels in
    /// `eager`'s direct slots (a lossy table: a value lost is made again,
    /// the same).
    pub(super) fn eval_slot(&mut self, e: ExprId, env: Env, ls: Ls) -> V {
        let sh = crate::hash::hash_front(e.0 as u64 | (ls.0 as u64) << 32, env.0 as u64);
        let si = (sh >> 50) as usize & (super::EAGER_SLOTS - 1);
        let s = self.eager_slots[si];
        if s[0] == e.0 && s[1] == env.0 && s[2] == ls.0 {
            return V(s[3]);
        }
        let v = self.eval(e, env, ls);
        self.eager_slots[si] = [e.0, env.0, ls.0, v.0];
        v
    }

    /// `eager` past its front (slot `si`): out of line, as it evaluates.
    #[inline(never)]
    fn eager_miss(&mut self, e: ExprId, env: Env, ls: Ls, si: usize) -> V {
        let d = self.st.data(e);
        let n = d.loose_bvar_range().min(self.a.env_len(env));
        if n > EAGER_MEMO_RANGE {
            // Deep: through a thunk, whose environment is cut once.
            let t = self.thunk_value(e, env, ls);
            let f = self.a.r(t).forced;
            if f != super::val::NONE {
                return V(f);
            }
            self.eager_depth += 1;
            let v = self.force(t);
            self.eager_depth -= 1;
            return v;
        }
        let key = self
            .memo_key(e, env, ls, d.unused_low() as u64, EAGER_MEMO_RANGE)
            .expect("in range");
        if EAGER_DIRECT && let Some([h, ke, kls, kt]) = key.by_tuple() {
            // A lossy table: a value lost is made again, the same.
            key.drop_in(&mut self.vargs);
            let di = h as usize & (super::EAGER_DIRECT_SLOTS - 1);
            let s = self.eager_direct[di];
            let v = if s[0] == ke && s[1] == kls && s[2] == kt {
                V(s[3])
            } else {
                self.eager_depth += 1;
                let v = self.eval(e, env, ls);
                self.eager_depth -= 1;
                self.eager_direct[di] = [ke, kls, kt, v.0];
                v
            };
            self.eager_slots[si] = [e.0, env.0, ls.0, v.0];
            return v;
        }
        let (i, found) = Self::memo_find_or_add(
            &mut self.vargs,
            &mut self.eager_memo,
            key,
            [super::val::NONE],
        );
        let known = self.eager_memo.get(i)[0];
        let v = if found && known != super::val::NONE {
            V(known)
        } else {
            self.eager_depth += 1;
            let v = self.eval(e, env, ls);
            self.eager_depth -= 1;
            self.eager_memo.set(i, 0, v.0);
            v
        };
        self.eager_slots[si] = [e.0, env.0, ls.0, v.0];
        v
    }

    /// The thunk of `e` in `env` (trimmed to what `e` may use) under `ls`.
    #[inline]
    pub fn thunk_value(&mut self, e: ExprId, env: Env, ls: Ls) -> V {
        let (slot, hit) = self.a.thunk_slot(e, env, ls);
        match hit {
            Some(t) => t,
            None => self.thunk_new(e, env, ls, slot),
        }
    }

    /// `thunk_value` not in the thunk table's `slot`.
    #[inline(never)]
    fn thunk_new(&mut self, e: ExprId, env: Env, ls: Ls, slot: usize) -> V {
        let d = self.st.data(e);
        let env2 = self.trim_prune(env, d);
        let ls2 = if d.has_level_param() { ls } else { Ls::ID };
        let t = self.a.mk(Val::Thunk(e, env2, ls2));
        self.a.set_thunk_slot(slot, e, env, ls, t);
        t
    }

    /// Whether the head of the application `e` is a constant or a bound
    /// variable whose (already known) value is a neutral, so that
    /// evaluating `e` reduces nothing.
    fn neutral_head(&self, e: ExprId, env: Env) -> bool {
        let mut f = e;
        while let ExprNode::App(g, _) = self.st.node(f) {
            f = g;
        }
        match self.st.node(f) {
            ExprNode::Const(..) | ExprNode::FVar(_) => true,
            ExprNode::BVar(i) => match self.a.lookup(env, i) {
                Some(v) => {
                    let f = self.a.r(v).forced;
                    let v = if f != super::val::NONE { V(f) } else { v };
                    matches!(self.a.get(v), Val::Const(..) | Val::FVar(..))
                }
                None => false,
            },
            _ => false,
        }
    }

    /// The head form of `v`.
    #[inline]
    pub fn force(&mut self, v: V) -> V {
        match self.a.get(v) {
            Val::Thunk(e, env, ls) => {
                let f = self.a.r(v).forced;
                if f != super::val::NONE {
                    return V(f);
                }
                let r = self.eval(e, env, ls);
                self.a.rm(v).forced = r.0;
                r
            }
            _ => v,
        }
    }

    pub fn bottom(&mut self, sp: Sp) -> V {
        self.a.mk(Val::FVar(BOTTOM, sp))
    }

    /// `f a`.
    pub fn apply(&mut self, f: V, a: V) -> V {
        let f = self.force(f);
        match self.a.get(f) {
            Val::Lam(t, env, ls) => {
                let ExprNode::Lam(_, _, _, body) = self.st.node(t) else {
                    unreachable!()
                };
                let env2 = self.a.cons(env, a);
                self.eval(body, env2, ls)
            }
            h @ (Val::Const(..) | Val::FVar(..)) => self.a.neutral_of(f, h, &[a]),
            _ => {
                let sp = self.a.snoc(Sp::NIL, Elim::Arg(a));
                self.bottom(sp)
            }
        }
    }

    pub fn apply_all(&mut self, f: V, args: &[V]) -> V {
        let base = self.vargs.len();
        self.vargs.extend_from_slice(args);
        let r = self.apply_n(f, base);
        self.vargs.truncate(base);
        r
    }

    /// `f` applied to `self.vargs[base..]`, which it leaves in place: the
    /// binders of a closure are entered together and a neutral gets the
    /// whole spine, so no partial application is built.
    pub fn apply_n(&mut self, mut f: V, base: usize) -> V {
        let end = self.vargs.len();
        let mut i = base;
        while i < end {
            f = self.force(f);
            match self.a.get(f) {
                Val::Lam(t, mut env, ls) => {
                    let mut body = t;
                    while i < end
                        && let ExprNode::Lam(_, _, _, b) = self.st.node(body)
                    {
                        env = self.a.cons(env, *super::val::at(&self.vargs, i));
                        body = b;
                        i += 1;
                    }
                    f = self.eval(body, env, ls);
                }
                h @ (Val::Const(..) | Val::FVar(..)) => {
                    return self.a.neutral_of(f, h, &self.vargs[i..end]);
                }
                _ => {
                    let sp = self.a.snoc_args(Sp::NIL, &self.vargs[i..end]);
                    return self.bottom(sp);
                }
            }
        }
        f
    }

    pub fn apply_elim(&mut self, f: V, e: Elim) -> V {
        match e {
            Elim::Arg(a) => self.apply(f, a),
            Elim::Proj(s, i) => self.proj(f, s, i),
        }
    }

    pub fn apply_elims(&mut self, mut f: V, es: &[Elim]) -> V {
        for &e in es {
            f = self.apply_elim(f, e);
        }
        f
    }

    /// Apply the eliminations of `sp` to `f`.
    pub fn apply_spine(&mut self, f: V, sp: Sp) -> V {
        if sp == Sp::NIL {
            return f;
        }
        let mut es = self.take_elims();
        self.a.elims(sp, &mut es);
        let base = self.vargs.len();
        let mut f = f;
        for &e in &es {
            match e {
                Elim::Arg(a) => self.vargs.push(a),
                Elim::Proj(s, i) => {
                    f = self.apply_n(f, base);
                    self.vargs.truncate(base);
                    f = self.proj(f, s, i);
                }
            }
        }
        let r = self.apply_n(f, base);
        self.vargs.truncate(base);
        self.put_elims(es);
        r
    }

    /// The field `i` of the constructor application `c`, if it is one of
    /// the structure `s` (Lean's `reduce_proj_core` after `whnf`).
    pub fn ctor_field(&mut self, c: V, s: NameId, i: u32) -> Option<V> {
        let Val::Const(mk, _, sp) = self.a.get(c) else {
            return None;
        };
        let d = self.find(mk)?;
        let DeclKind::Constructor {
            induct, num_params, ..
        } = d.kind
        else {
            return None;
        };
        if induct != s {
            return None;
        }
        let k = num_params + i;
        if k >= self.a.sp_len(sp) || self.a.sp_has_proj(sp) {
            return None;
        }
        Some(self.a.sp_arg(sp, k))
    }

    /// The projection `v.i` of the structure `s`: the field if `v` is a
    /// constructor application, else a neutral.
    pub fn proj(&mut self, v: V, s: NameId, i: u32) -> V {
        let v = self.force(v);
        match self.a.get(v) {
            Val::Const(..) => {
                if let Some(f) = self.ctor_field(v, s, i) {
                    return self.force(f);
                }
                let h = self.a.get(v);
                self.a.neutral_proj(v, h, s, i)
            }
            h @ Val::FVar(..) => self.a.neutral_proj(v, h, s, i),
            Val::Str(_) => match self.string_lit_to_constructor(v) {
                Ok(c) => self.proj(c, s, i),
                Err(_) => {
                    let sp = self.a.snoc(Sp::NIL, Elim::Proj(s, i));
                    self.bottom(sp)
                }
            },
            _ => {
                let sp = self.a.snoc(Sp::NIL, Elim::Proj(s, i));
                self.bottom(sp)
            }
        }
    }

    /// The value of constant `n` at levels `ls`.
    pub fn cnst(&mut self, n: NameId, ls: LevelList) -> V {
        self.a.mk(Val::Const(n, ls, Sp::NIL))
    }

    /// The type of constant `d` at levels `ls`.
    pub fn const_type(&mut self, d: &crate::env::Decl, ls: LevelList) -> V {
        if let Some(&t) = self.const_type.get(&(d.name, ls)) {
            return t;
        }
        let s = self.decl_ls(d, ls);
        let t = self.thunk(d.ty, Env::NIL, s);
        let t = self.force(t);
        self.const_type.insert((d.name, ls), t);
        t
    }

    /// The value of the definition `d` at levels `ls`.
    pub fn const_value(&mut self, d: &crate::env::Decl, value: ExprId, ls: LevelList) -> V {
        if let Some(&t) = self.const_value.get(&(d.name, ls)) {
            return t;
        }
        let s = self.decl_ls(d, ls);
        let t = self.eval(value, Env::NIL, s);
        self.const_value.insert((d.name, ls), t);
        t
    }
}
