//! Values, thunks and environments of the machine, and reading values back
//! as terms.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use crate::expr::ExprId;

use super::super::store::IdMap;
use super::super::tc::Tc;
use super::nat::Nat;
use super::{CtorInfo, Head};

pub type V = Rc<Val>;
pub type Th = Rc<Thunk>;

/// A value in weak head normal form. Each one stands for a closed term (see
/// `Readback`); the arguments are thunks, not yet evaluated.
pub enum Val {
    Nat(Nat),
    /// A string literal (the `Str` term).
    Str(ExprId),
    /// A constructor `c` (a `Const` term) applied to `args`.
    Ctor {
        c: ExprId,
        info: Rc<CtorInfo>,
        args: Vec<Th>,
    },
    /// The lambda `lam` in `env`.
    Clo {
        lam: ExprId,
        env: Env,
    },
    /// A head that does not reduce (a type, a sort, a Pi, an axiom, an
    /// opaque constant, `Quot.mk`) applied to `args`; `head` is closed.
    Neutral {
        head: ExprId,
        args: Vec<Th>,
    },
    /// A recursor, built-in operation or quotient eliminator, applied to
    /// fewer arguments than it needs to reduce.
    Pap {
        head: ExprId,
        kind: Head,
        args: Vec<Th>,
    },
    /// An array as a vector: it stands for `Array.mk ty [elems…]`.
    Arr(Rc<ArrVal>),
}

/// The constants of an array's type, at its universe level, and its
/// elements.
#[derive(Clone)]
pub struct ArrVal {
    /// `Array.mk`, `List.cons` and `List.nil`, with the level.
    pub mk: ExprId,
    pub cons: ExprId,
    pub nil: ExprId,
    /// The element type.
    pub ty: Th,
    pub elems: Vec<Th>,
}

pub enum TState {
    Delayed(ExprId, Env),
    Busy,
    Done(V),
}

/// A thunk, and for a closed term's thunk the term itself: it is read
/// back as that term, evaluated or not, as `whnf` leaves arguments alone.
pub struct Thunk(pub RefCell<TState>, pub Cell<Option<ExprId>>);

impl Thunk {
    pub fn delayed(e: ExprId, env: Env) -> Th {
        Rc::new(Thunk(
            RefCell::new(TState::Delayed(e, env)),
            Cell::new(None),
        ))
    }

    pub fn closed(e: ExprId) -> Th {
        Rc::new(Thunk(
            RefCell::new(TState::Delayed(e, Env::EMPTY)),
            Cell::new(Some(e)),
        ))
    }

    pub fn closed_done(e: ExprId, v: V) -> Th {
        Rc::new(Thunk(RefCell::new(TState::Done(v)), Cell::new(Some(e))))
    }

    pub fn done(v: V) -> Th {
        Rc::new(Thunk(RefCell::new(TState::Done(v)), Cell::new(None)))
    }
}

pub struct EnvNode {
    pub head: Th,
    pub tail: Env,
}

/// Thunks for the loose bound variables: `#0` first.
#[derive(Clone)]
pub struct Env(pub Option<Rc<EnvNode>>);

impl Env {
    pub const EMPTY: Env = Env(None);

    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    pub fn push(&self, t: Th) -> Env {
        Env(Some(Rc::new(EnvNode {
            head: t,
            tail: self.clone(),
        })))
    }

    pub fn get(&self, mut i: u32) -> &Th {
        let mut e = self;
        loop {
            let n = e.0.as_ref().expect("bound variable outside its binder");
            if i == 0 {
                return &n.head;
            }
            i -= 1;
            e = &n.tail;
        }
    }
}

/// Turns values and thunks back into closed terms, keeping sharing: a
/// thunk or value is read back once per `Readback`.
#[derive(Default)]
pub struct Readback {
    thunks: IdMap<usize, ExprId>,
    vals: IdMap<usize, ExprId>,
}

impl Readback {
    /// The term `e` with its loose bound variables replaced by `env`.
    pub fn inst(&mut self, tc: &mut Tc<'_>, e: ExprId, env: &Env) -> ExprId {
        let n = tc.st.data(e).loose_bvar_range();
        if n == 0 {
            return e;
        }
        let mut s = Vec::with_capacity(n as usize);
        let mut cur = env;
        for _ in 0..n {
            let node = cur.0.as_ref().expect("bound variable outside its binder");
            s.push(self.thunk(tc, &node.head));
            cur = &node.tail;
        }
        tc.st.instantiate(e, &s)
    }

    pub fn thunk(&mut self, tc: &mut Tc<'_>, t: &Th) -> ExprId {
        stacker::maybe_grow(256 << 10, 64 << 20, || self.thunk_here(tc, t))
    }

    fn thunk_here(&mut self, tc: &mut Tc<'_>, t: &Th) -> ExprId {
        if let Some(e) = t.1.get() {
            return e;
        }
        let key = Rc::as_ptr(t) as usize;
        if let Some(&e) = self.thunks.get(&key) {
            return e;
        }
        let st = t.0.borrow();
        let r = match &*st {
            TState::Done(v) => {
                let v = v.clone();
                drop(st);
                self.value(tc, &v)
            }
            TState::Delayed(e, env) => {
                let (e, env) = (*e, env.clone());
                drop(st);
                self.inst(tc, e, &env)
            }
            TState::Busy => unreachable!("reading back a thunk being evaluated"),
        };
        self.thunks.insert(key, r);
        r
    }

    pub fn value(&mut self, tc: &mut Tc<'_>, v: &V) -> ExprId {
        let key = Rc::as_ptr(v) as usize;
        if let Some(&e) = self.vals.get(&key) {
            return e;
        }
        let r = match &**v {
            Val::Nat(n) => match n {
                Nat::Small(x) => tc.st.nat_u64(*x),
                Nat::Big(b) => tc.st.nat((**b).clone()),
            },
            Val::Str(e) => *e,
            Val::Clo { lam, env } => self.inst(tc, *lam, env),
            Val::Ctor { c: h, args, .. }
            | Val::Neutral { head: h, args }
            | Val::Pap { head: h, args, .. } => {
                let mut r = *h;
                for a in args {
                    let x = self.thunk(tc, a);
                    r = tc.st.app(r, x);
                }
                r
            }
            Val::Arr(a) => {
                let ty = self.thunk(tc, &a.ty);
                let mut l = tc.st.app(a.nil, ty);
                for e in a.elems.iter().rev() {
                    let x = self.thunk(tc, e);
                    let c = tc.st.app(a.cons, ty);
                    let c = tc.st.app(c, x);
                    l = tc.st.app(c, l);
                }
                let m = tc.st.app(a.mk, ty);
                tc.st.app(m, l)
            }
        };
        self.vals.insert(key, r);
        r
    }
}
