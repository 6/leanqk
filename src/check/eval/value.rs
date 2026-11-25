//! Values, thunks and environments of the machine, and reading values back
//! as terms.

use std::cell::{Cell, RefCell};
use std::rc::{Rc, Weak};

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
///
/// The elements are a persistent array: one version (the root) holds them
/// in a vector, and every other version is a change to a neighbour, so
/// that `set` and `push` take constant time and memory however many
/// versions are alive. Reading a version moves the root to it first,
/// undoing and redoing the changes in between (Baker's rerooting).
pub struct ArrVal {
    /// `Array.mk`, `List.cons` and `List.nil`, with the level.
    pub mk: ExprId,
    pub cons: ExprId,
    pub nil: ExprId,
    /// The element type.
    pub ty: Th,
    node: RefCell<Node>,
}

enum Node {
    Root(Vec<Th>),
    /// The neighbour with element `i` replaced by the thunk.
    Set(usize, Th, Rc<ArrVal>),
    /// The neighbour without its last element.
    Pop(Rc<ArrVal>),
    /// The neighbour with the thunk added at the end.
    Push(Th, Rc<ArrVal>),
}

impl ArrVal {
    pub fn new(mk: ExprId, cons: ExprId, nil: ExprId, ty: Th, elems: Vec<Th>) -> Rc<ArrVal> {
        Rc::new(ArrVal {
            mk,
            cons,
            nil,
            ty,
            node: RefCell::new(Node::Root(elems)),
        })
    }

    fn version(&self, elems: Vec<Th>) -> Rc<ArrVal> {
        ArrVal::new(self.mk, self.cons, self.nil, self.ty.clone(), elems)
    }

    /// Makes `a` the root.
    fn reroot(a: &Rc<ArrVal>) {
        let mut path = vec![a.clone()];
        loop {
            let next = match &*path[path.len() - 1].node.borrow() {
                Node::Root(_) => break,
                Node::Set(_, _, n) | Node::Pop(n) | Node::Push(_, n) => n.clone(),
            };
            path.push(next);
        }
        for j in (0..path.len() - 1).rev() {
            let (x, root) = (&path[j], &path[j + 1]);
            let Node::Root(mut v) = root.node.replace(Node::Root(Vec::new())) else {
                unreachable!()
            };
            let back = match x.node.replace(Node::Root(Vec::new())) {
                Node::Set(i, t, _) => Node::Set(i, std::mem::replace(&mut v[i], t), x.clone()),
                Node::Pop(_) => Node::Push(v.pop().expect("pop of an empty version"), x.clone()),
                Node::Push(t, _) => {
                    v.push(t);
                    Node::Pop(x.clone())
                }
                Node::Root(_) => unreachable!(),
            };
            *root.node.borrow_mut() = back;
            *x.node.borrow_mut() = Node::Root(v);
        }
    }

    /// Runs `f` on the elements of `a`.
    pub fn with<R>(a: &Rc<ArrVal>, f: impl FnOnce(&[Th]) -> R) -> R {
        ArrVal::reroot(a);
        match &*a.node.borrow() {
            Node::Root(v) => f(v),
            _ => unreachable!(),
        }
    }

    pub fn len(a: &Rc<ArrVal>) -> usize {
        ArrVal::with(a, |v| v.len())
    }

    pub fn get(a: &Rc<ArrVal>, i: usize) -> Option<Th> {
        ArrVal::with(a, |v| v.get(i).cloned())
    }

    /// `a` with element `i` replaced by `t`, if `i` is in bounds.
    pub fn set(a: &Rc<ArrVal>, i: usize, t: Th) -> Option<Rc<ArrVal>> {
        ArrVal::reroot(a);
        let mut node = a.node.borrow_mut();
        let Node::Root(v) = &mut *node else {
            unreachable!()
        };
        if i >= v.len() {
            return None;
        }
        let old = std::mem::replace(&mut v[i], t);
        let b = a.version(std::mem::take(v));
        *node = Node::Set(i, old, b.clone());
        Some(b)
    }

    /// `a` with `t` added at the end.
    pub fn push(a: &Rc<ArrVal>, t: Th) -> Rc<ArrVal> {
        ArrVal::reroot(a);
        let mut node = a.node.borrow_mut();
        let Node::Root(v) = &mut *node else {
            unreachable!()
        };
        v.push(t);
        let b = a.version(std::mem::take(v));
        *node = Node::Pop(b.clone());
        b
    }
}

impl Drop for ArrVal {
    /// Drops a chain of versions in a loop rather than by recursion.
    fn drop(&mut self) {
        let mut n = std::mem::replace(self.node.get_mut(), Node::Root(Vec::new()));
        loop {
            let next = match n {
                Node::Root(_) => break,
                Node::Set(_, _, r) | Node::Pop(r) | Node::Push(_, r) => r,
            };
            match Rc::try_unwrap(next) {
                Ok(mut a) => n = std::mem::replace(a.node.get_mut(), Node::Root(Vec::new())),
                Err(_) => break,
            }
        }
    }
}

pub enum TState {
    Delayed(ExprId, Env),
    Busy,
    Done(V),
    /// The proof `e` (with loose bound variables), whose environment is
    /// not kept alive: while something else keeps it, the thunk is as
    /// good as `Delayed`; after that, forcing it or reading it back gives
    /// up.
    Erased(ExprId, Weak<EnvNode>),
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

    pub fn erased(e: ExprId, env: &Env) -> Th {
        let w = env.0.as_ref().map_or_else(Weak::new, Rc::downgrade);
        Rc::new(Thunk(RefCell::new(TState::Erased(e, w)), Cell::new(None)))
    }

    pub fn done(v: V) -> Th {
        Rc::new(Thunk(RefCell::new(TState::Done(v)), Cell::new(None)))
    }
}

/// Thunks bound by one beta step (or one `let`), in binding order: the
/// last one is the innermost variable.
pub struct EnvNode {
    pub thunks: Vec<Th>,
    pub tail: Env,
}

/// Thunks for the loose bound variables: `#0` is the last thunk of the
/// first node.
#[derive(Clone)]
pub struct Env(pub Option<Rc<EnvNode>>);

impl Env {
    pub const EMPTY: Env = Env(None);

    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    /// `self` with `ts` bound, in order (so the last one is `#0`).
    pub fn push_all(&self, ts: Vec<Th>) -> Env {
        debug_assert!(!ts.is_empty());
        Env(Some(Rc::new(EnvNode {
            thunks: ts,
            tail: self.clone(),
        })))
    }

    pub fn push(&self, t: Th) -> Env {
        self.push_all(vec![t])
    }

    pub fn get(&self, mut i: u32) -> &Th {
        let mut e = self;
        loop {
            let n = e.0.as_ref().expect("bound variable outside its binder");
            let k = n.thunks.len() as u32;
            if i < k {
                return &n.thunks[(k - 1 - i) as usize];
            }
            i -= k;
            e = &n.tail;
        }
    }

    /// The thunks of `#0 … #(n-1)`, or `None` if there are fewer.
    pub fn first(&self, n: u32) -> Option<Vec<&Th>> {
        let mut out = Vec::with_capacity(n as usize);
        let mut e = self;
        while (out.len() as u32) < n {
            let node = e.0.as_ref()?;
            for t in node.thunks.iter().rev() {
                if out.len() as u32 == n {
                    break;
                }
                out.push(t);
            }
            e = &node.tail;
        }
        Some(out)
    }
}

/// Turns values and thunks back into closed terms, keeping sharing: a
/// thunk or value is read back once per `Readback`. If it meets an erased
/// proof, `erased` is set and the term it built is meaningless.
#[derive(Default)]
pub struct Readback {
    thunks: IdMap<usize, ExprId>,
    vals: IdMap<usize, ExprId>,
    pub erased: bool,
}

impl Readback {
    /// The term `e` with its loose bound variables replaced by `env`.
    pub fn inst(&mut self, tc: &mut Tc<'_>, e: ExprId, env: &Env) -> ExprId {
        let n = tc.st.data(e).loose_bvar_range();
        if n == 0 {
            return e;
        }
        let ts = env.first(n).expect("bound variable outside its binder");
        let s: Vec<ExprId> = ts.into_iter().map(|t| self.thunk(tc, t)).collect();
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
            TState::Erased(e, w) => {
                let (e, w) = (*e, w.upgrade());
                drop(st);
                match w {
                    Some(env) => self.inst(tc, e, &Env(Some(env))),
                    None => {
                        self.erased = true;
                        e
                    }
                }
            }
            TState::Busy => unreachable!("reading back a thunk being evaluated"),
        };
        if self.erased {
            self.thunks.insert(key, r);
        } else {
            // The term the thunk stands for: kept with it, so that later
            // read-backs (and memo keys) do not build it again.
            t.1.set(Some(r));
        }
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
                for e in ArrVal::with(a, |v| v.to_vec()).iter().rev() {
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
