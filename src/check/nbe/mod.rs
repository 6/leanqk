//! The evaluating checker: type inference, weak head normalization and
//! definitional equality on values (normalization by evaluation), for the
//! declarations that are not inductive blocks or quotients. It decides what
//! `tc.rs` decides, following the same C++ functions of Lean's kernel
//! (`type_checker.cpp`) in the same order, but no term is ever substituted
//! into: a β-reduction extends an environment, a constant's universe
//! parameters travel with its closures, and an argument is only evaluated
//! when something looks at it.
//!
//! * `eval.rs`: evaluation, application and projections;
//! * `whnf.rs`: weak head normal forms (ι, δ, ζ, quotients, `Nat`);
//! * `conv.rs`: definitional equality;
//! * `infer.rs`: type inference and checking;
//! * `readback.rs`: values back to terms, for error messages.

mod conv;
mod eval;
mod infer;
mod readback;
pub mod val;
mod whnf;

pub use val::OutOfRoom;

use hashbrown::HashTable;
use num_bigint::BigUint;

use crate::env::{Decl, DeclKind};
use crate::expr::{BinderInfo, ExprId};
use crate::level::{LevelId, LevelList};
use crate::name::NameId;

use super::ext::Ext;
use super::store::{IdMap, IdSet, Store};
use super::tc::{KErr, R};
use val::{Arena, Ls, V};

/// A free variable opened while checking.
#[derive(Clone, Copy, Debug)]
pub struct FVarInfo {
    pub name: NameId,
    pub ty: V,
    pub val: Option<V>,
    pub bi: BinderInfo,
    /// What identifies it: its type and value.
    pub key: (V, V),
}

/// The free variable of an ill-typed application or projection that
/// evaluation met: it never reduces and has no type.
pub const BOTTOM: u32 = u32::MAX - 1;

/// Values an arena may hold before it is dropped between declarations.
const KEEP_VALUES: usize = 1 << 16;

type SynKey = (ExprId, val::Env, val::Ls, ExprId, val::Env, val::Ls, u32);

pub struct Nbe<'e> {
    pub st: Store<'e>,
    pub ext: &'e Ext,
    pub a: Arena,
    /// Only declarations before this index of `env.decls` are visible.
    pub limit: u32,
    /// Universe parameters in scope for checking.
    pub lparams: Vec<NameId>,
    eager: bool,
    pub fvars: Vec<FVarInfo>,
    bigs: Vec<BigUint>,
    big_table: HashTable<u32>,
    level_cache: IdMap<(LevelId, Ls), LevelId>,
    list_cache: IdMap<(LevelList, Ls), LevelList>,
    const_type: IdMap<(NameId, LevelList), V>,
    const_value: IdMap<(NameId, LevelList), V>,
    eq_ok: IdSet<(V, V)>,
    eq_fail: IdSet<(V, V)>,
    /// Pairs found not definitionally equal.
    neq: IdSet<(V, V)>,
    /// Terms with universe parameters marked checked in this declaration.
    level_checked: Vec<V>,
    fresh: bool,
    syn_ok: IdSet<(V, V)>,
    syn_fail: IdSet<(V, V)>,
    /// Structural comparisons of terms in environments, by `syn_eq_t`.
    syn_t: IdMap<SynKey, bool>,
    level_eq: IdMap<(LevelId, LevelId), bool>,
    major_induct: IdMap<NameId, NameId>,
    /// `prop_positions` of constants.
    prop_pos: IdMap<NameId, u64>,
    open_count: IdMap<(V, V), u32>,
    trim_cache: IdMap<(val::Env, u32), val::Env>,
    canon_fvar: IdMap<(V, V, u32), u32>,
    elims: Vec<Vec<val::Elim>>,
    terms: Vec<ExprId>,
    vargs: Vec<V>,
    /// Nesting of eager argument evaluation (see `thunk`).
    eager_depth: u32,
}

/// Empty `c`, dropping its storage if it is large: clearing a table costs
/// its capacity, and one big declaration should not slow down every later
/// one.
fn shrink<T: Default + Cap>(c: &mut T) {
    if c.cap() > 1 << 12 {
        *c = T::default();
    } else {
        c.clear_keep();
    }
}

trait Cap {
    fn cap(&self) -> usize;
    fn clear_keep(&mut self);
}

impl<K, W, S> Cap for hashbrown::HashMap<K, W, S> {
    fn cap(&self) -> usize {
        self.capacity()
    }
    fn clear_keep(&mut self) {
        self.clear()
    }
}

impl<K, S> Cap for hashbrown::HashSet<K, S> {
    fn cap(&self) -> usize {
        self.capacity()
    }
    fn clear_keep(&mut self) {
        self.clear()
    }
}

impl<T> Cap for HashTable<T> {
    fn cap(&self) -> usize {
        self.capacity()
    }
    fn clear_keep(&mut self) {
        self.clear()
    }
}

impl<T> Cap for Vec<T> {
    fn cap(&self) -> usize {
        self.capacity()
    }
    fn clear_keep(&mut self) {
        self.clear()
    }
}

impl<'e> Nbe<'e> {
    pub fn new(st: Store<'e>, ext: &'e Ext) -> Self {
        Nbe {
            st,
            ext,
            a: Arena::new(),
            limit: 0,
            lparams: Vec::new(),
            eager: false,
            fvars: Vec::new(),
            bigs: Vec::new(),
            big_table: HashTable::new(),
            level_cache: IdMap::default(),
            list_cache: IdMap::default(),
            const_type: IdMap::default(),
            const_value: IdMap::default(),
            eq_ok: IdSet::default(),
            eq_fail: IdSet::default(),
            neq: IdSet::default(),
            level_checked: Vec::new(),
            fresh: true,
            syn_ok: IdSet::default(),
            syn_fail: IdSet::default(),
            syn_t: IdMap::default(),
            level_eq: IdMap::default(),
            major_induct: IdMap::default(),
            prop_pos: IdMap::default(),
            open_count: IdMap::default(),
            trim_cache: IdMap::default(),
            canon_fvar: IdMap::default(),
            elims: Vec::new(),
            terms: Vec::new(),
            vargs: Vec::new(),
            eager_depth: 0,
        }
    }

    /// Start on a declaration checked against the first `limit` blocks.
    /// What the arena and the caches hold stays: a value means the same in
    /// every declaration (a free variable is identified by its type, value
    /// and depth), and the environment only grows. What depends on the
    /// declaration goes: its universe parameters, and so which terms with
    /// universe parameters are known to be well-formed. Past a size, all
    /// of it goes.
    pub fn begin(&mut self, limit: u32) {
        if self.a.len() > KEEP_VALUES || self.st.local_exprs() > KEEP_VALUES {
            self.reset(limit);
            return;
        }
        self.limit = limit;
        self.lparams.clear();
        self.eager = false;
        self.terms.clear();
        self.vargs.clear();
        self.eager_depth = 0;
        self.open_count.clear();
        for v in self.level_checked.drain(..) {
            self.a.clear_checked(v);
        }
        self.fresh = self.a.is_empty();
    }

    /// Forget everything.
    pub fn reset(&mut self, limit: u32) {
        self.limit = limit;
        self.lparams.clear();
        self.eager = false;
        shrink(&mut self.fvars);
        self.terms.clear();
        self.vargs.clear();
        self.eager_depth = 0;
        shrink(&mut self.open_count);
        shrink(&mut self.trim_cache);
        shrink(&mut self.canon_fvar);
        shrink(&mut self.level_checked);
        self.a.clear();
        if self.st.local_exprs() > KEEP_VALUES {
            self.st.clear();
        }
        shrink(&mut self.bigs);
        shrink(&mut self.big_table);
        shrink(&mut self.level_cache);
        shrink(&mut self.list_cache);
        shrink(&mut self.const_type);
        shrink(&mut self.const_value);
        shrink(&mut self.eq_ok);
        shrink(&mut self.eq_fail);
        shrink(&mut self.neq);
        shrink(&mut self.syn_ok);
        shrink(&mut self.syn_fail);
        shrink(&mut self.syn_t);
        shrink(&mut self.level_eq);
        shrink(&mut self.major_induct);
        self.fresh = true;
    }

    /// Whether nothing is kept from an earlier declaration.
    pub fn is_fresh(&self) -> bool {
        self.fresh
    }

    // ---- environment ----

    /// The declaration named `n`, if it is visible.
    pub fn find(&self, n: NameId) -> Option<Decl> {
        let env = self.st.env;
        let &i = env.by_name.get(&n)?;
        (i < self.limit).then(|| env.decls[i as usize])
    }

    pub fn get(&self, n: NameId) -> R<Decl> {
        match self.find(n) {
            Some(d) => Ok(d),
            None => Err(KErr(format!("unknown constant '{}'", self.st.show(n)))),
        }
    }

    fn decl_value(d: &Decl) -> Option<ExprId> {
        match d.kind {
            DeclKind::Definition { value, .. } | DeclKind::Theorem { value, .. } => Some(value),
            _ => None,
        }
    }

    // ---- universe substitutions ----

    pub fn inst_level(&mut self, l: LevelId, ls: Ls) -> LevelId {
        if ls == Ls::ID || !self.st.level_has_param(l) {
            return l;
        }
        if let Some(&r) = self.level_cache.get(&(l, ls)) {
            return r;
        }
        let node = self.a.ls(ls);
        let ps: Vec<NameId> = self.st.name_list(node.params).to_vec();
        let lv: Vec<LevelId> = self.st.list(node.levels).to_vec();
        let r = self.st.inst_level(l, &ps, &lv);
        self.level_cache.insert((l, ls), r);
        r
    }

    pub fn inst_list(&mut self, ll: LevelList, ls: Ls) -> LevelList {
        if ls == Ls::ID || !self.st.list_has_param(ll) {
            return ll;
        }
        if let Some(&r) = self.list_cache.get(&(ll, ls)) {
            return r;
        }
        let node = self.a.ls(ls);
        let ps: Vec<NameId> = self.st.name_list(node.params).to_vec();
        let lv: Vec<LevelId> = self.st.list(node.levels).to_vec();
        let r = self.st.inst_list(ll, &ps, &lv);
        self.list_cache.insert((ll, ls), r);
        r
    }

    /// The substitution of `d`'s universe parameters by `ls`.
    pub fn decl_ls(&mut self, d: &Decl, ls: LevelList) -> Ls {
        self.a.mk_ls(d.level_params, ls)
    }

    // ---- literals ----

    /// The canonical value of the literal `n`.
    pub fn nat(&mut self, n: BigUint) -> V {
        if let Ok(v) = u64::try_from(&n) {
            return self.a.mk(val::Val::Nat(v as u32, (v >> 32) as u32));
        }
        let h = crate::expr::big_hash(&n);
        let Self {
            bigs, big_table, ..
        } = self;
        let id = if let Some(&id) = big_table.find(h, |&id| bigs[id as usize] == n) {
            id
        } else {
            let id = bigs.len() as u32;
            bigs.push(n);
            let bigs = &*bigs;
            big_table.insert_unique(h, id, |&id| crate::expr::big_hash(&bigs[id as usize]));
            id
        };
        self.a.mk(val::Val::NatBig(id))
    }

    pub fn nat_u64(&mut self, v: u64) -> V {
        self.a.mk(val::Val::Nat(v as u32, (v >> 32) as u32))
    }

    pub fn nat_value(&self, v: V) -> Option<BigUint> {
        match self.a.get(v) {
            val::Val::Nat(lo, hi) => Some(BigUint::from((hi as u64) << 32 | lo as u64)),
            val::Val::NatBig(i) => Some(self.bigs[i as usize].clone()),
            _ => None,
        }
    }

    pub fn big(&self, i: u32) -> &BigUint {
        &self.bigs[i as usize]
    }

    // ---- free variables ----

    /// Open a binder: a free variable of type `ty` (and value `val`).
    /// Free variables are identified by their type, value and how many of
    /// the same are open already, so the same binder opened again, in
    /// another comparison or another branch, gets the same variable and
    /// meets the results cached about it the first time. Those still hold:
    /// a fact about a variable of type `ty` holds for any variable of that
    /// type. Two binders open at once never share a variable. Every
    /// `push_fvar` is undone by `pop_fvar` when its scope ends.
    pub fn push_fvar(&mut self, name: NameId, ty: V, val: Option<V>, bi: BinderInfo) -> V {
        let ty = self.force(ty);
        let tk = ty;
        let vk = val.unwrap_or(V(val::NONE));
        let n = self.open_count.entry((tk, vk)).or_insert(0);
        let idx = *n;
        *n += 1;
        let k = match self.canon_fvar.get(&(tk, vk, idx)) {
            Some(&k) => k,
            None => {
                let k = self.fvars.len() as u32;
                assert!(
                    k < BOTTOM,
                    "nitrolean: resource limit: too many free variables"
                );
                self.fvars.push(FVarInfo {
                    name,
                    ty,
                    val,
                    bi,
                    key: (tk, vk),
                });
                self.canon_fvar.insert((tk, vk, idx), k);
                k
            }
        };
        self.a.mk(val::Val::FVar(k, val::Sp::NIL))
    }

    /// Close the binder that `push_fvar` opened as `x`.
    pub fn pop_fvar(&mut self, x: V) {
        let val::Val::FVar(k, _) = self.a.get(x) else {
            unreachable!()
        };
        let f = self.fvars[k as usize];
        if let Some(n) = self.open_count.get_mut(&f.key) {
            *n -= 1;
        }
    }

    /// The first `n` entries of `env`: what a term with loose bound
    /// variables below `n` can see. Closures and thunks keep only those, so
    /// the same term reached under different irrelevant bindings is one
    /// value.
    #[inline]
    pub fn trim(&mut self, env: val::Env, n: u32) -> val::Env {
        if n == 0 {
            return val::Env::NIL;
        }
        if self.a.env_len(env) <= n {
            return env;
        }
        if let Some(&e) = self.trim_cache.get(&(env, n)) {
            return e;
        }
        let mut vs = Vec::with_capacity(n as usize);
        let mut cur = env;
        for _ in 0..n {
            vs.push(self.a.env_head(cur));
            cur = self.a.env_tail(cur);
        }
        let mut r = val::Env::NIL;
        for &v in vs.iter().rev() {
            r = self.a.cons(r, v);
        }
        self.trim_cache.insert((env, n), r);
        r
    }

    /// Scratch buffers for spines, reused across calls.
    fn take_elims(&mut self) -> Vec<val::Elim> {
        self.elims.pop().unwrap_or_default()
    }

    fn put_elims(&mut self, mut v: Vec<val::Elim>) {
        v.clear();
        self.elims.push(v);
    }
}
