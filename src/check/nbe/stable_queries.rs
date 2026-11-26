//! Exact structural ids for closed values. The persistent table contains
//! only immutable export expressions, names and levels, and its own ids.
//! Each worker uses one immutable environment. An equality or reduction
//! established under an earlier prefix still holds under a larger prefix
//! of that environment.

use crate::env::NameList;
use crate::expr::{ExprId, ExprNode};
use crate::level::{LevelId, LevelList, LevelNode};
use crate::name::NameId;
use crate::strings::StrId;

use super::super::store::{IdMap, LOCAL, Store, is_local};
use super::Nbe;
use super::val::{Arena, Elim, Env, Ls, V, Val};

const MAX_NODES: usize = 1 << 18;
// Keep the total storage for persistent nodes bounded across workers.
const NODE_BUDGET: usize = 1 << 20;
const MIN_NODES: usize = 1 << 10;
const MAX_ARENA_MEMOS: usize = 1 << 16;
const MAX_DEPTH: u32 = 64;
const UNKNOWN: u32 = u32::MAX;
const MIN_TICKS: u64 = 8;
// Persistent node indices occupy the low range. A tag in the top bits
// encodes values that need no new node at all.
const DIRECT_SHIFT: u32 = 29;
const DIRECT_MASK: u32 = (1 << DIRECT_SHIFT) - 1;
const DIRECT_LAM: u32 = 1;
const DIRECT_PI: u32 = 2;
const DIRECT_THUNK: u32 = 3;
const DIRECT_CONST: u32 = 4;
const DIRECT_SORT: u32 = 5;
const DIRECT_NAT: u32 = 6;

fn direct(tag: u32, id: u32) -> Option<u32> {
    (id <= DIRECT_MASK).then_some((tag << DIRECT_SHIFT) | id)
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Node {
    Sort(LevelId),
    Nat(u32, u32),
    Str(StrId),
    Const(NameId, LevelList),
    App(u32, u32),
    Proj(NameId, u32, u32),
    Lam(ExprId, u32, u32),
    Pi(ExprId, u32, u32),
    Thunk(ExprId, u32, u32),
    Capture(u32, u32),
    Substitution(u32, u32, LevelList),
    LevelSucc(LevelId),
    LevelMax(LevelId, LevelId),
    LevelIMax(LevelId, LevelId),
    LevelCons(LevelId, LevelList),
}

#[derive(Default)]
pub(super) struct Queries {
    intern: hashbrown::HashMap<Node, u32>,
    nodes: Vec<Node>,
    // These maps hold arena ids and are cleared when the arena is cleared.
    keys: Vec<u32>,
    restored: IdMap<u32, V>,
    substitutions: IdMap<Ls, u32>,
    levels: IdMap<LevelId, LevelId>,
    restored_levels: IdMap<LevelId, LevelId>,
    // The remaining maps use only persistent ids and record the prefix
    // in which the kernel established a positive result.
    checked_parameters: IdMap<(ExprId, u64), bool>,
    equal: IdMap<(u32, u32), u32>,
    reduct: IdMap<u32, (u32, u32)>,
    node_limit: usize,
    profile: bool,
    rotations: u64,
    eq_hits: u64,
    whnf_hits: u64,
}

impl Queries {
    pub(super) fn for_worker(jobs: usize) -> Option<Box<Self>> {
        let mode = std::env::var("NITROLEAN_STABLE_QUERIES");
        if mode.as_deref() == Ok("0") {
            return None;
        }
        let node_limit = (NODE_BUDGET / jobs).min(MAX_NODES);
        if node_limit < MIN_NODES {
            return None;
        }
        Some(Self::new(node_limit, mode.as_deref() == Ok("stats")))
    }

    fn new(node_limit: usize, profile: bool) -> Box<Self> {
        let mut cache = Box::<Self>::default();
        cache.node_limit = node_limit;
        cache.profile = profile;
        cache
    }

    pub(super) fn reset(&mut self) {
        self.keys.clear();
        self.restored.clear();
        self.substitutions.clear();
        self.levels.clear();
        self.restored_levels.clear();
        if self.checked_parameters.len() >= self.node_limit / 4 {
            self.checked_parameters.clear();
        }
        if self.nodes.len() == self.node_limit
            || self.equal.len() == self.node_limit / 2
            || self.reduct.len() == self.node_limit / 2
        {
            // Reset only at an arena boundary, when no transient memo can
            // still refer to a persistent node. Keep the allocated storage.
            self.intern.clear();
            self.nodes.clear();
            self.equal.clear();
            self.reduct.clear();
            self.rotations += 1;
        }
    }

    fn intern<const ADMIT: bool>(&mut self, node: Node) -> Option<u32> {
        // Reuse existing nodes even when there is no room for another.
        if let Some(&id) = self.intern.get(&node) {
            return Some(id);
        }
        if !ADMIT || self.nodes.len() == self.node_limit {
            return None;
        }
        self.nodes.push(node);
        let id = self.nodes.len() as u32;
        self.intern.insert(node, id);
        Some(id)
    }

    fn stable_id<const ADMIT: bool>(
        &mut self,
        arena: &Arena,
        store: &Store<'_>,
        v: V,
        depth: u32,
    ) -> Option<u32> {
        let i = v.0 as usize;
        if let Some(&key) = self.keys.get(i)
            && key != UNKNOWN
        {
            return Some(key);
        }
        if depth == 0 || arena.has_fvar(v) {
            return None;
        }
        let key = self.build_id::<ADMIT>(arena, store, v, depth - 1)?;
        if self.keys.len() <= i {
            self.keys.resize(i + 1, UNKNOWN);
        }
        self.keys[i] = key;
        Some(key)
    }

    fn build_id<const ADMIT: bool>(
        &mut self,
        arena: &Arena,
        store: &Store<'_>,
        v: V,
        depth: u32,
    ) -> Option<u32> {
        let node = match arena.get(v) {
            Val::Sort(l) if !store.level_has_param(l) => {
                if let Some(id) = direct(DIRECT_SORT, l.0) {
                    return Some(id);
                }
                Node::Sort(self.level::<ADMIT>(store, l, depth)?)
            }
            Val::Nat(lo, hi) => {
                if hi == 0
                    && let Some(id) = direct(DIRECT_NAT, lo)
                {
                    return Some(id);
                }
                Node::Nat(lo, hi)
            }
            Val::Str(s) => Node::Str(s),
            Val::Const(n, ls, sp) if !is_local(n.0) && !store.list_has_param(ls) => {
                let ls = self.level_list::<ADMIT>(store, ls)?;
                let mut id = if ls == LevelList::EMPTY
                    && let Some(id) = direct(DIRECT_CONST, n.0)
                {
                    id
                } else {
                    self.intern::<ADMIT>(Node::Const(n, ls))?
                };
                let len = arena.sp_len(sp);
                if len > MAX_DEPTH {
                    return None;
                }
                for i in 0..len {
                    let node = match arena.sp_elim(sp, i) {
                        Elim::Arg(a) => {
                            Node::App(id, self.stable_id::<ADMIT>(arena, store, a, depth)?)
                        }
                        Elim::Proj(n, i) if !is_local(n.0) => Node::Proj(n, i, id),
                        Elim::Proj(..) => return None,
                    };
                    id = self.intern::<ADMIT>(node)?;
                }
                return Some(id);
            }
            kind @ (Val::Lam(e, env, ls) | Val::Pi(e, env, ls) | Val::Thunk(e, env, ls))
                if !store.is_local_expr(e) =>
            {
                let data = store.data(e);
                let len = data.loose_bvar_range();
                if data.has_fvar() || len > arena.env_len(env) || len > MAX_DEPTH {
                    return None;
                }
                let subst = if data.has_level_param() {
                    self.closed_substitution::<ADMIT>(arena, store, e, ls)?
                } else {
                    0
                };
                if len == 0 && subst == 0 {
                    let tag = match kind {
                        Val::Lam(..) => DIRECT_LAM,
                        Val::Pi(..) => DIRECT_PI,
                        _ => DIRECT_THUNK,
                    };
                    if let Some(id) = direct(tag, e.0) {
                        return Some(id);
                    }
                }
                // Indices outside this prefix cannot occur in the expression.
                let mut captures = 0;
                for i in (0..len).rev() {
                    let value =
                        self.stable_id::<ADMIT>(arena, store, arena.lookup(env, i)?, depth)?;
                    captures = self.intern::<ADMIT>(Node::Capture(value, captures))?;
                }
                match kind {
                    Val::Lam(..) => Node::Lam(e, captures, subst),
                    Val::Pi(..) => Node::Pi(e, captures, subst),
                    _ => Node::Thunk(e, captures, subst),
                }
            }
            _ => return None,
        };
        self.intern::<ADMIT>(node)
    }

    fn closed_substitution<const ADMIT: bool>(
        &mut self,
        arena: &Arena,
        store: &Store<'_>,
        e: ExprId,
        ls: Ls,
    ) -> Option<u32> {
        if ls == Ls::ID {
            return None;
        }
        let subst = arena.ls(ls);
        let params = subst.params;
        let id = match self.substitutions.get(&ls) {
            Some(&id) => id,
            None => {
                if is_local(params.start)
                    || params.len() != store.list(subst.levels).len()
                    || store.list_has_param(subst.levels)
                {
                    return None;
                }
                let levels = self.level_list::<ADMIT>(store, subst.levels)?;
                let id =
                    self.intern::<ADMIT>(Node::Substitution(params.start, params.len, levels))?;
                if self.substitutions.len() < MAX_ARENA_MEMOS {
                    self.substitutions.insert(ls, id);
                }
                id
            }
        };
        self.parameters_covered(store, e, params, MAX_DEPTH)
            .then_some(id)
    }

    /// Every universe parameter in this global expression must occur in
    /// the substitution. Unsubstituted parameters would need a context.
    fn parameters_covered(
        &mut self,
        store: &Store<'_>,
        e: ExprId,
        params: NameList,
        depth: u32,
    ) -> bool {
        if !store.data(e).has_level_param() {
            return true;
        }
        let k = (e, u64::from(params.start) << 32 | u64::from(params.len));
        if let Some(&covered) = self.checked_parameters.get(&k) {
            return covered;
        }
        if depth == 0 || self.checked_parameters.len() >= self.node_limit / 4 {
            return false;
        }
        let names = store.name_list(params);
        let mut fuel = MAX_DEPTH;
        let covered = match store.node(e) {
            ExprNode::Sort(l) => Self::level_covered(store, l, names, &mut fuel),
            ExprNode::Const(_, ls) => store
                .list(ls)
                .iter()
                .all(|&l| Self::level_covered(store, l, names, &mut fuel)),
            ExprNode::App(a, b) | ExprNode::Lam(_, _, a, b) | ExprNode::Pi(_, _, a, b) => {
                self.parameters_covered(store, a, params, depth - 1)
                    && self.parameters_covered(store, b, params, depth - 1)
            }
            ExprNode::Let(l, b) => {
                let binder = store.let_binder(l);
                self.parameters_covered(store, binder.ty, params, depth - 1)
                    && self.parameters_covered(store, binder.value, params, depth - 1)
                    && self.parameters_covered(store, b, params, depth - 1)
            }
            ExprNode::Proj(_, _, e) => self.parameters_covered(store, e, params, depth - 1),
            _ => false,
        };
        self.checked_parameters.insert(k, covered);
        covered
    }

    fn level_covered(store: &Store<'_>, level: LevelId, names: &[NameId], fuel: &mut u32) -> bool {
        if !store.level_has_param(level) {
            return true;
        }
        if *fuel == 0 {
            return false;
        }
        *fuel -= 1;
        match store.level(level) {
            LevelNode::Param(name) => names.contains(&name),
            LevelNode::Succ(a) => Self::level_covered(store, a, names, fuel),
            LevelNode::Max(a, b) | LevelNode::IMax(a, b) => {
                Self::level_covered(store, a, names, fuel)
                    && Self::level_covered(store, b, names, fuel)
            }
            LevelNode::Zero => true,
        }
    }

    /// Global ids are already stable. A local level or list uses the
    /// local-id bit to tag an index into the persistent nodes instead.
    fn level<const ADMIT: bool>(
        &mut self,
        store: &Store<'_>,
        l: LevelId,
        depth: u32,
    ) -> Option<LevelId> {
        if !is_local(l.0) {
            return Some(l);
        }
        if depth == 0 {
            return None;
        }
        if let Some(&r) = self.levels.get(&l) {
            return Some(r);
        }
        if self.levels.len() >= MAX_ARENA_MEMOS {
            return None;
        }
        let r = self.intern_level::<ADMIT>(store, l, depth)?;
        if self.levels.len() < MAX_ARENA_MEMOS {
            self.levels.insert(l, r);
        }
        Some(r)
    }

    fn intern_level<const ADMIT: bool>(
        &mut self,
        store: &Store<'_>,
        l: LevelId,
        depth: u32,
    ) -> Option<LevelId> {
        let node = match store.level(l) {
            LevelNode::Zero => return Some(LevelId::ZERO),
            LevelNode::Succ(a) => Node::LevelSucc(self.level::<ADMIT>(store, a, depth - 1)?),
            LevelNode::Max(a, b) => Node::LevelMax(
                self.level::<ADMIT>(store, a, depth - 1)?,
                self.level::<ADMIT>(store, b, depth - 1)?,
            ),
            LevelNode::IMax(a, b) => Node::LevelIMax(
                self.level::<ADMIT>(store, a, depth - 1)?,
                self.level::<ADMIT>(store, b, depth - 1)?,
            ),
            LevelNode::Param(_) => return None,
        };
        self.intern::<ADMIT>(node).map(|id| LevelId(id | LOCAL))
    }

    fn level_list<const ADMIT: bool>(
        &mut self,
        store: &Store<'_>,
        ls: LevelList,
    ) -> Option<LevelList> {
        if !is_local(ls.0) {
            return Some(ls);
        }
        let mut tail = LevelList::EMPTY;
        let levels = store.list(ls);
        if levels.len() > MAX_DEPTH as usize {
            return None;
        }
        for &l in levels.iter().rev() {
            let key = self.level::<ADMIT>(store, l, MAX_DEPTH)?;
            tail = LevelList(self.intern::<ADMIT>(Node::LevelCons(key, tail))? | LOCAL);
        }
        Some(tail)
    }

    fn restore(
        &mut self,
        arena: &mut Arena,
        store: &mut Store<'_>,
        id: u32,
        depth: u32,
    ) -> Option<V> {
        if let Some(&v) = self.restored.get(&id) {
            return Some(v);
        }
        if depth == 0 {
            return None;
        }
        let value = id & DIRECT_MASK;
        match id >> DIRECT_SHIFT {
            DIRECT_LAM => return Some(arena.mk(Val::Lam(ExprId(value), Env::NIL, Ls::ID))),
            DIRECT_PI => return Some(arena.mk(Val::Pi(ExprId(value), Env::NIL, Ls::ID))),
            DIRECT_THUNK => return Some(arena.mk(Val::Thunk(ExprId(value), Env::NIL, Ls::ID))),
            DIRECT_CONST => return Some(arena.cnst(NameId(value), LevelList::EMPTY)),
            DIRECT_SORT => return Some(arena.sort(LevelId(value))),
            DIRECT_NAT => return Some(arena.mk(Val::Nat(value, 0))),
            _ => {}
        }
        let node = self.nodes[(id - 1) as usize];
        let v = match node {
            Node::Sort(l) => arena.sort(self.restore_level(store, l, MAX_DEPTH)?),
            Node::Nat(lo, hi) => arena.mk(Val::Nat(lo, hi)),
            Node::Str(s) => arena.mk(Val::Str(s)),
            Node::Const(n, ls) => arena.cnst(n, self.restore_list(store, ls)?),
            Node::App(f, a) => {
                let f = self.restore(arena, store, f, depth - 1)?;
                let a = self.restore(arena, store, a, depth - 1)?;
                let head = arena.get(f);
                arena.neutral(head, &[a])
            }
            Node::Proj(n, i, x) => {
                let x = self.restore(arena, store, x, depth - 1)?;
                let Val::Const(c, ls, sp) = arena.get(x) else {
                    unreachable!("a stored spine has a constant head")
                };
                let sp = arena.snoc(sp, Elim::Proj(n, i));
                arena.mk(Val::Const(c, ls, sp))
            }
            Node::Lam(e, captures, ls)
            | Node::Pi(e, captures, ls)
            | Node::Thunk(e, captures, ls) => {
                let env = self.restore_env(arena, store, captures, depth - 1)?;
                let ls = if ls == 0 {
                    Ls::ID
                } else {
                    let Node::Substitution(start, len, levels) = self.nodes[(ls - 1) as usize]
                    else {
                        unreachable!("a stored closure has a substitution")
                    };
                    let levels = self.restore_list(store, levels)?;
                    arena.mk_ls(NameList { start, len }, levels)
                };
                let value = match node {
                    Node::Lam(..) => Val::Lam(e, env, ls),
                    Node::Pi(..) => Val::Pi(e, env, ls),
                    _ => Val::Thunk(e, env, ls),
                };
                arena.mk(value)
            }
            _ => unreachable!("a stored query value is a value node"),
        };
        self.restored.insert(id, v);
        Some(v)
    }

    fn restore_env(
        &mut self,
        arena: &mut Arena,
        store: &mut Store<'_>,
        id: u32,
        depth: u32,
    ) -> Option<Env> {
        if id == 0 {
            return Some(Env::NIL);
        }
        if depth == 0 {
            return None;
        }
        let Node::Capture(value, rest) = self.nodes[(id - 1) as usize] else {
            unreachable!("an environment must contain captures")
        };
        let tail = self.restore_env(arena, store, rest, depth - 1)?;
        let v = self.restore(arena, store, value, depth - 1)?;
        Some(arena.cons(tail, v))
    }

    fn restore_level(&mut self, store: &mut Store<'_>, l: LevelId, depth: u32) -> Option<LevelId> {
        if !is_local(l.0) {
            return Some(l);
        }
        if let Some(&r) = self.restored_levels.get(&l) {
            return Some(r);
        }
        if depth == 0 {
            return None;
        }
        let node = match self.nodes[((l.0 & !LOCAL) - 1) as usize] {
            Node::LevelSucc(a) => LevelNode::Succ(self.restore_level(store, a, depth - 1)?),
            Node::LevelMax(a, b) => LevelNode::Max(
                self.restore_level(store, a, depth - 1)?,
                self.restore_level(store, b, depth - 1)?,
            ),
            Node::LevelIMax(a, b) => LevelNode::IMax(
                self.restore_level(store, a, depth - 1)?,
                self.restore_level(store, b, depth - 1)?,
            ),
            _ => unreachable!("a stored level is a level node"),
        };
        let r = store.mk_level(node);
        self.restored_levels.insert(l, r);
        Some(r)
    }

    fn restore_list(&mut self, store: &mut Store<'_>, mut ls: LevelList) -> Option<LevelList> {
        if !is_local(ls.0) {
            return Some(ls);
        }
        let mut levels = Vec::new();
        while is_local(ls.0) {
            let Node::LevelCons(head, tail) = self.nodes[((ls.0 & !LOCAL) - 1) as usize] else {
                unreachable!("a stored list is a level cons")
            };
            levels.push(self.restore_level(store, head, MAX_DEPTH)?);
            ls = tail;
        }
        Some(store.mk_list(&levels))
    }
}

impl Drop for Queries {
    fn drop(&mut self) {
        if self.profile {
            eprintln!(
                "stable-queries: nodes={} equal={} reducts={} rotations={} equality_hits={} whnf_hits={}",
                self.nodes.len(),
                self.equal.len(),
                self.reduct.len(),
                self.rotations,
                self.eq_hits,
                self.whnf_hits
            );
        }
    }
}

impl Nbe<'_> {
    fn stable_query<const ADMIT: bool>(&mut self, v: V) -> Option<u32> {
        if self.eval_probe || self.a.has_fvar(v) {
            return None;
        }
        self.stable_queries
            .as_mut()?
            .stable_id::<ADMIT>(&self.a, &self.st, v, MAX_DEPTH)
    }

    fn stable_pair<const ADMIT: bool>(&mut self, t: V, s: V) -> Option<(u32, u32)> {
        if self.a.has_fvar(s) {
            return None;
        }
        let a = self.stable_query::<ADMIT>(t)?;
        let b = self.stable_query::<ADMIT>(s)?;
        Some((a.min(b), a.max(b)))
    }

    pub(super) fn stable_eq_hit(&mut self, t: V, s: V) -> bool {
        let Some(key) = self.stable_pair::<false>(t, s) else {
            return false;
        };
        let cache = self.stable_queries.as_mut().expect("valid key");
        let hit = cache.equal.get(&key).is_some_and(|&at| at < self.limit);
        if cache.profile {
            cache.eq_hits += u64::from(hit);
        }
        hit
    }

    pub(super) fn record_stable_eq(&mut self, t: V, s: V, start: u64) {
        if self.ticks - start >= MIN_TICKS
            && let Some(key) = self.stable_pair::<true>(t, s)
        {
            let cache = self.stable_queries.as_mut().expect("valid key");
            if cache.equal.len() < cache.node_limit / 2 {
                cache.equal.entry(key).or_insert(self.limit);
            }
        }
    }

    pub(super) fn stable_reduct(&mut self, value: V) -> Option<V> {
        let key = self.stable_query::<false>(value)?;
        let cache = self.stable_queries.as_mut()?;
        let (id, at) = *cache.reduct.get(&key)?;
        if at >= self.limit {
            return None;
        }
        let result = cache.restore(&mut self.a, &mut self.st, id, MAX_DEPTH);
        if cache.profile {
            cache.whnf_hits += u64::from(result.is_some());
        }
        result
    }

    pub(super) fn record_stable_reduct(&mut self, value: V, reduct: V, start: u64) {
        if self.ticks - start >= MIN_TICKS
            && let Some(key) = self.stable_query::<true>(value)
            && let Some(id) = self.stable_query::<true>(reduct)
            && key != id
        {
            let cache = self.stable_queries.as_mut().expect("valid key");
            if cache.reduct.len() < cache.node_limit / 2 {
                cache.reduct.entry(key).or_insert((id, self.limit));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::Env as KernelEnv;
    use crate::expr::{BinderInfo, ExprNode};
    use crate::name::NameNode;

    #[test]
    fn closed_keys_and_captures_survive_arena_reset() {
        let mut env = KernelEnv::new();
        let sort = env
            .exprs
            .intern(ExprNode::Sort(LevelId::ZERO), &env.levels)
            .unwrap()
            .0;
        let captured = env.exprs.intern(ExprNode::BVar(1), &env.levels).unwrap().0;
        let lam = env
            .exprs
            .intern(
                ExprNode::Lam(BinderInfo::Default, NameId::ANON, sort, captured),
                &env.levels,
            )
            .unwrap()
            .0;
        let ext = crate::check::Ext::with_decls(&env, &[]);
        let mut nb = Nbe::new(Store::new(&env), &ext);
        nb.stable_queries = Some(Queries::new(MAX_NODES, false));
        nb.reset(1);

        let open = nb.bottom(super::super::val::Sp::NIL);
        assert!(nb.stable_query::<true>(open).is_none());
        let input = nb.a.mk(Val::Nat(7, 0));
        let env = nb.a.cons(Env::NIL, input);
        let closure = nb.a.mk(Val::Lam(lam, env, Ls::ID));
        let key = nb.stable_query::<true>(closure).unwrap();
        let other = nb.a.mk(Val::Nat(8, 0));
        let other_env = nb.a.cons(Env::NIL, other);
        let other_closure = nb.a.mk(Val::Lam(lam, other_env, Ls::ID));
        assert_ne!(nb.stable_query::<true>(other_closure).unwrap(), key);
        nb.ticks += MIN_TICKS;
        nb.record_stable_eq(closure, closure, nb.ticks - MIN_TICKS);
        assert!(!nb.stable_eq_hit(closure, closure));

        nb.reset(2);
        let restored = nb
            .stable_queries
            .as_mut()
            .unwrap()
            .restore(&mut nb.a, &mut nb.st, key, MAX_DEPTH)
            .unwrap();
        assert_eq!(nb.stable_query::<false>(restored), Some(key));
        assert!(nb.stable_eq_hit(restored, restored));
        let arg = nb.a.mk(Val::Nat(42, 0));
        let result = nb.apply(restored, arg);
        assert_eq!(nb.a.get(result), Val::Nat(7, 0));
    }

    #[test]
    fn universe_arguments_must_cover_the_expression_and_be_ground() {
        let mut env = KernelEnv::new();
        let u = env.names.intern(NameNode::Num(NameId::ANON, 1)).unwrap().0;
        let v = env.names.intern(NameNode::Num(NameId::ANON, 2)).unwrap().0;
        let us = env.push_names(&[u]).unwrap();
        let vs = env.push_names(&[v]).unwrap();
        let param = env.levels.intern(LevelNode::Param(u)).unwrap().0;
        let sort = env
            .exprs
            .intern(ExprNode::Sort(param), &env.levels)
            .unwrap()
            .0;
        let ext = crate::check::Ext::with_decls(&env, &[]);
        let mut nb = Nbe::new(Store::new(&env), &ext);
        nb.stable_queries = Some(Queries::new(MAX_NODES, false));
        let zero = nb.st.mk_list(&[LevelId::ZERO]);
        let succ = nb.st.mk_level(LevelNode::Succ(LevelId::ZERO));
        let one = nb.st.mk_list(&[succ]);
        let symbolic = nb.st.mk_list(&[param]);

        let zero_subst = nb.a.mk_ls(us, zero);
        let one_subst = nb.a.mk_ls(us, one);
        let zero_thunk = nb.a.mk(Val::Thunk(sort, Env::NIL, zero_subst));
        let one_thunk = nb.a.mk(Val::Thunk(sort, Env::NIL, one_subst));
        let zero_key = nb.stable_query::<true>(zero_thunk).unwrap();
        let one_key = nb.stable_query::<true>(one_thunk).unwrap();
        assert_ne!(zero_key, one_key);

        let unbound = nb.a.mk_ls(vs, zero);
        let symbolic = nb.a.mk_ls(us, symbolic);
        for subst in [Ls::ID, unbound, symbolic] {
            let thunk = nb.a.mk(Val::Thunk(sort, Env::NIL, subst));
            assert!(nb.stable_query::<true>(thunk).is_none());
        }

        nb.reset(2);
        for (key, level) in [(zero_key, LevelId::ZERO), (one_key, succ)] {
            let thunk = nb
                .stable_queries
                .as_mut()
                .unwrap()
                .restore(&mut nb.a, &mut nb.st, key, MAX_DEPTH)
                .unwrap();
            let result = nb.force(thunk);
            assert_eq!(nb.a.get(result), Val::Sort(level));
        }
    }

    #[test]
    fn rotating_the_node_table_clears_facts_before_reusing_ids() {
        let env = KernelEnv::new();
        let ext = crate::check::Ext::with_decls(&env, &[]);
        let mut nb = Nbe::new(Store::new(&env), &ext);
        nb.stable_queries = Some(Queries::new(2, false));
        nb.reset(1);
        let input = nb.a.mk(Val::Nat(0, 1));
        let first = nb.stable_query::<true>(input).unwrap();
        nb.ticks += MIN_TICKS;
        nb.record_stable_eq(input, input, nb.ticks - MIN_TICKS);

        nb.reset(2);
        let other = nb.a.mk(Val::Nat(1, 1));
        assert_eq!(nb.stable_query::<true>(other), Some(first));
        assert!(!nb.stable_eq_hit(other, other));
    }
}
