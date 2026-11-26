//! Exact structural ids for closed values. The persistent table contains
//! only immutable export expressions, names and levels, and its own ids.
//! Each worker uses one immutable environment. An equality or reduction
//! established under an earlier prefix still holds under a larger prefix
//! of that environment.

use crate::expr::ExprId;
use crate::level::{LevelId, LevelList};
use crate::name::NameId;

use super::super::store::{IdMap, Store, is_local};
use super::Nbe;
use super::val::{Arena, Elim, Env, Ls, V, Val};

const MAX_NODES: usize = 1 << 18;
const MAX_QUERIES: usize = 1 << 17;
const MAX_DEPTH: u32 = 64;
const UNKNOWN: u32 = u32::MAX;
const UNSUPPORTED: u32 = 0;
const MIN_TICKS: u64 = 8;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Node {
    Sort(LevelId),
    Nat(u32, u32),
    Const(NameId, LevelList),
    App(u32, u32),
    Proj(NameId, u32, u32),
    Lam(ExprId, u32),
    Pi(ExprId, u32),
    Thunk(ExprId, u32),
    Capture(u32, u32),
}

#[derive(Default)]
pub(super) struct Queries {
    intern: hashbrown::HashMap<Node, u32>,
    nodes: Vec<Node>,
    // These maps hold arena ids and are cleared when the arena is cleared.
    keys: Vec<u32>,
    restored: IdMap<u32, V>,
    // The remaining maps use only persistent ids and record the prefix
    // in which the kernel established a positive result.
    equal: IdMap<(u32, u32), u32>,
    reduct: IdMap<u32, (u32, u32)>,
    profile: bool,
    eq_hits: u64,
    whnf_hits: u64,
}

impl Queries {
    pub fn from_env() -> Option<Box<Self>> {
        let mode = std::env::var("NITROLEAN_STABLE_QUERIES");
        if let Ok(mode @ ("1" | "stats")) = mode.as_deref() {
            let mut cache = Box::<Self>::default();
            cache.profile = mode == "stats";
            Some(cache)
        } else {
            None
        }
    }

    pub fn reset(&mut self) {
        self.keys.clear();
        self.restored.clear();
    }

    fn intern(&mut self, node: Node) -> Option<u32> {
        // Reuse existing nodes even when there is no room for another.
        if let Some(&id) = self.intern.get(&node) {
            return Some(id);
        }
        if self.nodes.len() == MAX_NODES {
            return None;
        }
        self.nodes.push(node);
        let id = self.nodes.len() as u32;
        self.intern.insert(node, id);
        Some(id)
    }

    fn stable_id(&mut self, arena: &Arena, store: &Store<'_>, v: V, depth: u32) -> Option<u32> {
        let i = v.0 as usize;
        if let Some(&key) = self.keys.get(i)
            && key != UNKNOWN
        {
            return (key != UNSUPPORTED).then_some(key);
        }
        if depth == 0 || arena.has_fvar(v) {
            return None;
        }
        let key = self.build_id(arena, store, v, depth - 1);
        if self.keys.len() <= i {
            self.keys.resize(i + 1, UNKNOWN);
        }
        self.keys[i] = key.unwrap_or(UNSUPPORTED);
        key
    }

    fn build_id(&mut self, arena: &Arena, store: &Store<'_>, v: V, depth: u32) -> Option<u32> {
        let node = match arena.get(v) {
            Val::Sort(l) if !is_local(l.0) && !store.level_has_param(l) => Node::Sort(l),
            Val::Nat(lo, hi) => Node::Nat(lo, hi),
            Val::Const(n, ls, sp)
                if !is_local(n.0) && !is_local(ls.0) && !store.list_has_param(ls) =>
            {
                let mut id = self.intern(Node::Const(n, ls))?;
                let len = arena.sp_len(sp);
                if len > MAX_DEPTH {
                    return None;
                }
                for i in 0..len {
                    let node = match arena.sp_elim(sp, i) {
                        Elim::Arg(a) => Node::App(id, self.stable_id(arena, store, a, depth)?),
                        Elim::Proj(n, i) if !is_local(n.0) => Node::Proj(n, i, id),
                        Elim::Proj(..) => return None,
                    };
                    id = self.intern(node)?;
                }
                return Some(id);
            }
            kind @ (Val::Lam(e, env, Ls::ID)
            | Val::Pi(e, env, Ls::ID)
            | Val::Thunk(e, env, Ls::ID))
                if !store.is_local_expr(e) =>
            {
                let data = store.data(e);
                let len = data.loose_bvar_range();
                if data.has_fvar()
                    || data.has_level_param()
                    || len > arena.env_len(env)
                    || len > MAX_DEPTH
                {
                    return None;
                }
                // Indices outside this prefix cannot occur in the expression.
                let mut captures = 0;
                for i in (0..len).rev() {
                    let value = self.stable_id(arena, store, arena.lookup(env, i)?, depth)?;
                    captures = self.intern(Node::Capture(value, captures))?;
                }
                match kind {
                    Val::Lam(..) => Node::Lam(e, captures),
                    Val::Pi(..) => Node::Pi(e, captures),
                    _ => Node::Thunk(e, captures),
                }
            }
            _ => return None,
        };
        self.intern(node)
    }

    fn restore(&mut self, arena: &mut Arena, id: u32, depth: u32) -> Option<V> {
        if let Some(&v) = self.restored.get(&id) {
            return Some(v);
        }
        if depth == 0 {
            return None;
        }
        let node = self.nodes[(id - 1) as usize];
        let v = match node {
            Node::Sort(l) => arena.sort(l),
            Node::Nat(lo, hi) => arena.mk(Val::Nat(lo, hi)),
            Node::Const(n, ls) => arena.cnst(n, ls),
            Node::App(f, a) => {
                let f = self.restore(arena, f, depth - 1)?;
                let a = self.restore(arena, a, depth - 1)?;
                let head = arena.get(f);
                arena.neutral(head, &[a])
            }
            Node::Proj(n, i, x) => {
                let x = self.restore(arena, x, depth - 1)?;
                let Val::Const(c, ls, sp) = arena.get(x) else {
                    unreachable!("a stored spine has a constant head")
                };
                let sp = arena.snoc(sp, Elim::Proj(n, i));
                arena.mk(Val::Const(c, ls, sp))
            }
            Node::Lam(e, captures) | Node::Pi(e, captures) | Node::Thunk(e, captures) => {
                let env = self.restore_env(arena, captures, depth - 1)?;
                let value = match node {
                    Node::Lam(..) => Val::Lam(e, env, Ls::ID),
                    Node::Pi(..) => Val::Pi(e, env, Ls::ID),
                    _ => Val::Thunk(e, env, Ls::ID),
                };
                arena.mk(value)
            }
            Node::Capture(..) => unreachable!("a capture is not a value"),
        };
        self.restored.insert(id, v);
        Some(v)
    }

    fn restore_env(&mut self, arena: &mut Arena, id: u32, depth: u32) -> Option<Env> {
        if id == 0 {
            return Some(Env::NIL);
        }
        if depth == 0 {
            return None;
        }
        let Node::Capture(value, rest) = self.nodes[(id - 1) as usize] else {
            unreachable!("an environment must contain captures")
        };
        let tail = self.restore_env(arena, rest, depth - 1)?;
        let v = self.restore(arena, value, depth - 1)?;
        Some(arena.cons(tail, v))
    }
}

impl Drop for Queries {
    fn drop(&mut self) {
        if self.profile {
            eprintln!(
                "stable-queries: nodes={} equal={} reducts={} equality_hits={} whnf_hits={}",
                self.nodes.len(),
                self.equal.len(),
                self.reduct.len(),
                self.eq_hits,
                self.whnf_hits
            );
        }
    }
}

impl Nbe<'_> {
    pub(super) fn stable_query(&mut self, v: V) -> Option<u32> {
        if self.eval_probe || self.a.has_fvar(v) {
            return None;
        }
        self.stable_queries
            .as_mut()?
            .stable_id(&self.a, &self.st, v, MAX_DEPTH)
    }

    pub(super) fn stable_eq_hit(&mut self, key: (u32, u32)) -> bool {
        let cache = self.stable_queries.as_mut().expect("valid key");
        let hit = cache.equal.get(&key).is_some_and(|&at| at < self.limit);
        if cache.profile {
            cache.eq_hits += u64::from(hit);
        }
        hit
    }

    pub(super) fn record_stable_eq(&mut self, key: (u32, u32), start: u64) {
        if self.ticks - start >= MIN_TICKS {
            let cache = self.stable_queries.as_mut().expect("valid key");
            if cache.equal.len() < MAX_QUERIES {
                cache.equal.entry(key).or_insert(self.limit);
            }
        }
    }

    pub(super) fn stable_reduct(&mut self, key: u32) -> Option<V> {
        let cache = self.stable_queries.as_mut()?;
        let (id, at) = *cache.reduct.get(&key)?;
        if at >= self.limit {
            return None;
        }
        let result = cache.restore(&mut self.a, id, MAX_DEPTH);
        if cache.profile {
            cache.whnf_hits += u64::from(result.is_some());
        }
        result
    }

    pub(super) fn record_stable_reduct(&mut self, key: u32, reduct: V, start: u64) {
        if self.ticks - start >= MIN_TICKS
            && let Some(id) = self.stable_query(reduct)
            && key != id
        {
            let cache = self.stable_queries.as_mut().expect("valid key");
            if cache.reduct.len() < MAX_QUERIES {
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
        nb.stable_queries = Some(Box::default());
        nb.reset(1);

        let open = nb.bottom(super::super::val::Sp::NIL);
        assert!(nb.stable_query(open).is_none());
        let input = nb.a.mk(Val::Nat(7, 0));
        let env = nb.a.cons(Env::NIL, input);
        let closure = nb.a.mk(Val::Lam(lam, env, Ls::ID));
        let key = nb.stable_query(closure).unwrap();
        let other = nb.a.mk(Val::Nat(8, 0));
        let other_env = nb.a.cons(Env::NIL, other);
        let other_closure = nb.a.mk(Val::Lam(lam, other_env, Ls::ID));
        assert_ne!(nb.stable_query(other_closure).unwrap(), key);
        let pair = (key, key);
        nb.ticks += MIN_TICKS;
        nb.record_stable_eq(pair, nb.ticks - MIN_TICKS);
        assert!(!nb.stable_eq_hit(pair));

        nb.reset(2);
        assert!(nb.stable_eq_hit(pair));
        let restored = nb
            .stable_queries
            .as_mut()
            .unwrap()
            .restore(&mut nb.a, key, MAX_DEPTH)
            .unwrap();
        assert_eq!(nb.stable_query(restored), Some(key));
        let arg = nb.a.mk(Val::Nat(42, 0));
        let result = nb.apply(restored, arg);
        assert_eq!(nb.a.get(result), Val::Nat(7, 0));
    }
}
