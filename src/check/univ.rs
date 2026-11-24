//! Universe level comparison.
//!
//! Lean's kernel compares levels by normalizing them (`level.cpp`), which is
//! sound but incomplete for `imax` (the lean-kernel-arena corner cases
//! `imax-nested-absorption` and `imax-right-successor` are equations it
//! misses). Here `l1 ≤ l2` is decided exactly, for every assignment of
//! natural numbers to the parameters:
//!
//! * Without `imax`, a level is a maximum of terms `p + k` and constants
//!   `k`. Then `l1 ≤ l2` holds iff each term of `l1` is dominated by one of
//!   `l2`: a constant `k` by any term with offset at least `k`, and `p + k`
//!   by a term `p + k'` with `k' ≥ k` (take `p` large and the rest zero).
//! * `imax a b` is `0` when `b` is and `max a b` otherwise. When neither is
//!   evident, we split on a parameter `p` of `b`: `p = 0`, or `p = p' + 1`
//!   (writing `p'` as `p` again, since it ranges over all naturals too).
//!
//! Splitting is exponential in the number of parameters it has to split on;
//! past a fixed budget the comparison answers "not provably ≤", which is
//! sound (the checker may then reject a correct declaration, never accept a
//! wrong one). Real code never comes close.

use crate::level::{LevelId, LevelNode};
use crate::name::NameId;

use super::store::Store;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Asg {
    Zero,
    /// `p ↦ p + 1`.
    Succ,
}

type Term = (Option<NameId>, u64);

/// Most parameters split on in one comparison.
const MAX_SPLITS: usize = 16;

fn lookup(asg: &[(NameId, Asg)], p: NameId) -> Option<Asg> {
    asg.iter().rev().find(|(q, _)| *q == p).map(|&(_, a)| a)
}

/// Append the terms of `succ^k l` to `out`, or return a parameter to split on.
fn form(
    st: &Store<'_>,
    l: LevelId,
    k: u64,
    asg: &[(NameId, Asg)],
    out: &mut Vec<Term>,
) -> Result<(), NameId> {
    match st.level(l) {
        LevelNode::Zero => out.push((None, k)),
        LevelNode::Succ(a) => form(st, a, k.saturating_add(1), asg, out)?,
        LevelNode::Max(a, b) => {
            form(st, a, k, asg, out)?;
            form(st, b, k, asg, out)?;
        }
        LevelNode::Param(p) => match lookup(asg, p) {
            Some(Asg::Zero) => out.push((None, k)),
            Some(Asg::Succ) => out.push((Some(p), k.saturating_add(1))),
            None => out.push((Some(p), k)),
        },
        LevelNode::IMax(a, b) => {
            let mut fb = Vec::new();
            form(st, b, 0, asg, &mut fb)?;
            if fb.iter().any(|&(_, o)| o >= 1) {
                // `b ≥ 1` everywhere: `imax a b = max a b`.
                form(st, a, k, asg, out)?;
                out.extend(fb.into_iter().map(|(x, o)| (x, o.saturating_add(k))));
            } else if let Some(&(Some(p), _)) = fb.iter().find(|t| t.0.is_some()) {
                return Err(p);
            } else {
                // `b = 0` everywhere.
                out.push((None, k));
            }
        }
    }
    Ok(())
}

fn dominated(f1: &[Term], f2: &[Term]) -> bool {
    f1.iter().all(|&(x, k)| {
        k == 0 && x.is_none() || f2.iter().any(|&(y, k2)| k2 >= k && (x.is_none() || y == x))
    })
}

fn leq_under(st: &Store<'_>, a: LevelId, b: LevelId, asg: &mut Vec<(NameId, Asg)>) -> bool {
    let mut fa = Vec::new();
    let mut fb = Vec::new();
    let split = match form(st, a, 0, asg, &mut fa) {
        Err(p) => Some(p),
        Ok(()) => form(st, b, 0, asg, &mut fb).err(),
    };
    match split {
        None => dominated(&fa, &fb),
        Some(p) => {
            if asg.len() >= MAX_SPLITS {
                return false;
            }
            asg.push((p, Asg::Zero));
            let r = leq_under(st, a, b, asg);
            asg.pop();
            if !r {
                return false;
            }
            asg.push((p, Asg::Succ));
            let r = leq_under(st, a, b, asg);
            asg.pop();
            r
        }
    }
}

/// `a ≤ b` for every assignment of the parameters.
pub fn leq(st: &Store<'_>, a: LevelId, b: LevelId) -> bool {
    a == b || matches!(st.level(a), LevelNode::Zero) || leq_under(st, a, b, &mut Vec::new())
}

/// `a = b` for every assignment.
pub fn equiv(st: &Store<'_>, a: LevelId, b: LevelId) -> bool {
    a == b || leq(st, a, b) && leq(st, b, a)
}

/// `l = 0` for every assignment (Lean: `normalizes_to_zero`).
pub fn is_zero(st: &Store<'_>, l: LevelId) -> bool {
    leq(st, l, LevelId::ZERO)
}

/// `l ≥ 1` for every assignment (Lean's syntactic `is_not_zero`, decided).
pub fn is_never_zero(st: &mut Store<'_>, l: LevelId) -> bool {
    let one = st.succ(LevelId::ZERO);
    leq(st, one, l)
}

/// A parameter of `l` not in `ps`, if any.
pub fn undefined_param(st: &Store<'_>, l: LevelId, ps: &[NameId]) -> Option<NameId> {
    if !st.level_has_param(l) {
        return None;
    }
    match st.level(l) {
        LevelNode::Zero => None,
        LevelNode::Succ(a) => undefined_param(st, a, ps),
        LevelNode::Max(a, b) | LevelNode::IMax(a, b) => {
            undefined_param(st, a, ps).or_else(|| undefined_param(st, b, ps))
        }
        LevelNode::Param(p) => (!ps.contains(&p)).then_some(p),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::Env;
    use crate::name::NameNode;

    fn setup(env: &mut Env) -> (NameId, NameId) {
        let (u, _) = env.names.str(NameId::ANON, "u").unwrap();
        let (v, _) = env.names.str(NameId::ANON, "v").unwrap();
        (u, v)
    }

    #[test]
    fn imax_cases() {
        let mut env = Env::new();
        let (un, vn) = setup(&mut env);
        let mut st = Store::new(&env);
        let z = LevelId::ZERO;
        let one = st.succ(z);
        let u = st.param(un);
        let v = st.param(vn);
        let su = st.succ(u);
        let sv = st.succ(v);
        // imax u 0 = 0, imax u 1 = max u 1
        let iu0 = st.imax(u, z);
        assert!(equiv(&st, iu0, z));
        let iu1 = st.imax(u, one);
        let mu1 = st.max(u, one);
        assert!(equiv(&st, iu1, mu1));
        // imax u (v+1) = max u (v+1)
        let iusv = st.imax(u, sv);
        let musv = st.max(u, sv);
        assert!(equiv(&st, iusv, musv));
        // imax u v ≠ max u v (v = 0, u = 1)
        let iuv = st.imax(u, v);
        let muv = st.max(u, v);
        assert!(!equiv(&st, iuv, muv));
        assert!(leq(&st, iuv, muv));
        // imax u v = imax (imax u v) v
        let iiuvv = st.imax(iuv, v);
        assert!(equiv(&st, iuv, iiuvv));
        let ivi = st.imax(v, iuv);
        assert!(equiv(&st, iuv, ivi));
        // succ (imax u v) ≰ imax u v; succ (imax 0 v) ≠ imax 0 v
        let siuv = st.succ(iuv);
        assert!(!leq(&st, siuv, iuv));
        let i0v = st.imax(z, v);
        let si0v = st.succ(i0v);
        assert!(!equiv(&st, i0v, si0v));
        // max is commutative and associative
        let mvu = st.max(v, u);
        assert!(equiv(&st, muv, mvu));
        assert!(leq(&st, u, su));
        assert!(!leq(&st, su, u));
        assert!(!leq(&st, u, v));
        assert!(is_zero(&st, iu0));
        assert!(!is_zero(&st, u));
        assert!(is_never_zero(&mut st, iusv));
        assert!(!is_never_zero(&mut st, iuv));
        // imax u u = u
        let iuu = st.imax(u, u);
        assert!(equiv(&st, iuu, u));
        let _ = NameNode::Anon;
    }
}
