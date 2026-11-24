//! Universe levels: Lean's normalization (`level.cpp`), with `mk_max` and
//! `mk_imax` simplifying as Lean's do, `is_equivalent` as equality of
//! normal forms, `is_geq`, and the syntactic `is_not_zero` and
//! `normalizes_to_zero`. These are sound but incomplete for `imax` (the
//! lean-kernel-arena corner cases `imax-nested-absorption` and
//! `imax-right-successor` are true equations they miss); leanqk follows
//! Lean's verdicts there. The tests check them against an exact decision
//! procedure (in `exact` below): whatever Lean's procedures claim must hold
//! for every assignment of the parameters.

use std::cmp::Ordering;

use crate::level::{LevelId, LevelNode};
use crate::name::NameId;

use super::store::Store;

fn to_offset(st: &Store<'_>, mut l: LevelId) -> (LevelId, u32) {
    let mut k = 0;
    while let LevelNode::Succ(a) = st.level(l) {
        l = a;
        k += 1;
    }
    (l, k)
}

fn is_explicit(st: &Store<'_>, l: LevelId) -> bool {
    to_offset(st, l).0 == LevelId::ZERO
}

fn mk_succ_n(st: &mut Store<'_>, mut l: LevelId, k: u32) -> LevelId {
    for _ in 0..k {
        l = st.succ(l);
    }
    l
}

/// Lean's `is_not_zero`.
pub fn is_not_zero(st: &Store<'_>, l: LevelId) -> bool {
    match st.level(l) {
        LevelNode::Zero | LevelNode::Param(_) => false,
        LevelNode::Succ(_) => true,
        LevelNode::Max(a, b) => is_not_zero(st, a) || is_not_zero(st, b),
        LevelNode::IMax(_, b) => is_not_zero(st, b),
    }
}

/// Lean's `normalizes_to_zero`.
pub fn normalizes_to_zero(st: &Store<'_>, l: LevelId) -> bool {
    match st.level(l) {
        LevelNode::Zero => true,
        LevelNode::Param(_) | LevelNode::Succ(_) => false,
        LevelNode::Max(a, b) => normalizes_to_zero(st, a) && normalizes_to_zero(st, b),
        LevelNode::IMax(_, b) => normalizes_to_zero(st, b),
    }
}

/// Lean's simplifying `mk_max`.
pub fn mk_max(st: &mut Store<'_>, l1: LevelId, l2: LevelId) -> LevelId {
    if is_explicit(st, l1) && is_explicit(st, l2) {
        return if to_offset(st, l1).1 >= to_offset(st, l2).1 {
            l1
        } else {
            l2
        };
    }
    if l1 == l2 {
        return l1;
    }
    if l1 == LevelId::ZERO {
        return l2;
    }
    if l2 == LevelId::ZERO {
        return l1;
    }
    if let LevelNode::Max(a, b) = st.level(l2)
        && (a == l1 || b == l1)
    {
        return l2;
    }
    if let LevelNode::Max(a, b) = st.level(l1)
        && (a == l2 || b == l2)
    {
        return l1;
    }
    let (p1, k1) = to_offset(st, l1);
    let (p2, k2) = to_offset(st, l2);
    if p1 == p2 {
        return if k1 > k2 { l1 } else { l2 };
    }
    st.max(l1, l2)
}

/// Lean's simplifying `mk_imax`.
pub fn mk_imax(st: &mut Store<'_>, l1: LevelId, l2: LevelId) -> LevelId {
    let one = st.succ(LevelId::ZERO);
    if is_not_zero(st, l2) {
        mk_max(st, l1, l2)
    } else if l2 == LevelId::ZERO {
        l2
    } else if l1 == LevelId::ZERO || l1 == one {
        l2
    } else if l1 == l2 {
        l1
    } else {
        st.imax(l1, l2)
    }
}

fn kind_rank(n: LevelNode) -> u8 {
    match n {
        LevelNode::Zero => 0,
        LevelNode::Succ(_) => 1,
        LevelNode::Max(..) => 2,
        LevelNode::IMax(..) => 3,
        LevelNode::Param(_) => 4,
    }
}

/// Lean's `is_norm_lt`: a total order in which `succ l` comes right after
/// `l` and `zero` first. Parameters are ordered by id rather than by name,
/// which gives the same normal forms up to the order of `max` arguments,
/// applied the same way on both sides of a comparison.
fn norm_cmp(st: &Store<'_>, a: LevelId, b: LevelId) -> Ordering {
    if a == b {
        return Ordering::Equal;
    }
    let (l1, k1) = to_offset(st, a);
    let (l2, k2) = to_offset(st, b);
    if l1 != l2 {
        let (n1, n2) = (st.level(l1), st.level(l2));
        let (r1, r2) = (kind_rank(n1), kind_rank(n2));
        if r1 != r2 {
            return r1.cmp(&r2);
        }
        return match (n1, n2) {
            (LevelNode::Param(x), LevelNode::Param(y)) => x.cmp(&y),
            (LevelNode::Max(x1, y1), LevelNode::Max(x2, y2))
            | (LevelNode::IMax(x1, y1), LevelNode::IMax(x2, y2)) => {
                if x1 != x2 {
                    norm_cmp(st, x1, x2)
                } else {
                    norm_cmp(st, y1, y2)
                }
            }
            _ => unreachable!(),
        };
    }
    k1.cmp(&k2)
}

fn push_max_args(st: &Store<'_>, l: LevelId, out: &mut Vec<LevelId>) {
    if let LevelNode::Max(a, b) = st.level(l) {
        push_max_args(st, a, out);
        push_max_args(st, b, out);
    } else {
        out.push(l);
    }
}

fn mk_max_list(st: &mut Store<'_>, args: &[LevelId]) -> LevelId {
    let n = args.len();
    if n == 1 {
        return args[0];
    }
    let mut r = mk_max(st, args[n - 2], args[n - 1]);
    for i in (0..n - 2).rev() {
        r = mk_max(st, args[i], r);
    }
    r
}

/// Lean's `normalize`.
pub fn normalize(st: &mut Store<'_>, l: LevelId) -> LevelId {
    let (r, k) = to_offset(st, l);
    match st.level(r) {
        LevelNode::Succ(_) => unreachable!(),
        LevelNode::Zero | LevelNode::Param(_) => l,
        LevelNode::IMax(a, b) => {
            let l1 = normalize(st, a);
            let l2 = normalize(st, b);
            let i = mk_imax(st, l1, l2);
            mk_succ_n(st, i, k)
        }
        LevelNode::Max(..) => {
            let mut todo = Vec::new();
            push_max_args(st, r, &mut todo);
            let mut args = Vec::new();
            for a in todo {
                let na = normalize(st, a);
                push_max_args(st, na, &mut args);
            }
            args.sort_by(|&a, &b| norm_cmp(st, a, b));
            let mut rargs = Vec::new();
            let mut i = 0;
            if is_explicit(st, args[i]) {
                while i + 1 < args.len() && is_explicit(st, args[i + 1]) {
                    i += 1;
                }
                let kk = to_offset(st, args[i]).1;
                let mut j = i + 1;
                while j < args.len() {
                    if to_offset(st, args[j]).1 >= kk {
                        break;
                    }
                    j += 1;
                }
                if j < args.len() {
                    i += 1;
                }
            }
            rargs.push(args[i]);
            let mut prev = to_offset(st, args[i]);
            i += 1;
            while i < args.len() {
                let cur = to_offset(st, args[i]);
                if prev.0 == cur.0 {
                    if prev.1 < cur.1 {
                        prev = cur;
                        rargs.pop();
                        rargs.push(args[i]);
                    }
                } else {
                    prev = cur;
                    rargs.push(args[i]);
                }
                i += 1;
            }
            for a in rargs.iter_mut() {
                *a = mk_succ_n(st, *a, k);
            }
            mk_max_list(st, &rargs)
        }
    }
}

/// Lean's `is_equivalent`.
pub fn equiv(st: &mut Store<'_>, a: LevelId, b: LevelId) -> bool {
    a == b || normalize(st, a) == normalize(st, b)
}

fn geq_core(st: &mut Store<'_>, l1: LevelId, l2: LevelId) -> bool {
    if l1 == l2 || l2 == LevelId::ZERO {
        return true;
    }
    if let LevelNode::Max(a, b) = st.level(l2) {
        return geq(st, l1, a) && geq(st, l1, b);
    }
    if let LevelNode::Max(a, b) = st.level(l1)
        && (geq(st, a, l2) || geq(st, b, l2))
    {
        return true;
    }
    if let LevelNode::IMax(a, b) = st.level(l2) {
        return geq(st, l1, a) && geq(st, l1, b);
    }
    if let LevelNode::IMax(_, b) = st.level(l1) {
        return geq(st, b, l2);
    }
    let (p1, k1) = to_offset(st, l1);
    let (p2, k2) = to_offset(st, l2);
    if p1 == p2 || p2 == LevelId::ZERO {
        return k1 >= k2;
    }
    if k1 == k2 && k1 > 0 {
        return geq(st, p1, p2);
    }
    false
}

/// Lean's `is_geq`: `l1 ≥ l2`.
pub fn geq(st: &mut Store<'_>, l1: LevelId, l2: LevelId) -> bool {
    let a = normalize(st, l1);
    let b = normalize(st, l2);
    geq_core(st, a, b)
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

/// An exact decision procedure for `l1 ≤ l2` over all assignments, used
/// by the tests as an oracle. Without `imax`, a level is a maximum of terms
/// `p + k` and constants `k`, and `l1 ≤ l2` iff each term of `l1` is
/// dominated by one of `l2`. `imax a b` is `0` when `b` is and `max a b`
/// otherwise; when neither is evident, split on a parameter `p` of `b`:
/// `p = 0`, or `p = p' + 1`.
#[cfg(test)]
pub mod exact {
    use super::*;

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

    /// `l = 0` for every assignment.
    pub fn is_zero(st: &Store<'_>, l: LevelId) -> bool {
        leq(st, l, LevelId::ZERO)
    }

    /// `l ≥ 1` for every assignment.
    pub fn is_never_zero(st: &mut Store<'_>, l: LevelId) -> bool {
        let one = st.succ(LevelId::ZERO);
        leq(st, one, l)
    }
}

#[cfg(test)]
mod tests {
    use super::exact::{equiv as xequiv, is_never_zero, is_zero, leq};
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
        assert!(xequiv(&st, iu0, z));
        let iu1 = st.imax(u, one);
        let mu1 = st.max(u, one);
        assert!(xequiv(&st, iu1, mu1));
        // imax u (v+1) = max u (v+1)
        let iusv = st.imax(u, sv);
        let musv = st.max(u, sv);
        assert!(xequiv(&st, iusv, musv));
        // imax u v ≠ max u v (v = 0, u = 1)
        let iuv = st.imax(u, v);
        let muv = st.max(u, v);
        assert!(!xequiv(&st, iuv, muv));
        assert!(leq(&st, iuv, muv));
        // imax u v = imax (imax u v) v
        let iiuvv = st.imax(iuv, v);
        assert!(xequiv(&st, iuv, iiuvv));
        let ivi = st.imax(v, iuv);
        assert!(xequiv(&st, iuv, ivi));
        // succ (imax u v) ≰ imax u v; succ (imax 0 v) ≠ imax 0 v
        let siuv = st.succ(iuv);
        assert!(!leq(&st, siuv, iuv));
        let i0v = st.imax(z, v);
        let si0v = st.succ(i0v);
        assert!(!xequiv(&st, i0v, si0v));
        // max is commutative and associative
        let mvu = st.max(v, u);
        assert!(xequiv(&st, muv, mvu));
        assert!(leq(&st, u, su));
        assert!(!leq(&st, su, u));
        assert!(!leq(&st, u, v));
        assert!(is_zero(&st, iu0));
        assert!(!is_zero(&st, u));
        assert!(is_never_zero(&mut st, iusv));
        assert!(!is_never_zero(&mut st, iuv));
        // imax u u = u
        let iuu = st.imax(u, u);
        assert!(xequiv(&st, iuu, u));
        let _ = NameNode::Anon;
    }

    fn random_level(st: &mut Store<'_>, ps: &[LevelId], seed: &mut u64, depth: u32) -> LevelId {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let r = (*seed >> 33) % if depth == 0 { 2 } else { 5 };
        match r {
            0 => LevelId::ZERO,
            1 => ps[((*seed >> 40) % ps.len() as u64) as usize],
            2 => {
                let a = random_level(st, ps, seed, depth - 1);
                st.succ(a)
            }
            3 => {
                let a = random_level(st, ps, seed, depth - 1);
                let b = random_level(st, ps, seed, depth - 1);
                st.max(a, b)
            }
            _ => {
                let a = random_level(st, ps, seed, depth - 1);
                let b = random_level(st, ps, seed, depth - 1);
                st.imax(a, b)
            }
        }
    }

    /// Lean's procedures are sound: what they claim holds everywhere.
    #[test]
    fn lean_procedures_are_sound() {
        let mut env = Env::new();
        let (un, vn) = setup(&mut env);
        let mut st = Store::new(&env);
        let ps = [st.param(un), st.param(vn)];
        let mut seed = 7u64;
        let (mut eqs, mut geqs) = (0, 0);
        for _ in 0..20000 {
            let a = random_level(&mut st, &ps, &mut seed, 4);
            let b = random_level(&mut st, &ps, &mut seed, 4);
            if equiv(&mut st, a, b) {
                eqs += 1;
                assert!(xequiv(&st, a, b));
            }
            if geq(&mut st, a, b) {
                geqs += 1;
                assert!(leq(&st, b, a));
            }
            if normalizes_to_zero(&st, a) {
                assert!(is_zero(&st, a));
            }
            if is_not_zero(&st, a) {
                assert!(is_never_zero(&mut st, a));
            }
        }
        assert!(eqs > 100 && geqs > 1000);
    }
}
