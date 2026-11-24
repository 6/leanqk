//! `Nat` values: machine words while they fit, big integers otherwise,
//! with the kernel's literal operations (`Tc::nat_op`). Where `Tc::nat_op`
//! raises an error (a size limit), these give up instead, so that `whnf`
//! raises it.

use std::rc::Rc;

use num_bigint::BigUint;

use super::super::ext::NatOp;
use super::super::tc::NAT_MAX_BYTES;
use super::Bail;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Nat {
    Small(u64),
    /// Always at least 2^64.
    Big(Rc<BigUint>),
}

pub enum OpResult {
    Nat(Nat),
    Bool(bool),
}

impl Nat {
    pub const ZERO: Nat = Nat::Small(0);

    pub fn small(lo: u32, hi: u32) -> Nat {
        Nat::Small((hi as u64) << 32 | lo as u64)
    }

    pub fn big(b: BigUint) -> Nat {
        match u64::try_from(&b) {
            Ok(x) => Nat::Small(x),
            Err(_) => Nat::Big(Rc::new(b)),
        }
    }

    fn to_big(&self) -> BigUint {
        match self {
            Nat::Small(x) => BigUint::from(*x),
            Nat::Big(b) => (**b).clone(),
        }
    }

    fn bits(&self) -> u64 {
        match self {
            Nat::Small(x) => 64 - x.leading_zeros() as u64,
            Nat::Big(b) => b.bits(),
        }
    }

    pub fn succ(&self) -> Nat {
        match self {
            Nat::Small(x) if *x < u64::MAX => Nat::Small(x + 1),
            _ => Nat::big(self.to_big() + 1u32),
        }
    }

    /// `n - 1`, or `None` for zero.
    pub fn pred(&self) -> Option<Nat> {
        match self {
            Nat::Small(0) => None,
            Nat::Small(x) => Some(Nat::Small(x - 1)),
            Nat::Big(b) => Some(Nat::big(&**b - 1u32)),
        }
    }
}

fn size_ok(n: Nat) -> Result<Nat, Bail> {
    if n.bits().div_ceil(8) > NAT_MAX_BYTES {
        return Err(Bail::Limit);
    }
    Ok(n)
}

fn gcd(mut a: BigUint, mut b: BigUint) -> BigUint {
    while b != BigUint::ZERO {
        let r = &a % &b;
        a = b;
        b = r;
    }
    a
}

/// `op x y`, as `Tc::nat_op` computes it.
pub fn op(op: NatOp, x: &Nat, y: &Nat) -> Result<OpResult, Bail> {
    use Nat::Small as S;
    let r = match (op, x, y) {
        (NatOp::Beq, _, _) => return Ok(OpResult::Bool(x == y)),
        (NatOp::Ble, S(a), S(b)) => return Ok(OpResult::Bool(a <= b)),
        (NatOp::Ble, _, _) => return Ok(OpResult::Bool(x.to_big() <= y.to_big())),
        (NatOp::Add, S(a), S(b)) => match a.checked_add(*b) {
            Some(c) => S(c),
            None => Nat::big(x.to_big() + y.to_big()),
        },
        (NatOp::Add, _, _) => size_ok(Nat::big(x.to_big() + y.to_big()))?,
        (NatOp::Sub, S(a), S(b)) => S(a.saturating_sub(*b)),
        (NatOp::Sub, _, _) => {
            let (a, b) = (x.to_big(), y.to_big());
            if a >= b { Nat::big(a - b) } else { Nat::ZERO }
        }
        (NatOp::Mul, S(a), S(b)) => match a.checked_mul(*b) {
            Some(c) => S(c),
            None => Nat::big(x.to_big() * y.to_big()),
        },
        (NatOp::Mul, _, _) => size_ok(Nat::big(x.to_big() * y.to_big()))?,
        (NatOp::Div, _, S(0)) => Nat::ZERO,
        (NatOp::Div, S(a), S(b)) => S(a / b),
        (NatOp::Div, _, _) => Nat::big(x.to_big() / y.to_big()),
        (NatOp::Mod, _, S(0)) => x.clone(),
        (NatOp::Mod, S(a), S(b)) => S(a % b),
        (NatOp::Mod, _, _) => Nat::big(x.to_big() % y.to_big()),
        (NatOp::Gcd, S(a), S(b)) => {
            let (mut a, mut b) = (*a, *b);
            while b != 0 {
                (a, b) = (b, a % b);
            }
            S(a)
        }
        (NatOp::Gcd, _, _) => Nat::big(gcd(x.to_big(), y.to_big())),
        (NatOp::Land, S(a), S(b)) => S(a & b),
        (NatOp::Land, _, _) => Nat::big(x.to_big() & y.to_big()),
        (NatOp::Lor, S(a), S(b)) => S(a | b),
        (NatOp::Lor, _, _) => Nat::big(x.to_big() | y.to_big()),
        (NatOp::Xor, S(a), S(b)) => S(a ^ b),
        (NatOp::Xor, _, _) => Nat::big(x.to_big() ^ y.to_big()),
        (NatOp::Pow, _, _) => {
            let k = match y {
                S(k) if *k <= u32::MAX as u64 => *k as u32,
                _ => return Err(Bail::Limit),
            };
            // `x > 1`
            if (matches!(x, Nat::Big(_)) || matches!(x, S(a) if *a > 1))
                && k != 0
                && x.bits().div_ceil(8) > NAT_MAX_BYTES / k as u64
            {
                return Err(Bail::Limit);
            }
            match x {
                S(a) => match a.checked_pow(k) {
                    Some(c) => S(c),
                    None => Nat::big(BigUint::from(*a).pow(k)),
                },
                Nat::Big(b) => Nat::big(b.pow(k)),
            }
        }
        (NatOp::ShiftLeft, S(0), _) => Nat::ZERO,
        (NatOp::ShiftLeft, _, _) => {
            let k = match y {
                S(k) if *k <= u32::MAX as u64 => *k as u32,
                _ => return Err(Bail::Limit),
            };
            if x.bits().div_ceil(8) + k as u64 / 8 + 1 > NAT_MAX_BYTES {
                return Err(Bail::Limit);
            }
            match x {
                S(a) if k < 64 && a.leading_zeros() >= k => S(a << k),
                _ => Nat::big(x.to_big() << k),
            }
        }
        (NatOp::ShiftRight, _, _) => match y {
            S(k) if *k < x.bits() => match x {
                S(a) => S(a >> k),
                Nat::Big(b) => Nat::big(&**b >> *k),
            },
            _ => Nat::ZERO,
        },
    };
    Ok(OpResult::Nat(r))
}
