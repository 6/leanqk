//! Synthetic matrix certificates: a seeded random matrix and its witness.

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Zero};
use std::fmt::Write as _;

/// splitmix64, the generator the entries come from.
pub struct SplitMix64(u64);

impl SplitMix64 {
    pub fn new(seed: u64) -> Self {
        SplitMix64(seed)
    }

    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Uniform in `[0, n)`, by rejection.
    pub fn below(&mut self, n: u64) -> u64 {
        let total = 1u128 << 64;
        let limit = total - total % n as u128;
        loop {
            let x = self.next();
            if (x as u128) < limit {
                return x % n;
            }
        }
    }
}

/// What a certificate file holds.
pub enum Cert {
    /// `A * B = 1 (mod p)`.
    Inverse {
        p: u64,
        a: Vec<Vec<u64>>,
        b: Vec<Vec<u64>>,
    },
    /// `A * B = d * 1` over the integers, `d != 0`.
    Nonsingular {
        d: BigInt,
        a: Vec<Vec<i64>>,
        b: Vec<Vec<BigInt>>,
    },
}

fn mulmod(x: u64, y: u64, p: u64) -> u64 {
    ((x as u128 * y as u128) % p as u128) as u64
}

fn inv_mod(x: u64, p: u64) -> u64 {
    // extended Euclid on (x, p), p prime and x != 0 mod p
    let (mut r0, mut r1) = (p as i128, (x % p) as i128);
    let (mut t0, mut t1) = (0i128, 1i128);
    while r1 != 0 {
        let q = r0 / r1;
        (r0, r1) = (r1, r0 - q * r1);
        (t0, t1) = (t1, t0 - q * t1);
    }
    assert_eq!(r0, 1, "not invertible");
    t0.rem_euclid(p as i128) as u64
}

/// The inverse of `a` modulo the prime `p`, by Gauss-Jordan elimination.
pub fn inverse_mod(a: &[Vec<u64>], p: u64) -> Result<Vec<Vec<u64>>, String> {
    let n = a.len();
    let mut m: Vec<Vec<u64>> = (0..n)
        .map(|i| {
            a[i].iter()
                .copied()
                .chain((0..n).map(|j| u64::from(i == j)))
                .collect()
        })
        .collect();
    for k in 0..n {
        let piv = (k..n)
            .find(|&r| !m[r][k].is_multiple_of(p))
            .ok_or("the matrix is singular modulo P; use another seed")?;
        m.swap(k, piv);
        let inv = inv_mod(m[k][k], p);
        m[k] = m[k].iter().map(|&x| mulmod(x, inv, p)).collect();
        let rk = m[k].clone();
        for (i, row) in m.iter_mut().enumerate() {
            let f = row[k];
            if i != k && f != 0 {
                for (x, &y) in row.iter_mut().zip(&rk) {
                    *x = (*x + p - mulmod(f, y, p)) % p;
                }
            }
        }
    }
    Ok(m.into_iter().map(|r| r[n..].to_vec()).collect())
}

/// `(d, B)` with `A * B = d * 1`, by fraction-free Gauss-Jordan elimination on `[A | 1]`.
pub fn det_adjugate(a: &[Vec<i64>]) -> Result<(BigInt, Vec<Vec<BigInt>>), String> {
    let n = a.len();
    let mut m: Vec<Vec<BigInt>> = (0..n)
        .map(|i| {
            a[i].iter()
                .map(|&x| BigInt::from(x))
                .chain((0..n).map(|j| BigInt::from(u8::from(i == j))))
                .collect()
        })
        .collect();
    let mut prev = BigInt::one();
    for k in 0..n {
        let piv = (k..n)
            .find(|&r| !m[r][k].is_zero())
            .ok_or("the matrix is singular; use another seed")?;
        m.swap(k, piv);
        let rk = m[k].clone();
        let p = rk[k].clone();
        for (i, row) in m.iter_mut().enumerate() {
            if i == k {
                continue;
            }
            let f = row[k].clone();
            for (x, y) in row.iter_mut().zip(&rk) {
                let (q, r) = (&p * &*x - &f * y).div_mod_floor(&prev);
                assert!(r.is_zero(), "inexact division");
                *x = q;
            }
        }
        prev = p;
    }
    let d = m[0][0].clone();
    assert!((0..n).all(|i| m[i][i] == d));
    Ok((d, m.into_iter().map(|r| r[n..].to_vec()).collect()))
}

/// A random `n x n` matrix modulo `p` and its inverse.
pub fn inverse(p: u64, n: usize, seed: u64) -> Result<Cert, String> {
    let mut g = SplitMix64::new(seed);
    let a: Vec<Vec<u64>> = (0..n)
        .map(|_| (0..n).map(|_| g.below(p)).collect())
        .collect();
    let b = inverse_mod(&a, p)?;
    for (i, row) in a.iter().enumerate() {
        for j in 0..n {
            let s = row
                .iter()
                .zip(&b)
                .fold(0u64, |s, (&x, bl)| (s + mulmod(x, bl[j], p)) % p);
            assert_eq!(s, u64::from(i == j) % p, "inverse check failed");
        }
    }
    Ok(Cert::Inverse { p, a, b })
}

/// A random `n x n` integer matrix with entries in `[-bound, bound]`, its determinant and adjugate.
pub fn nonsingular(n: usize, bound: u64, seed: u64) -> Result<Cert, String> {
    let mut g = SplitMix64::new(seed);
    let a: Vec<Vec<i64>> = (0..n)
        .map(|_| {
            (0..n)
                .map(|_| g.below(2 * bound + 1) as i64 - bound as i64)
                .collect()
        })
        .collect();
    let (d, b) = det_adjugate(&a)?;
    assert!(!d.is_zero());
    for (i, row) in a.iter().enumerate() {
        for j in 0..n {
            let s: BigInt = row.iter().zip(&b).map(|(&x, bl)| &bl[j] * x).sum();
            let want = if i == j { d.clone() } else { BigInt::zero() };
            assert_eq!(s, want, "adjugate check failed");
        }
    }
    Ok(Cert::Nonsingular { d, a, b })
}

impl Cert {
    /// Changes the last entry of `B`, so that the certificate is wrong.
    pub fn corrupt(&mut self) {
        match self {
            Cert::Inverse { p, b, .. } => {
                let x = b.last_mut().and_then(|r| r.last_mut()).expect("empty");
                *x = (*x + 1) % *p;
            }
            Cert::Nonsingular { b, .. } => {
                *b.last_mut().and_then(|r| r.last_mut()).expect("empty") += 1;
            }
        }
    }

    /// The certificate file: a header line `inverse P N` or `nonsingular N D`, then the rows
    /// of `A` and of `B`, entries separated by single spaces.
    pub fn render(&self) -> String {
        fn rows<T: std::fmt::Display>(out: &mut String, m: &[Vec<T>]) {
            for r in m {
                let mut first = true;
                for x in r {
                    if !first {
                        out.push(' ');
                    }
                    first = false;
                    write!(out, "{x}").unwrap();
                }
                out.push('\n');
            }
        }
        let mut out = String::new();
        match self {
            Cert::Inverse { p, a, b } => {
                writeln!(out, "inverse {p} {}", a.len()).unwrap();
                rows(&mut out, a);
                rows(&mut out, b);
            }
            Cert::Nonsingular { d, a, b } => {
                writeln!(out, "nonsingular {} {d}", a.len()).unwrap();
                rows(&mut out, a);
                rows(&mut out, b);
            }
        }
        out
    }
}
