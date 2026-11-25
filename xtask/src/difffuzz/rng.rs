//! A small deterministic generator (SplitMix64), so that a mutant is
//! reproduced from its seed number on any machine.

pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng(seed ^ 0x9E37_79B9_7F4A_7C15)
    }

    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Uniform in [0, 1).
    pub fn random(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 / (1u64 << 53) as f64
    }

    /// Uniform in [0, n); n must be positive.
    pub fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }

    pub fn chance(&mut self, p: f64) -> bool {
        self.random() < p
    }

    pub fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }

    /// Two distinct indices of a slice of length n >= 2.
    pub fn two(&mut self, n: usize) -> (usize, usize) {
        let i = self.below(n);
        let mut j = self.below(n - 1);
        if j >= i {
            j += 1;
        }
        (i, j)
    }

    /// An index chosen with the given weights.
    pub fn weighted(&mut self, w: &[u32]) -> usize {
        let total: u64 = w.iter().map(|&x| x as u64).sum();
        let mut r = self.next_u64() % total.max(1);
        for (i, &x) in w.iter().enumerate() {
            if r < x as u64 {
                return i;
            }
            r -= x as u64;
        }
        w.len() - 1
    }
}
