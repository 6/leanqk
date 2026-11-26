//! Small, fast, non-cryptographic hashing for the hash-consing tables.
//!
//! Arena nodes refer to their children by canonical id, so a node's hash only
//! has to mix a couple of machine words; no recursion and no stored hashes.
//! The folded 64x64->128 multiply is the mixing step used by foldhash and
//! wyhash.

const K0: u64 = 0x243f_6a88_85a3_08d3;
const K1: u64 = 0x1319_8a2e_0370_7344;
const K2: u64 = 0xa409_3822_299f_31d0;

#[inline]
fn fold_mul(a: u64, b: u64) -> u64 {
    let r = (a as u128).wrapping_mul(b as u128);
    (r as u64) ^ ((r >> 64) as u64)
}

/// Hash two words. The result has entropy in its high bits too, which the
/// SwissTable control bytes need.
#[inline]
pub fn hash2(w0: u64, w1: u64) -> u64 {
    fold_mul(fold_mul(w0 ^ K0, K2) ^ w1, K1)
}

/// Hash two words with one multiply, for direct-mapped tables (lossy
/// caches): their high bits only pick a slot.
#[inline]
pub fn hash_front(w0: u64, w1: u64) -> u64 {
    fold_mul(w0 ^ K0, w1 ^ K2)
}

/// Hash a byte string.
pub fn hash_bytes(bytes: &[u8]) -> u64 {
    let mut h = K2 ^ bytes.len() as u64;
    let (chunks, rest) = bytes.as_chunks::<8>();
    for c in chunks {
        h = fold_mul(h ^ u64::from_le_bytes(*c), K0);
    }
    let mut buf = [0u8; 8];
    buf[..rest.len()].copy_from_slice(rest);
    hash2(h, u64::from_le_bytes(buf))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn distinguishes_small_inputs() {
        assert_ne!(hash2(0, 1), hash2(1, 0));
        assert_ne!(hash_bytes(b"a"), hash_bytes(b"a\0"));
        assert_ne!(hash_bytes(b""), hash_bytes(b"\0"));
        assert_eq!(hash_bytes(b"Nat.succ"), hash_bytes(b"Nat.succ"));
    }
}
