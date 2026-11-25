//! Runs of application lines, the commonest record by far (four lines in
//! five of a real export), read in one loop.
//!
//! An application line is `{"app":{"arg":A,"fn":F},"ie":I}` and a
//! newline, and in an export with dense ids, `I` is the next expression
//! id. A line of another shape, or that the loop cannot take for any
//! other reason, ends the run, and the scanner reads it.

/// The eight bytes of `w` from `p` (at most 56).
#[inline(always)]
fn ld(w: &[u8; 64], p: usize) -> u64 {
    let p = p.min(56);
    u64::from_le_bytes(w[p..p + 8].try_into().expect("8 bytes"))
}

/// The constants of the loop, loaded from memory rather than built in
/// every line (see `Keys` in the scanner).
struct Consts {
    head0: u64,
    head1: u64,
    fn_: u64,
    ie: u64,
    end: u64,
    below_ten: u64,
    join: u64,
    ten: u64,
    hundred: u64,
}

static CONSTS: Consts = Consts {
    head0: u64::from_le_bytes(*b"{\"app\":{"),
    head1: u64::from_le_bytes(*b"\"arg\":\0\0"),
    fn_: u64::from_le_bytes(*b",\"fn\":\0\0"),
    ie: u64::from_le_bytes(*b"},\"ie\":\0"),
    end: u16::from_le_bytes(*b"}\n") as u64,
    below_ten: 0x7676_7676_7676_7676,
    join: 42_949_672_960_001,
    ten: 10,
    hundred: 100,
};

const MASK6: u64 = (1 << 48) - 1;
const MASK7: u64 = (1 << 56) - 1;

/// The natural number at `p` of `w` (canonical, at most 9 digits), and
/// where it ends.
#[inline(always)]
fn nat(w: &[u8; 64], p: usize, k: &Consts) -> Option<(u64, usize)> {
    let v = ld(w, p);
    let x = v ^ 0x3030_3030_3030_3030;
    // As in the scanner: the high bit of each byte that is not a digit.
    let t = (x | x.wrapping_add(k.below_ten)) & 0x8080_8080_8080_8080;
    let n8 = t.trailing_zeros() & !7;
    if n8 == 0 || (n8 > 8 && v as u8 == b'0') {
        return None;
    }
    let d = x << (64 - n8);
    let d = d.wrapping_mul(k.ten).wrapping_add(d >> 8) & 0x00FF_00FF_00FF_00FF;
    let d = d.wrapping_mul(k.hundred).wrapping_add(d >> 16) & 0x0000_FFFF_0000_FFFF;
    let d = d.wrapping_mul(k.join) >> 32;
    if n8 == 64 {
        let c = w[(p + 8).min(63)].wrapping_sub(b'0');
        if c <= 9 {
            if w[(p + 9).min(63)].is_ascii_digit() {
                return None;
            }
            return Some((d * 10 + c as u64, p + 9));
        }
    }
    Some((d, p + (n8 / 8) as usize))
}

/// The application lines at the start of `s` while their ids are `e`,
/// `e + 1`, ...: each is given to `push` (with its id, function and
/// argument), until it refuses one. How many bytes and lines it took.
#[inline(always)]
pub(super) fn apps(s: &[u8], e: u64, mut push: impl FnMut(u64, u64, u64) -> bool) -> (usize, u64) {
    let k = std::hint::black_box(&CONSTS);
    let (mut pos, mut e2) = (0, e);
    // The longest line the loop takes (three numbers of 9 digits) is 58
    // bytes.
    while let Some(w) = s.get(pos..pos + 64) {
        let w: &[u8; 64] = w.try_into().expect("64 bytes");
        if ld(w, 0) != k.head0 || ld(w, 8) & MASK6 != k.head1 {
            break;
        }
        let Some((a, q)) = nat(w, 14, k) else { break };
        if ld(w, q) & MASK6 != k.fn_ {
            break;
        }
        let Some((f, q)) = nat(w, q + 6, k) else {
            break;
        };
        if ld(w, q) & MASK7 != k.ie {
            break;
        }
        let Some((i, q)) = nat(w, q + 7, k) else {
            break;
        };
        if i != e2 || ld(w, q) & 0xFFFF != k.end || !push(i, f, a) {
            break;
        }
        pos += q + 2;
        e2 += 1;
    }
    (pos, e2 - e)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn runs_of_applications() {
        let pad = " ".repeat(64);
        let text = format!(
            "{{\"app\":{{\"arg\":3,\"fn\":7}},\"ie\":8}}\n\
             {{\"app\":{{\"arg\":123456789,\"fn\":0}},\"ie\":9}}\n\
             {{\"app\":{{\"arg\":1,\"fn\":2}},\"ie\":10}}\n\
             {{\"app\":{{\"arg\":01,\"fn\":2}},\"ie\":11}}\n{pad}"
        );
        let mut got = Vec::new();
        let (n, k) = apps(text.as_bytes(), 8, |e, f, a| {
            got.push((e, f, a));
            true
        });
        assert_eq!(got, [(8, 7, 3), (9, 0, 123456789), (10, 2, 1)]);
        assert_eq!(k, 3);
        assert!(text[n..].starts_with("{\"app\":{\"arg\":01"));
        // A wrong id, a number of ten digits, a refusal.
        for (line, e) in [
            ("{\"app\":{\"arg\":3,\"fn\":7},\"ie\":9}\n", 8),
            ("{\"app\":{\"arg\":3,\"fn\":7},\"ie\":8 }\n", 8),
            ("{\"app\":{\"arg\":1234567890,\"fn\":7},\"ie\":8}\n", 8),
            ("{\"app\":{\"arg\":3,\"fn\":7},\"ie\":80}\n", 8),
        ] {
            let text = format!("{line}{pad}");
            assert_eq!(apps(text.as_bytes(), e, |_, _, _| true), (0, 0), "{line}");
        }
        let text = format!("{{\"app\":{{\"arg\":3,\"fn\":7}},\"ie\":8}}\n{pad}");
        assert_eq!(apps(text.as_bytes(), 8, |_, _, _| false), (0, 0));
    }
}
