//! Runs of application and binder lines, the commonest records by far
//! (nine lines in ten of a real export), read in one loop.
//!
//! An application line is `{"app":{"arg":A,"fn":F},"ie":I}` and a
//! newline; a binder line is `{"forallE":{"binderInfo":"default",`
//! `"body":B,"name":N,"type":T},"ie":I}` or `{"ie":I,"lam":{...}}`. In an
//! export with dense ids, `I` is the next expression id. A line of
//! another shape, or that the loop cannot take for any other reason, ends
//! the run, and the scanner reads it.

use crate::expr::BinderInfo;

/// The bytes the loop looks at from a line's start: the longest line it
/// takes (a binder with five numbers of 9 digits) is 110 bytes.
const WIN: usize = 128;

/// The eight bytes of `w` from `p` (at most `WIN - 8`).
#[inline(always)]
fn ld(w: &[u8; WIN], p: usize) -> u64 {
    let p = p.min(WIN - 8);
    u64::from_le_bytes(w[p..p + 8].try_into().expect("8 bytes"))
}

/// Where the records go.
pub(super) trait Records {
    /// Application `id`; false to refuse it (and end the run).
    fn app(&mut self, id: u64, f: u64, a: u64) -> bool;

    /// Binder `id`; as [`Records::app`].
    fn binder(&mut self, id: u64, pi: bool, bi: BinderInfo, name: u64, ty: u64, body: u64) -> bool;
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
    forall: [u64; 4],
    lam: [u64; 3],
    default: u64,
    implicit: u64,
    strict: [u64; 2],
    inst: [u64; 2],
    body: u64,
    name: u64,
    ty: u64,
    lam_end: u64,
    ie_head: u64,
}

/// The eight bytes of `s` from `i` (zero past the end), as a word.
const fn word(s: &[u8], i: usize) -> u64 {
    let mut b = [0u8; 8];
    let mut j = 0;
    while j < 8 && i + j < s.len() {
        b[j] = s[i + j];
        j += 1;
    }
    u64::from_le_bytes(b)
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
    // `{"forallE":{"binderInfo":"`, 26 bytes.
    forall: {
        let s = b"{\"forallE\":{\"binderInfo\":\"";
        [word(s, 0), word(s, 8), word(s, 16), word(s, 24)]
    },
    // `,"lam":{"binderInfo":"`, 22 bytes.
    lam: {
        let s = b",\"lam\":{\"binderInfo\":\"";
        [word(s, 0), word(s, 8), word(s, 16)]
    },
    default: word(b"default\"", 0),
    implicit: word(b"implicit", 0),
    strict: [word(b"strictImplicit\"", 0), word(b"strictImplicit\"", 8)],
    inst: [word(b"instImplicit\"", 0), word(b"instImplicit\"", 8)],
    body: word(b",\"body\":", 0),
    name: word(b",\"name\":", 0),
    ty: word(b",\"type\":", 0),
    lam_end: word(b"}}\n", 0),
    ie_head: word(b"{\"ie\":", 0),
};

const MASK2: u64 = (1 << 16) - 1;
const MASK3: u64 = (1 << 24) - 1;
const MASK5: u64 = (1 << 40) - 1;
const MASK6: u64 = (1 << 48) - 1;
const MASK7: u64 = (1 << 56) - 1;

/// The natural number at `p` of `w` (canonical, at most 9 digits), and
/// where it ends.
#[inline(always)]
fn nat(w: &[u8; WIN], p: usize, k: &Consts) -> Option<(u64, usize)> {
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
        let c = w[(p + 8).min(WIN - 1)].wrapping_sub(b'0');
        if c <= 9 {
            if w[(p + 9).min(WIN - 1)].is_ascii_digit() {
                return None;
            }
            return Some((d * 10 + c as u64, p + 9));
        }
    }
    Some((d, p + (n8 / 8) as usize))
}

/// A binder's fields from `p` (its binder info's text): binder info,
/// body, name, type, and where they end.
#[inline(always)]
fn binder(w: &[u8; WIN], p: usize, k: &Consts) -> Option<(BinderInfo, u64, u64, u64, usize)> {
    let x = ld(w, p);
    // The binder info and its closing quote.
    let (bi, q) = if x == k.default {
        (BinderInfo::Default, p + 8)
    } else if x == k.implicit && w[(p + 8).min(WIN - 1)] == b'"' {
        (BinderInfo::Implicit, p + 9)
    } else if x == k.inst[0] && ld(w, p + 8) & MASK5 == k.inst[1] {
        (BinderInfo::InstImplicit, p + 13)
    } else if x == k.strict[0] && ld(w, p + 8) & MASK7 == k.strict[1] {
        (BinderInfo::StrictImplicit, p + 15)
    } else {
        return None;
    };
    if ld(w, q) != k.body {
        return None;
    }
    let (body, q) = nat(w, q + 8, k)?;
    if ld(w, q) != k.name {
        return None;
    }
    let (name, q) = nat(w, q + 8, k)?;
    if ld(w, q) != k.ty {
        return None;
    }
    let (ty, q) = nat(w, q + 8, k)?;
    Some((bi, body, name, ty, q))
}

/// The application and binder lines at the start of `s` while their ids
/// are `e`, `e + 1`, ...: each goes to `out`, until it refuses one. How
/// many bytes and lines it took.
#[inline(always)]
pub(super) fn exprs(s: &[u8], e: u64, out: &mut impl Records) -> (usize, u64) {
    let k = std::hint::black_box(&CONSTS);
    let (mut pos, mut e2) = (0, e);
    while let Some(w) = s.get(pos..pos + WIN) {
        let w: &[u8; WIN] = w.try_into().expect("a window");
        let head = ld(w, 0);
        let end = if head == k.head0 {
            if ld(w, 8) & MASK6 != k.head1 {
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
            if i != e2 || ld(w, q) & MASK2 != k.end || !out.app(i, f, a) {
                break;
            }
            q + 2
        } else if head == k.forall[0] {
            if ld(w, 8) != k.forall[1]
                || ld(w, 16) != k.forall[2]
                || ld(w, 24) & MASK2 != k.forall[3]
            {
                break;
            }
            let Some((bi, body, name, ty, q)) = binder(w, 26, k) else {
                break;
            };
            if ld(w, q) & MASK7 != k.ie {
                break;
            }
            let Some((i, q)) = nat(w, q + 7, k) else {
                break;
            };
            if i != e2 || ld(w, q) & MASK2 != k.end || !out.binder(i, true, bi, name, ty, body) {
                break;
            }
            q + 2
        } else if head & MASK6 == k.ie_head {
            // `{"ie":`, an id, then (for a lambda) `,"lam":{"binderInfo":"`.
            let Some((i, q)) = nat(w, 6, k) else { break };
            if ld(w, q) != k.lam[0] || ld(w, q + 8) != k.lam[1] || ld(w, q + 16) & MASK6 != k.lam[2]
            {
                break;
            }
            let Some((bi, body, name, ty, q)) = binder(w, q + 22, k) else {
                break;
            };
            if i != e2 || ld(w, q) & MASK3 != k.lam_end || !out.binder(i, false, bi, name, ty, body)
            {
                break;
            }
            q + 3
        } else {
            break;
        };
        pos += end;
        e2 += 1;
    }
    (pos, e2 - e)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Default)]
    struct Got(Vec<(u64, String)>, bool);

    impl Records for Got {
        fn app(&mut self, id: u64, f: u64, a: u64) -> bool {
            self.0.push((id, format!("app {f} {a}")));
            !self.1
        }

        fn binder(
            &mut self,
            id: u64,
            pi: bool,
            bi: BinderInfo,
            name: u64,
            ty: u64,
            body: u64,
        ) -> bool {
            self.0.push((id, format!("{pi} {bi:?} {name} {ty} {body}")));
            !self.1
        }
    }

    fn run(text: &str, e: u64) -> (Vec<(u64, String)>, usize, u64) {
        let pad = " ".repeat(WIN);
        let text = format!("{text}{pad}");
        let mut got = Got::default();
        let (n, k) = exprs(text.as_bytes(), e, &mut got);
        (got.0, n, k)
    }

    #[test]
    fn runs_of_records() {
        let text = "{\"app\":{\"arg\":3,\"fn\":7},\"ie\":8}\n\
             {\"app\":{\"arg\":123456789,\"fn\":0},\"ie\":9}\n\
             {\"forallE\":{\"binderInfo\":\"default\",\"body\":0,\"name\":2,\"type\":1},\"ie\":10}\n\
             {\"ie\":11,\"lam\":{\"binderInfo\":\"implicit\",\"body\":123456789,\"name\":20,\"type\":4}}\n\
             {\"ie\":12,\"lam\":{\"binderInfo\":\"instImplicit\",\"body\":5,\"name\":6,\"type\":7}}\n\
             {\"forallE\":{\"binderInfo\":\"strictImplicit\",\"body\":123456789,\"name\":123456789,\"type\":123456789},\"ie\":123456789}\n";
        let (got, n, k) = run(text, 8);
        let want = [
            (8, "app 7 3"),
            (9, "app 0 123456789"),
            (10, "true Default 2 1 0"),
            (11, "false Implicit 20 4 123456789"),
            (12, "false InstImplicit 6 7 5"),
        ];
        let want: Vec<(u64, String)> = want.iter().map(|&(i, s)| (i, s.to_string())).collect();
        assert_eq!(got, want);
        assert_eq!(k, 5);
        assert!(text[n..].starts_with("{\"forallE\":{\"binderInfo\":\"strict"));
        let (got, _, k) = run(&text[n..], 123456789);
        assert_eq!((got.len(), k), (1, 1));
        assert_eq!(
            got[0].1,
            "true StrictImplicit 123456789 123456789 123456789"
        );
        // A wrong id, a number of ten digits, a leading zero, other text.
        for (line, e) in [
            ("{\"app\":{\"arg\":3,\"fn\":7},\"ie\":9}\n", 8),
            ("{\"app\":{\"arg\":3,\"fn\":7},\"ie\":8 }\n", 8),
            ("{\"app\":{\"arg\":1234567890,\"fn\":7},\"ie\":8}\n", 8),
            ("{\"app\":{\"arg\":01,\"fn\":7},\"ie\":8}\n", 8),
            ("{\"app\":{\"arg\":3,\"fn\":7},\"ie\":80}\n", 8),
            (
                "{\"ie\":8,\"lam\":{\"binderInfo\":\"implicitx\",\"body\":5,\"name\":6,\"type\":7}}\n",
                8,
            ),
            (
                "{\"ie\":8,\"lam\":{\"binderInfo\":\"default\",\"body\":5,\"name\":6,\"type\":7}}}\n",
                8,
            ),
            (
                "{\"ie\":8,\"lam\":{\"binderInfo\":\"default\",\"body\":5,\"name\":6,\"type\":7}} \n",
                8,
            ),
            (
                "{\"ie\":8,\"letE\":{\"body\":5,\"name\":6,\"nondep\":false,\"type\":7,\"value\":1}}\n",
                8,
            ),
            (
                "{\"forallE\":{\"binderInfo\":\"default\",\"body\":0,\"name\":2,\"type\":1},\"ie\":10}\n",
                9,
            ),
            (
                "{\"forallE\":{\"binderInfo\":\"default\",\"body\":0,\"name\":2,\"type\":1,\"x\":1},\"ie\":9}\n",
                9,
            ),
        ] {
            let (got, n, k) = run(line, e);
            assert_eq!((n, k), (0, 0), "{line} gave {got:?}");
        }
        // A refusal.
        let mut got = Got(Vec::new(), true);
        let line = format!(
            "{{\"app\":{{\"arg\":3,\"fn\":7}},\"ie\":8}}\n{}",
            " ".repeat(WIN)
        );
        assert_eq!(exprs(line.as_bytes(), 8, &mut got), (0, 0));
    }
}
