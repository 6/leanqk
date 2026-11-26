//! Runs of application and binder lines, the commonest records by far
//! (nine lines in ten of a real export), read in one loop.
//!
//! An application line is `{"app":{"arg":A,"fn":F},"ie":I}` and a
//! newline; a binder line is `{"forallE":{"binderInfo":"default",`
//! `"body":B,"name":N,"type":T},"ie":I}` or `{"ie":I,"lam":{...}}`. In an
//! export with dense ids, `I` is the next expression id. A constant line
//! goes to [`Records::leaf`] (which hands it to the scanner) and the run
//! goes on; a line of another shape, or that the loop cannot take for any
//! other reason, ends the run, and the scanner reads it.

use crate::expr::BinderInfo;

/// The bytes the loop looks at from a line's start: the longest line it
/// takes (a binder with five numbers of 9 digits) is 110 bytes, and it
/// reads no further than 8 bytes past a position below [`AT`].
const WIN: usize = AT + 8;

/// Positions in a window are taken modulo this (a mask rather than a
/// bounds check; every position the loop reaches is below it anyway).
const AT: usize = 128;

/// The eight bytes of `w` from `p` (modulo [`AT`]).
#[inline(always)]
fn ld(w: &[u8; WIN], p: usize) -> u64 {
    let p = p % AT;
    u64::from_le_bytes(w[p..p + 8].try_into().expect("8 bytes"))
}

/// The byte of `w` at `p` (modulo [`AT`]).
#[inline(always)]
fn byte(w: &[u8; WIN], p: usize) -> u8 {
    w[p % AT]
}

/// Lines [`exprs`] reads at most at a time.
pub(super) const BATCH: u64 = 512;

/// Where the records go: at most [`BATCH`] between flushes.
pub(super) trait Records {
    /// Application `id`; false to refuse it (and end the run).
    fn app(&mut self, id: u64, f: u64, a: u64) -> bool;

    /// Binder `id`; as [`Records::app`].
    fn binder(&mut self, id: u64, pi: bool, bi: BinderInfo, name: u64, ty: u64, body: u64) -> bool;

    /// The constant line at the start of `s`, expression `id`: how many
    /// bytes it took (its newline too), or `None` to end the run there.
    fn leaf(&mut self, id: u64, s: &[u8]) -> Option<usize> {
        let _ = (id, s);
        None
    }

    /// After each [`exprs`] (which makes no calls, so that the loop keeps
    /// its state in registers), with the ids it took.
    fn flush(&mut self, ids: std::ops::Range<u64>);
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
    konst: u64,
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
    konst: word(b"{\"const\"", 0),
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
    if n8 == 0 || (n8 > 8 && x as u8 == 0) {
        return None;
    }
    let d = x << (64 - n8);
    let d = d.wrapping_mul(k.ten).wrapping_add(d >> 8) & 0x00FF_00FF_00FF_00FF;
    let d = d.wrapping_mul(k.hundred).wrapping_add(d >> 16) & 0x0000_FFFF_0000_FFFF;
    let d = d.wrapping_mul(k.join) >> 32;
    if n8 == 64 {
        let c = byte(w, p + 8).wrapping_sub(b'0');
        if c <= 9 {
            if byte(w, p + 9).is_ascii_digit() {
                return None;
            }
            return Some((d * 10 + c as u64, p + 9));
        }
    }
    Some((d, p + (n8 / 8) as usize))
}

/// The number at `p` (of at most 8 digits) and where it ends.
#[inline(always)]
fn nat8(w: &[u8; WIN], p: usize, k: &Consts) -> Option<(u64, usize)> {
    let v = ld(w, p);
    let x = v ^ 0x3030_3030_3030_3030;
    let t = (x | x.wrapping_add(k.below_ten)) & 0x8080_8080_8080_8080;
    let n8 = t.trailing_zeros() & !7;
    if n8 == 0 || (n8 > 8 && x as u8 == 0) {
        return None;
    }
    let d = x << (64 - n8);
    let d = d.wrapping_mul(k.ten).wrapping_add(d >> 8) & 0x00FF_00FF_00FF_00FF;
    let d = d.wrapping_mul(k.hundred).wrapping_add(d >> 16) & 0x0000_FFFF_0000_FFFF;
    let d = d.wrapping_mul(k.join) >> 32;
    Some((d, p + (n8 / 8) as usize))
}

/// The number at `p` (of at most 9 digits), which the text `word`
/// (under `mask`, starting with a non-digit) follows: the number and
/// where the text starts. A ninth digit is only looked for if the text
/// is not after the eighth, so most numbers cost no more than 8 digits.
#[inline(always)]
fn nat_to(w: &[u8; WIN], p: usize, k: &Consts, word: u64, mask: u64) -> Option<(u64, usize)> {
    let (d, q) = nat8(w, p, k)?;
    if ld(w, q) & mask == word {
        return Some((d, q));
    }
    let c = byte(w, q).wrapping_sub(b'0');
    if q != p + 8 || c > 9 || ld(w, q + 1) & mask != word {
        return None;
    }
    Some((d * 10 + c as u64, q + 1))
}

/// The number of digits of `e`, and the first number with more.
pub(super) fn digits(e: u64) -> (u32, u64) {
    let (mut len, mut next) = (1, 10);
    while e >= next {
        len += 1;
        next *= 10;
    }
    (len, next)
}

/// The ids [`exprs`] expects: their length, the first id with more
/// digits, and an id `e` with (if it has at most 8 digits) its text, as
/// the bytes of a word (the first digit in the low byte).
#[derive(Clone, Copy, Debug)]
pub(super) struct Ids {
    len: u32,
    next: u64,
    e: u64,
    txt: u64,
}

impl Default for Ids {
    fn default() -> Self {
        Ids::at(0)
    }
}

impl Ids {
    fn at(e: u64) -> Ids {
        let (len, next) = digits(e);
        Ids {
            len,
            next,
            e,
            txt: text(e, len),
        }
    }

    /// Move to `e`: by counting up from a little before it.
    #[inline(always)]
    fn seek(&mut self, e: u64) {
        if e >= self.next || e < self.e || e - self.e > 16 {
            *self = Ids::at(e);
        }
        while self.e < e {
            self.txt = next_text(self.txt, self.len);
            self.e += 1;
        }
    }
}

/// The text of `e` (of `len` digits) in the top bytes of a word (the
/// last digit in the top byte; as a word read from the text and shifted
/// up), or 0 if it has more than 8.
fn text(e: u64, len: u32) -> u64 {
    if len > 8 {
        return 0;
    }
    let (mut t, mut x) = (0, e);
    for i in (0..len).rev() {
        t |= (b'0' as u64 + x % 10) << (8 * i);
        x /= 10;
    }
    t << (64 - 8 * len)
}

/// The text after `t` (of `len` digits, up to 8; the next number is to
/// have as many).
#[inline(always)]
fn next_text(t: u64, len: u32) -> u64 {
    if len > 8 {
        return t;
    }
    carry(t + (1 << 56), len)
}

/// `t` with its last digit just incremented: a digit past `9` (which
/// reads `:`) becomes `0` and increments the one before it.
#[inline(always)]
fn carry(mut t: u64, len: u32) -> u64 {
    let mut at = 56;
    while (t >> at) as u8 == b':' && at > 64 - 8 * len.min(8) {
        t -= 10 << at;
        at -= 8;
        t += 1 << at;
    }
    t
}

/// Whether the id at `p` is `e` (of `len` digits): where it ends. Its
/// length is known, so this reads exactly that many digits (and the
/// value then also rules out a leading zero).
#[inline(always)]
fn id_at(w: &[u8; WIN], p: usize, e: u64, len: u32, k: &Consts) -> Option<usize> {
    if len > 8 {
        return match nat(w, p, k) {
            Some((i, q)) if i == e => Some(q),
            _ => None,
        };
    }
    // The digits, most significant first, in the top bytes.
    let x = (ld(w, p) ^ 0x3030_3030_3030_3030) << (64 - 8 * len);
    if (x | x.wrapping_add(k.below_ten)) & 0x8080_8080_8080_8080 != 0 {
        return None;
    }
    let d = x.wrapping_mul(k.ten).wrapping_add(x >> 8) & 0x00FF_00FF_00FF_00FF;
    let d = d.wrapping_mul(k.hundred).wrapping_add(d >> 16) & 0x0000_FFFF_0000_FFFF;
    let d = d.wrapping_mul(k.join) >> 32;
    (d == e).then_some(p + len as usize)
}

/// A binder's fields from `p` (its binder info's text), which the text
/// `word` (under `mask`) follows: binder info, body, name, type, and
/// where they end.
#[inline(always)]
fn binder(
    w: &[u8; WIN],
    p: usize,
    k: &Consts,
    (word, mask): (u64, u64),
) -> Option<(BinderInfo, u64, u64, u64, usize)> {
    let x = ld(w, p);
    // The binder info and its closing quote.
    let (bi, q) = if x == k.default {
        (BinderInfo::Default, p + 8)
    } else if x == k.implicit && byte(w, p + 8) == b'"' {
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
    let (body, q) = nat_to(w, q + 8, k, k.name, u64::MAX)?;
    let (name, q) = nat_to(w, q + 8, k, k.ty, u64::MAX)?;
    let (ty, q) = nat_to(w, q + 8, k, word, mask)?;
    Some((bi, body, name, ty, q))
}

/// Whether the id at `p` is `e` (of `len` digits): where it ends. Its
/// text is `txt` if it has at most 8 digits (`shift` being
/// `64 - 8 * len`); if 9, `txt` is that of the first 8 (as a word read
/// from the text) and `last` the last digit.
#[inline(always)]
fn id_is(
    w: &[u8; WIN],
    p: usize,
    (e, len, txt, shift, last): (u64, u32, u64, u32, u8),
    k: &Consts,
) -> Option<usize> {
    if len <= 8 {
        (ld(w, p) << shift == txt).then_some(p + len as usize)
    } else if len == 9 {
        (ld(w, p) == txt && byte(w, p + 8) == last).then_some(p + 9)
    } else {
        id_at(w, p, e, len, k)
    }
}

/// The application and binder lines at the start of `s` while their ids
/// are `e`, `e + 1`, ... (below `limit`, all of `len` digits): each goes
/// to `out`, until it refuses one. How many bytes and lines it took.
/// `SHORT` if the ids have at most 8 digits (`len`), which are then
/// compared as text.
#[inline(always)]
fn exprs<const SHORT: bool>(
    s: &[u8],
    e: u64,
    (len, limit): (u32, u64),
    mut txt: u64,
    out: &mut impl Records,
) -> (usize, u64, u64) {
    let k = std::hint::black_box(&CONSTS);
    let (mut pos, mut e2) = (0, e);
    // Ids of up to 8 digits are compared as text; `txt` is `e2`'s.
    // (So that the compiler knows which way `id_is` goes.)
    let len = if SHORT { len.min(8) } else { len.max(9) };
    let shift = 64 - 8 * len.min(8);
    // The last line start with a whole window.
    let Some(stop) = s.len().checked_sub(WIN) else {
        return (0, 0, txt);
    };
    // Ids of 9 digits are compared as text too (see `id_is`); this loop
    // keeps their text, not `Ids`.
    let mut last = 0u8;
    let short_txt = txt;
    if !SHORT && len == 9 {
        txt = text(e / 10, 8);
        last = b'0' + (e % 10) as u8;
    }

    while e2 < limit && pos <= stop {
        let Some(w) = s[pos..].first_chunk::<WIN>() else {
            break;
        };
        let head = ld(w, 0);
        let end = if head == k.head0 {
            if ld(w, 8) & MASK6 != k.head1 {
                break;
            }
            let Some((a, q)) = nat_to(w, 14, k, k.fn_, MASK6) else {
                break;
            };
            let Some((f, q)) = nat_to(w, q + 6, k, k.ie, MASK7) else {
                break;
            };
            let Some(q) = id_is(w, q + 7, (e2, len, txt, shift, last), k) else {
                break;
            };
            if ld(w, q) & MASK2 != k.end || !out.app(e2, f, a) {
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
            let Some((bi, body, name, ty, q)) = binder(w, 26, k, (k.ie, MASK7)) else {
                break;
            };
            let Some(q) = id_is(w, q + 7, (e2, len, txt, shift, last), k) else {
                break;
            };
            if ld(w, q) & MASK2 != k.end || !out.binder(e2, true, bi, name, ty, body) {
                break;
            }
            q + 2
        } else if head & MASK6 == k.ie_head {
            // `{"ie":`, an id, then (for a lambda) `,"lam":{"binderInfo":"`.
            let Some(q) = id_is(w, 6, (e2, len, txt, shift, last), k) else {
                break;
            };
            if ld(w, q) != k.lam[0] || ld(w, q + 8) != k.lam[1] || ld(w, q + 16) & MASK6 != k.lam[2]
            {
                break;
            }
            let Some((bi, body, name, ty, q)) = binder(w, q + 22, k, (k.lam_end, MASK3)) else {
                break;
            };
            if !out.binder(e2, false, bi, name, ty, body) {
                break;
            }
            q + 3
        } else if head == k.konst
            && let Some(n) = out.leaf(e2, &s[pos..])
            && n > 0
        {
            n
        } else {
            break;
        };
        pos += end;
        e2 += 1;
        if SHORT {
            txt = txt.wrapping_add(1 << 56);
            if (txt >> 56) as u8 == b':' {
                txt = carry(txt, len);
            }
        } else if len == 9 {
            last += 1;
            if last == b':' {
                last = b'0';
                txt = next_text(txt, 8);
            }
        }
    }
    (pos, e2 - e, if SHORT { txt } else { short_txt })
}

/// [`exprs`] for ids of more than 8 digits (the last few lines of the
/// largest exports), kept out of the loop of the others.
#[inline(never)]
fn long_exprs(
    s: &[u8],
    e: u64,
    ids: (u32, u64),
    txt: u64,
    out: &mut impl Records,
) -> (usize, u64, u64) {
    exprs::<false>(s, e, ids, txt, out)
}

/// [`exprs`] for any ids, a batch at a time: from `e`, across their
/// lengths. `ids` is where the last call left off (updated).
#[inline(always)]
pub(super) fn all_exprs(s: &[u8], e: u64, ids: &mut Ids, out: &mut impl Records) -> (usize, u64) {
    let (mut pos, mut e2) = (0, e);
    loop {
        ids.seek(e2);
        let limit = ids.next.min(e2 + BATCH);
        let (n, m, txt) = if ids.len <= 8 {
            exprs::<true>(&s[pos..], e2, (ids.len, limit), ids.txt, out)
        } else {
            long_exprs(&s[pos..], e2, (ids.len, limit), ids.txt, out)
        };
        out.flush(e2..e2 + m);
        pos += n;
        e2 += m;
        (ids.e, ids.txt) = (e2, txt);
        // Stopped before the limit.
        if e2 != limit {
            return (pos, e2 - e);
        }
    }
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

        fn flush(&mut self, _: std::ops::Range<u64>) {}
    }

    fn run(text: &str, e: u64) -> (Vec<(u64, String)>, usize, u64) {
        let pad = " ".repeat(WIN);
        let text = format!("{text}{pad}");
        let mut got = Got::default();
        let (n, k) = all_exprs(text.as_bytes(), e, &mut Ids::default(), &mut got);
        (got.0, n, k)
    }

    #[test]
    fn ids_by_length() {
        let pad = " ".repeat(WIN);
        for e in [
            0u64,
            7,
            9,
            10,
            99,
            100,
            12345678,
            99_999_999,
            100_000_000,
            123_456_789,
        ] {
            let (len, next) = digits(e);
            assert_eq!(len as usize, e.to_string().len());
            assert_eq!(next, 10u64.pow(len));
            for (text, ok) in [
                (format!("{e}}}"), true),
                (format!("0{e}}}"), false),
                (format!("{}}}", e + 1), false),
                (format!("{e}0}}"), false),
                (format!(":{e}}}"), false),
            ] {
                let t = format!("{text}{pad}");
                let w: &[u8; WIN] = t.as_bytes()[..WIN].try_into().unwrap();
                // As the caller does: the id, then `}`.
                let got = id_at(w, 0, e, len, &CONSTS).filter(|&q| w[q] == b'}');
                assert_eq!(got.is_some(), ok, "{text}");
            }
        }
    }

    #[test]
    fn texts_of_ids() {
        let mut ids = Ids::default();
        for e in (0..200_000).chain(99_999_990..100_000_010) {
            ids.seek(e);
            let (len, _) = digits(e);
            assert_eq!(ids.txt, text(e, len), "{e}");
            if len <= 8 {
                let t = ids.txt.to_le_bytes();
                assert_eq!(&t[8 - len as usize..], e.to_string().as_bytes());
            }
        }
    }

    #[test]
    fn runs_of_records() {
        let text = "{\"app\":{\"arg\":3,\"fn\":7},\"ie\":8}\n\
             {\"app\":{\"arg\":123456789,\"fn\":12345678},\"ie\":9}\n\
             {\"forallE\":{\"binderInfo\":\"default\",\"body\":0,\"name\":2,\"type\":1},\"ie\":10}\n\
             {\"ie\":11,\"lam\":{\"binderInfo\":\"implicit\",\"body\":123456789,\"name\":20,\"type\":4}}\n\
             {\"ie\":12,\"lam\":{\"binderInfo\":\"instImplicit\",\"body\":5,\"name\":6,\"type\":7}}\n\
             {\"forallE\":{\"binderInfo\":\"strictImplicit\",\"body\":123456789,\"name\":123456789,\"type\":123456789},\"ie\":123456789}\n";
        let (got, n, k) = run(text, 8);
        let want = [
            (8, "app 7 3"),
            (9, "app 12345678 123456789"),
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
            ("{\"app\":{\"arg\":012345678,\"fn\":7},\"ie\":8}\n", 8),
            ("{\"app\":{\"arg\":12345678,\"fn\":7}, \"ie\":8}\n", 8),
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
        assert_eq!(
            all_exprs(line.as_bytes(), 8, &mut Ids::default(), &mut got),
            (0, 0)
        );
    }
}
