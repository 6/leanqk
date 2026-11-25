//! The fastest path: name, level and expression records exactly as
//! lean4export writes them.
//!
//! The exporter writes each record on one line, with no spaces and with
//! keys sorted, so a record of a given kind is fixed text with numbers
//! (and at most one string) in between, such as
//! `{"app":{"arg":5,"fn":6},"ie":7}`. This scanner matches that text
//! directly and reads numbers eight digits at a time. Anything else
//! (other spacing or key order, escapes, `mdata`, declarations) makes it
//! return `None`, and the caller falls back to the [`super::fast`]
//! scanner and then to the general JSON parser. As there, the contract
//! (checked by differential tests) is that when this returns an item, the
//! general path yields the same one.

use super::{Comp, Item, R, RawExpr, RawLevel};
use crate::env::{Hints, Safety};
use crate::expr::BinderInfo;

/// A theorem or definition record. The lists are ranges of the scratch
/// space given to [`line`]; `hints` and `safety` are those of a
/// definition (unused for a theorem).
pub(super) struct Decl {
    pub thm: bool,
    pub all: (usize, usize),
    pub level_params: (usize, usize),
    pub name: u64,
    pub ty: u64,
    pub value: u64,
    pub hints: Hints,
    pub safety: Safety,
}

/// What a scanned record goes to. The commonest kinds have their own
/// methods, so that the reader can apply them without building an
/// [`Item`] first.
pub(super) trait Sink {
    fn app(&mut self, id: u64, f: u64, a: u64) -> R<()>;

    fn binder(&mut self, id: u64, pi: bool, bi: BinderInfo, name: u64, ty: u64, body: u64)
    -> R<()>;

    /// Any other record; its text ranges are into `line`, and the levels
    /// of a `const` into `us`.
    fn item(&mut self, item: Item, line: &[u8], us: &[u64]) -> R<()>;

    /// A theorem or definition, with its lists in `us`; `None` to leave
    /// the line to the general parser.
    fn decl(&mut self, _d: &Decl, _us: &[u64]) -> Option<R<()>> {
        None
    }
}

/// A cursor over the rest of the input, starting at a line.
struct C<'a> {
    s: &'a [u8],
    p: usize,
}

impl C<'_> {
    /// Expect the bytes `w`.
    #[inline(always)]
    fn lit<const N: usize>(&mut self, w: &[u8; N]) -> Option<()> {
        let ok = if N <= 16 && self.p + 16 <= self.s.len() {
            // Compare words: the literal, padded with zeros, against the
            // input with the bytes past the literal masked off.
            let mut pad = [0u8; 16];
            pad[..N].copy_from_slice(w);
            let lo = u64::from_le_bytes(pad[..8].try_into().expect("8"));
            let hi = u64::from_le_bytes(pad[8..].try_into().expect("8"));
            let at = &self.s[self.p..self.p + 16];
            let x = u64::from_le_bytes(at[..8].try_into().expect("8"));
            let mask = |n: usize| {
                if n >= 8 {
                    u64::MAX
                } else {
                    (1u64 << (8 * n)) - 1
                }
            };
            if N <= 8 {
                x & mask(N) == lo
            } else {
                let y = u64::from_le_bytes(at[8..].try_into().expect("8"));
                x == lo && y & mask(N - 8) == hi
            }
        } else {
            self.s.get(self.p..self.p + N)? == w
        };
        if ok {
            self.p += N;
            Some(())
        } else {
            None
        }
    }

    /// Whether the bytes `w` come next (and if so, skip them).
    #[inline(always)]
    fn opt<const N: usize>(&mut self, w: &[u8; N]) -> bool {
        self.lit(w).is_some()
    }

    /// A natural number in canonical JSON syntax, of at most 19 digits
    /// (so that it fits a `u64`).
    #[inline(always)]
    fn nat(&mut self) -> Option<u64> {
        let start = self.p;
        let Some(b) = self.s.get(start..start + 8) else {
            let (v, p) = nat_slow(self.s, start)?;
            self.p = p;
            return Some(v);
        };
        let w = u64::from_le_bytes(b.try_into().expect("8 bytes"));
        let x = w.wrapping_sub(0x3030_3030_3030_3030);
        // The high bit of each byte that is not a digit. A byte below a
        // non-digit is a digit, so no borrow or carry reaches the first
        // non-digit from below.
        let t = (x | x.wrapping_add(0x7676_7676_7676_7676)) & 0x8080_8080_8080_8080;
        // Eight times the number of leading digits (`t` has bits only at
        // 7, 15, ..., so this is 8n for n < 8, and 64 when t is 0).
        let n8 = t.trailing_zeros() & !7;
        // No digits, or a leading zero.
        if n8 == 0 || (n8 > 8 && w as u8 == b'0') {
            return None;
        }
        // The digits, most significant first, as eight digits with
        // leading zeros.
        let mut d = x << (64 - n8);
        d = (d & 0x0F0F_0F0F_0F0F_0F0F).wrapping_mul(2561) >> 8;
        d = (d & 0x00FF_00FF_00FF_00FF).wrapping_mul(6_553_601) >> 16;
        d = (d & 0x0000_FFFF_0000_FFFF).wrapping_mul(42_949_672_960_001) >> 32;
        self.p += (n8 / 8) as usize;
        if n8 == 64 {
            // A ninth digit (ids of a big export), or more.
            match self.s.get(self.p) {
                Some(&c) if c.is_ascii_digit() => {
                    if self.s.get(self.p + 1).is_some_and(u8::is_ascii_digit) {
                        let (v, p) = nat_slow(self.s, start)?;
                        self.p = p;
                        return Some(v);
                    }
                    self.p += 1;
                    return Some(d * 10 + (c - b'0') as u64);
                }
                _ => {}
            }
        }
        Some(d)
    }

    /// The contents of a string without escapes or control characters
    /// (the opening quote is already read), as a range of the line.
    #[inline(always)]
    fn string(&mut self) -> Option<(u32, u32)> {
        let start = self.p;
        loop {
            match *self.s.get(self.p)? {
                b'"' => break,
                b'\\' => return None,
                c if c < 0x20 => return None,
                _ => self.p += 1,
            }
        }
        let end = self.p;
        self.p += 1;
        let text = &self.s[start..end];
        if !text.is_ascii() {
            std::str::from_utf8(text).ok()?;
        }
        Some((u32::try_from(start).ok()?, u32::try_from(end).ok()?))
    }

    #[inline(always)]
    fn binder_info(&mut self) -> Option<BinderInfo> {
        Some(match self.s.get(self.p)? {
            b'd' if self.opt(b"default\"") => BinderInfo::Default,
            b'i' if self.opt(b"implicit\"") => BinderInfo::Implicit,
            b'i' if self.opt(b"instImplicit\"") => BinderInfo::InstImplicit,
            b's' if self.opt(b"strictImplicit\"") => BinderInfo::StrictImplicit,
            _ => return None,
        })
    }

    /// `"binderInfo":"…","body":B,"name":N,"type":T}`, after the
    /// binder's opening brace: binder info, name, type and body.
    #[inline(always)]
    fn binder(&mut self) -> Option<(BinderInfo, u64, u64, u64)> {
        self.lit(b"\"binderInfo\":\"")?;
        let bi = self.binder_info()?;
        self.lit(b",\"body\":")?;
        let body = self.nat()?;
        self.lit(b",\"name\":")?;
        let name = self.nat()?;
        self.lit(b",\"type\":")?;
        let ty = self.nat()?;
        self.lit(b"}")?;
        Some((bi, name, ty, body))
    }

    /// The end of a line: a newline, or the end of the input.
    #[inline(always)]
    fn eol(&mut self) -> Option<()> {
        match self.s.get(self.p) {
            None => Some(()),
            Some(b'\n') => {
                self.p += 1;
                Some(())
            }
            _ => None,
        }
    }

    /// A list of numbers (the opening bracket is already read), pushed to
    /// `us`: the range they take there.
    fn nats(&mut self, us: &mut Vec<u64>) -> Option<(usize, usize)> {
        let start = us.len();
        if !self.opt(b"]") {
            loop {
                us.push(self.nat()?);
                if self.opt(b"]") {
                    break;
                }
                self.lit(b",")?;
            }
        }
        Some((start, us.len()))
    }

    /// The fields of a theorem or definition after `{"thm":` or
    /// `{"def":`, and the end of the line.
    fn decl(&mut self, thm: bool, us: &mut Vec<u64>) -> Option<Decl> {
        us.clear();
        self.lit(b"{\"all\":[")?;
        let all = self.nats(us)?;
        let mut hints = Hints::Opaque;
        if !thm {
            self.lit(b",\"hints\":")?;
            hints = if self.opt(b"\"abbrev\"") {
                Hints::Abbrev
            } else if self.opt(b"\"opaque\"") {
                Hints::Opaque
            } else {
                self.lit(b"{\"regular\":")?;
                let h = u32::try_from(self.nat()?).ok()?;
                self.lit(b"}")?;
                Hints::Regular(h)
            };
        }
        self.lit(b",\"levelParams\":[")?;
        let level_params = self.nats(us)?;
        self.lit(b",\"name\":")?;
        let name = self.nat()?;
        let mut safety = Safety::Safe;
        if !thm {
            self.lit(b",\"safety\":\"")?;
            safety = if self.opt(b"safe\"") {
                Safety::Safe
            } else if self.opt(b"unsafe\"") {
                Safety::Unsafe
            } else {
                self.lit(b"partial\"")?;
                Safety::Partial
            };
        }
        self.lit(b",\"type\":")?;
        let ty = self.nat()?;
        self.lit(b",\"value\":")?;
        let value = self.nat()?;
        self.lit(b"}}")?;
        self.eol()?;
        Some(Decl {
            thm,
            all,
            level_params,
            name,
            ty,
            value,
            hints,
            safety,
        })
    }
}

/// [`C::nat`] a digit at a time, from `p`: the value and the position
/// after it.
#[cold]
#[inline(never)]
fn nat_slow(s: &[u8], start: usize) -> Option<(u64, usize)> {
    let mut p = start;
    let mut v: u64 = 0;
    while let Some(&c) = s.get(p) {
        if !c.is_ascii_digit() {
            break;
        }
        if p - start == 19 {
            return None;
        }
        v = v * 10 + (c - b'0') as u64;
        p += 1;
    }
    let len = p - start;
    if len == 0 || (len > 1 && s[start] == b'0') {
        return None;
    }
    Some((v, p))
}

/// Read the record at the start of `s` (a line, and maybe more input
/// after it), and give it to `sink`. On success, the length of the line,
/// newline included, and what the sink returned. `us` is scratch space.
#[inline(always)]
pub(super) fn line<S: Sink>(s: &[u8], us: &mut Vec<u64>, sink: &mut S) -> Option<(usize, R<()>)> {
    let mut c = C { s, p: 0 };
    c.lit(b"{\"")?;
    let item = match *s.get(2)? {
        b'a' => {
            c.lit(b"app\":{\"arg\":")?;
            let a = c.nat()?;
            c.lit(b",\"fn\":")?;
            let f = c.nat()?;
            c.lit(b"},\"ie\":")?;
            let id = c.nat()?;
            c.lit(b"}")?;
            c.eol()?;
            return Some((c.p, sink.app(id, f, a)));
        }
        b'f' => {
            c.lit(b"forallE\":{")?;
            let (bi, name, ty, body) = c.binder()?;
            c.lit(b",\"ie\":")?;
            let id = c.nat()?;
            c.lit(b"}")?;
            c.eol()?;
            return Some((c.p, sink.binder(id, true, bi, name, ty, body)));
        }
        b'c' => {
            c.lit(b"const\":{\"name\":")?;
            let name = c.nat()?;
            c.lit(b",\"us\":[")?;
            us.clear();
            let start = 0;
            if !c.opt(b"]") {
                loop {
                    us.push(c.nat()?);
                    if c.opt(b"]") {
                        break;
                    }
                    c.lit(b",")?;
                }
            }
            c.lit(b"},\"ie\":")?;
            let id = c.nat()?;
            c.lit(b"}")?;
            let (a, b) = (u32::try_from(start).ok()?, u32::try_from(us.len()).ok()?);
            Item::Expr {
                id,
                node: RawExpr::Const(name, a, b),
            }
        }
        b't' | b'd' => {
            let thm = s[2] == b't';
            if thm {
                c.lit(b"thm\":")?;
            } else {
                c.lit(b"def\":")?;
            }
            let d = c.decl(thm, us)?;
            return sink.decl(&d, us).map(|r| (c.p, r));
        }
        b'b' => {
            c.lit(b"bvar\":")?;
            let i = c.nat()?;
            c.lit(b",\"ie\":")?;
            let id = c.nat()?;
            c.lit(b"}")?;
            Item::Expr {
                id,
                node: RawExpr::BVar(i),
            }
        }
        b'i' => match *s.get(3)? {
            b'e' => {
                c.lit(b"ie\":")?;
                let id = c.nat()?;
                c.lit(b",\"")?;
                let node = match *c.s.get(c.p)? {
                    b'l' if c.opt(b"lam\":{") => {
                        let (bi, name, ty, body) = c.binder()?;
                        c.lit(b"}")?;
                        c.eol()?;
                        return Some((c.p, sink.binder(id, false, bi, name, ty, body)));
                    }
                    b'l' => {
                        c.lit(b"letE\":{\"body\":")?;
                        let body = c.nat()?;
                        c.lit(b",\"name\":")?;
                        let name = c.nat()?;
                        c.lit(b",\"nondep\":")?;
                        let nondep = if c.opt(b"false") {
                            false
                        } else {
                            c.lit(b"true")?;
                            true
                        };
                        c.lit(b",\"type\":")?;
                        let ty = c.nat()?;
                        c.lit(b",\"value\":")?;
                        let value = c.nat()?;
                        c.lit(b"}}")?;
                        RawExpr::Let {
                            name,
                            ty,
                            value,
                            body,
                            nondep,
                        }
                    }
                    b'p' => {
                        c.lit(b"proj\":{\"idx\":")?;
                        let idx = u32::try_from(c.nat()?).ok()?;
                        c.lit(b",\"struct\":")?;
                        let e = c.nat()?;
                        c.lit(b",\"typeName\":")?;
                        let name = c.nat()?;
                        c.lit(b"}}")?;
                        RawExpr::Proj(name, idx, e)
                    }
                    b's' if c.opt(b"sort\":") => {
                        let l = c.nat()?;
                        c.lit(b"}")?;
                        RawExpr::Sort(l)
                    }
                    b's' => {
                        c.lit(b"strVal\":\"")?;
                        let (a, b) = c.string()?;
                        c.lit(b"}")?;
                        RawExpr::Str(a, b)
                    }
                    b'n' => {
                        c.lit(b"natVal\":\"")?;
                        let (a, b) = c.string()?;
                        let digits = &s[a as usize..b as usize];
                        if digits.is_empty() || !digits.iter().all(u8::is_ascii_digit) {
                            return None;
                        }
                        c.lit(b"}")?;
                        RawExpr::Nat(a, b)
                    }
                    _ => return None,
                };
                Item::Expr { id, node }
            }
            b'n' => {
                c.lit(b"in\":")?;
                let id = c.nat()?;
                let (pre, comp) = if c.opt(b",\"str\":{\"pre\":") {
                    let pre = c.nat()?;
                    c.lit(b",\"str\":\"")?;
                    let (a, b) = c.string()?;
                    (pre, Comp::Str(a, b))
                } else {
                    c.lit(b",\"num\":{\"i\":")?;
                    let i = c.nat()?;
                    c.lit(b",\"pre\":")?;
                    (c.nat()?, Comp::Num(i))
                };
                c.lit(b"}}")?;
                Item::Name { id, pre, comp }
            }
            b'l' => {
                c.lit(b"il\":")?;
                let id = c.nat()?;
                c.lit(b",\"")?;
                let node = match *c.s.get(c.p)? {
                    b's' => {
                        c.lit(b"succ\":")?;
                        RawLevel::Succ(c.nat()?)
                    }
                    b'p' => {
                        c.lit(b"param\":")?;
                        RawLevel::Param(c.nat()?)
                    }
                    k @ (b'm' | b'i') => {
                        if k == b'm' {
                            c.lit(b"max\":[")?;
                        } else {
                            c.lit(b"imax\":[")?;
                        }
                        let a = c.nat()?;
                        c.lit(b",")?;
                        let b = c.nat()?;
                        c.lit(b"]")?;
                        if k == b'm' {
                            RawLevel::Max(a, b)
                        } else {
                            RawLevel::IMax(a, b)
                        }
                    }
                    _ => return None,
                };
                c.lit(b"}")?;
                Item::Level { id, node }
            }
            _ => return None,
        },
        _ => return None,
    };
    c.eol()?;
    Some((c.p, sink.item(item, s, us)))
}
