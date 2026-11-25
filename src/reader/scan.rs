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

use super::{Comp, Item, RawExpr, RawLevel};
use crate::expr::BinderInfo;

/// A cursor over the rest of the input, starting at a line.
struct C<'a> {
    s: &'a [u8],
    p: usize,
}

impl C<'_> {
    /// Expect the bytes `w`.
    #[inline(always)]
    fn lit(&mut self, w: &[u8]) -> Option<()> {
        if self.s.get(self.p..self.p + w.len())? == w {
            self.p += w.len();
            Some(())
        } else {
            None
        }
    }

    /// Whether the bytes `w` come next (and if so, skip them).
    #[inline(always)]
    fn opt(&mut self, w: &[u8]) -> bool {
        self.lit(w).is_some()
    }

    /// A natural number in canonical JSON syntax, of at most 19 digits
    /// (so that it fits a `u64`).
    #[inline(always)]
    fn nat(&mut self) -> Option<u64> {
        let start = self.p;
        let mut v;
        if let Some(b) = self.s.get(start..start + 8) {
            let w = u64::from_le_bytes(b.try_into().expect("8 bytes"));
            let x = w.wrapping_sub(0x3030_3030_3030_3030);
            // The high bit of each byte that is not a digit. A byte below
            // a non-digit is a digit, so no borrow or carry reaches the
            // first non-digit from below.
            let t = (x | x.wrapping_add(0x7676_7676_7676_7676)) & 0x8080_8080_8080_8080;
            let n = (t.trailing_zeros() / 8) as usize;
            if n == 0 {
                return None;
            }
            // The digits, most significant first, as eight digits with
            // leading zeros.
            let mut d = if n == 8 { x } else { x << (64 - 8 * n) };
            d = (d & 0x0F0F_0F0F_0F0F_0F0F).wrapping_mul(2561) >> 8;
            d = (d & 0x00FF_00FF_00FF_00FF).wrapping_mul(6_553_601) >> 16;
            d = (d & 0x0000_FFFF_0000_FFFF).wrapping_mul(42_949_672_960_001) >> 32;
            v = d;
            self.p += n;
            if n < 8 {
                return (n == 1 || b[0] != b'0').then_some(v);
            }
            if b[0] == b'0' {
                return None;
            }
        } else {
            v = 0;
        }
        while let Some(&c) = self.s.get(self.p) {
            if !c.is_ascii_digit() {
                break;
            }
            if self.p - start == 19 {
                return None;
            }
            v = v * 10 + (c - b'0') as u64;
            self.p += 1;
        }
        let len = self.p - start;
        if len == 0 || (len > 1 && self.s[start] == b'0') {
            return None;
        }
        Some(v)
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
    /// binder's opening brace.
    fn binder(&mut self, pi: bool) -> Option<RawExpr> {
        self.lit(b"\"binderInfo\":\"")?;
        let bi = self.binder_info()?;
        self.lit(b",\"body\":")?;
        let body = self.nat()?;
        self.lit(b",\"name\":")?;
        let name = self.nat()?;
        self.lit(b",\"type\":")?;
        let ty = self.nat()?;
        self.lit(b"}")?;
        Some(RawExpr::Binder {
            pi,
            bi,
            name,
            ty,
            body,
        })
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
}

/// Read the record at the start of `s` (a line, and maybe more input
/// after it). On success, the item and the length of the line, newline
/// included. Text ranges in the item are relative to `s`, and the levels
/// of a `const` are pushed on `us` (its range is into `us`).
#[inline]
pub(super) fn line(s: &[u8], us: &mut Vec<u64>) -> Option<(Item, usize)> {
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
            Item::Expr {
                id,
                node: RawExpr::App(f, a),
            }
        }
        b'f' => {
            c.lit(b"forallE\":{")?;
            let node = c.binder(true)?;
            c.lit(b",\"ie\":")?;
            let id = c.nat()?;
            c.lit(b"}")?;
            Item::Expr { id, node }
        }
        b'c' => {
            c.lit(b"const\":{\"name\":")?;
            let name = c.nat()?;
            c.lit(b",\"us\":[")?;
            let start = us.len();
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
                        let n = c.binder(false)?;
                        c.lit(b"}")?;
                        n
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
                        c.lit(if k == b'm' { b"max\":[" } else { b"imax\":[" })?;
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
    Some((item, c.p))
}
