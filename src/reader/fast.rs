//! Single-pass fast path for name, level and expression records.
//!
//! Almost every line of an export is a small record like
//! `{"ie":7,"app":{"arg":5,"fn":6}}`. This scanner reads such a line in one
//! pass, without building a JSON tape, straight into an [`Item`]. It is
//! deliberately conservative: anything it does not expect (escapes, floats,
//! `null`, deeper nesting, `mdata`, a malformed or unusual record) makes it
//! return `None`, and the caller re-parses the line with the general JSON
//! parser, which also produces the error messages. The contract, checked by
//! differential tests, is that when this returns `Some(item)` the general
//! path yields the same item.

use super::{Batch, Comp, Item, RawExpr, RawLevel};
use crate::expr::BinderInfo;

const MAX_INNER: usize = 8;
const MAX_ARR: usize = 32;

#[derive(Clone, Copy, PartialEq, Eq)]
enum V {
    Nat(u64),
    /// Byte range in the line; contains no escapes.
    Str(u32, u32),
    Bool(bool),
    /// Range in the parser's array buffer.
    Arr(u8, u8),
    /// The (single) nested object.
    Obj,
}

type Key = (u32, u32);

struct P<'a> {
    s: &'a [u8],
    pos: usize,
    arr: [u64; MAX_ARR],
    narr: usize,
    inner: [(Key, V); MAX_INNER],
    ninner: usize,
}

impl P<'_> {
    #[inline]
    fn ws(&mut self) {
        while let Some(b' ' | b'\t' | b'\r' | b'\n') = self.s.get(self.pos) {
            self.pos += 1;
        }
    }

    #[inline]
    fn peek(&self) -> Option<u8> {
        self.s.get(self.pos).copied()
    }

    #[inline]
    fn eat(&mut self, c: u8) -> Option<()> {
        if self.peek()? == c {
            self.pos += 1;
            Some(())
        } else {
            None
        }
    }

    /// A string without escapes or control characters.
    #[inline]
    fn string(&mut self) -> Option<(u32, u32)> {
        self.eat(b'"')?;
        let start = self.pos;
        loop {
            match *self.s.get(self.pos)? {
                b'"' => break,
                b'\\' => return None,
                c if c < 0x20 => return None,
                _ => self.pos += 1,
            }
        }
        let end = self.pos;
        self.pos += 1;
        Some((start as u32, end as u32))
    }

    /// A natural number in canonical JSON integer syntax, fitting a u64.
    #[inline]
    fn nat(&mut self) -> Option<u64> {
        let start = self.pos;
        let mut v: u64 = 0;
        while let Some(&c) = self.s.get(self.pos) {
            if !c.is_ascii_digit() {
                break;
            }
            v = v.checked_mul(10)?.checked_add((c - b'0') as u64)?;
            self.pos += 1;
        }
        let len = self.pos - start;
        if len == 0 || (len > 1 && self.s[start] == b'0') {
            return None;
        }
        // Fractions and exponents are for the general parser.
        if let Some(b'.' | b'e' | b'E') = self.peek() {
            return None;
        }
        Some(v)
    }

    fn word(&mut self, w: &[u8]) -> Option<()> {
        if self.s[self.pos..].starts_with(w) {
            self.pos += w.len();
            Some(())
        } else {
            None
        }
    }

    fn scalar(&mut self) -> Option<V> {
        Some(match self.peek()? {
            b'0'..=b'9' => V::Nat(self.nat()?),
            b'"' => {
                let (a, b) = self.string()?;
                V::Str(a, b)
            }
            b't' => {
                self.word(b"true")?;
                V::Bool(true)
            }
            b'f' => {
                self.word(b"false")?;
                V::Bool(false)
            }
            b'[' => {
                self.pos += 1;
                let start = self.narr;
                self.ws();
                if self.peek()? == b']' {
                    self.pos += 1;
                } else {
                    loop {
                        self.ws();
                        if self.narr == MAX_ARR {
                            return None;
                        }
                        self.arr[self.narr] = self.nat()?;
                        self.narr += 1;
                        self.ws();
                        match self.peek()? {
                            b',' => self.pos += 1,
                            b']' => {
                                self.pos += 1;
                                break;
                            }
                            _ => return None,
                        }
                    }
                }
                V::Arr(start as u8, (self.narr - start) as u8)
            }
            _ => return None,
        })
    }

    fn key_eq(&self, a: Key, b: Key) -> bool {
        self.s[a.0 as usize..a.1 as usize] == self.s[b.0 as usize..b.1 as usize]
    }

    fn key_is(&self, k: Key, name: &[u8]) -> bool {
        &self.s[k.0 as usize..k.1 as usize] == name
    }

    /// The nested object, whose values are scalars.
    fn object(&mut self) -> Option<()> {
        self.pos += 1;
        self.ws();
        if self.peek()? == b'}' {
            self.pos += 1;
            return Some(());
        }
        loop {
            self.ws();
            let k = self.string()?;
            self.ws();
            self.eat(b':')?;
            self.ws();
            let v = self.scalar()?;
            if self.ninner == MAX_INNER {
                return None;
            }
            for i in 0..self.ninner {
                if self.key_eq(self.inner[i].0, k) {
                    return None;
                }
            }
            self.inner[self.ninner] = (k, v);
            self.ninner += 1;
            self.ws();
            match self.peek()? {
                b',' => self.pos += 1,
                b'}' => {
                    self.pos += 1;
                    return Some(());
                }
                _ => return None,
            }
        }
    }

    fn field(&self, name: &[u8]) -> Option<V> {
        self.inner[..self.ninner]
            .iter()
            .find(|(k, _)| self.key_is(*k, name))
            .map(|&(_, v)| v)
    }

    fn nat_field(&self, name: &[u8]) -> Option<u64> {
        match self.field(name)? {
            V::Nat(n) => Some(n),
            _ => None,
        }
    }

    fn str_field(&self, name: &[u8]) -> Option<&str> {
        match self.field(name)? {
            V::Str(a, b) => std::str::from_utf8(&self.s[a as usize..b as usize]).ok(),
            _ => None,
        }
    }

    fn text(&self, a: u32, b: u32) -> Option<&str> {
        std::str::from_utf8(&self.s[a as usize..b as usize]).ok()
    }
}

/// Try to parse `line` as a name, level or expression record.
pub(super) fn parse(line: &str, batch: &mut Batch) -> Option<Item> {
    let mut p = P {
        s: line.as_bytes(),
        pos: 0,
        arr: [0; MAX_ARR],
        narr: 0,
        inner: [((0, 0), V::Bool(false)); MAX_INNER],
        ninner: 0,
    };
    let mut top: [(Key, V); 2] = [((0, 0), V::Bool(false)); 2];
    let mut ntop = 0;
    p.ws();
    p.eat(b'{')?;
    loop {
        p.ws();
        let k = p.string()?;
        p.ws();
        p.eat(b':')?;
        p.ws();
        let v = if p.peek()? == b'{' {
            if top[..ntop].iter().any(|&(_, v)| v == V::Obj) {
                return None;
            }
            p.object()?;
            V::Obj
        } else {
            p.scalar()?
        };
        if ntop == 2 {
            return None;
        }
        top[ntop] = (k, v);
        ntop += 1;
        p.ws();
        match p.peek()? {
            b',' => p.pos += 1,
            b'}' => {
                p.pos += 1;
                break;
            }
            _ => return None,
        }
    }
    p.ws();
    if p.pos != p.s.len() || ntop != 2 || p.key_eq(top[0].0, top[1].0) {
        return None;
    }
    // The id key is the first of `in`/`il`/`ie`, as in the general path.
    let table_of = |k: Key| -> Option<u8> {
        match &p.s[k.0 as usize..k.1 as usize] {
            b"in" => Some(b'n'),
            b"il" => Some(b'l'),
            b"ie" => Some(b'e'),
            _ => None,
        }
    };
    let (i, table) = match (table_of(top[0].0), table_of(top[1].0)) {
        (Some(t), _) => (0, t),
        (None, Some(t)) => (1, t),
        (None, None) => return None,
    };
    let V::Nat(id) = top[i].1 else {
        return None;
    };
    let (kind_key, v) = top[1 - i];
    let kind = &p.s[kind_key.0 as usize..kind_key.1 as usize];
    match table {
        b'n' => {
            if v != V::Obj {
                return None;
            }
            let pre = p.nat_field(b"pre")?;
            let comp = match kind {
                b"str" => {
                    let s = p.str_field(b"str")?;
                    let (a, b) = batch.push_text(s).ok()?;
                    Comp::Str(a, b)
                }
                b"num" => Comp::Num(p.nat_field(b"i")?),
                _ => return None,
            };
            Some(Item::Name { id, pre, comp })
        }
        b'l' => {
            let node = match (kind, v) {
                (b"succ", V::Nat(l)) => RawLevel::Succ(l),
                (b"param", V::Nat(n)) => RawLevel::Param(n),
                (b"max" | b"imax", V::Arr(s, 2)) => {
                    let (a, b) = (p.arr[s as usize], p.arr[s as usize + 1]);
                    if kind == b"max" {
                        RawLevel::Max(a, b)
                    } else {
                        RawLevel::IMax(a, b)
                    }
                }
                _ => return None,
            };
            Some(Item::Level { id, node })
        }
        _ => {
            let node = match (kind, v) {
                (b"bvar", V::Nat(i)) => RawExpr::BVar(i),
                (b"sort", V::Nat(l)) => RawExpr::Sort(l),
                (b"natVal", V::Str(a, b)) => {
                    let s = p.text(a, b)?;
                    if s.is_empty() || !s.bytes().all(|c| c.is_ascii_digit()) {
                        return None;
                    }
                    let (a, b) = batch.push_text(s).ok()?;
                    RawExpr::Nat(a, b)
                }
                (b"strVal", V::Str(a, b)) => {
                    let (a, b) = batch.push_text(p.text(a, b)?).ok()?;
                    RawExpr::Str(a, b)
                }
                (_, V::Obj) => expr_obj(&p, kind, batch)?,
                _ => return None,
            };
            Some(Item::Expr { id, node })
        }
    }
}

fn expr_obj(p: &P<'_>, kind: &[u8], batch: &mut Batch) -> Option<RawExpr> {
    Some(match kind {
        b"app" => RawExpr::App(p.nat_field(b"fn")?, p.nat_field(b"arg")?),
        b"lam" | b"forallE" => {
            let bi = match p.str_field(b"binderInfo")? {
                "default" => BinderInfo::Default,
                "implicit" => BinderInfo::Implicit,
                "strictImplicit" => BinderInfo::StrictImplicit,
                "instImplicit" => BinderInfo::InstImplicit,
                _ => return None,
            };
            RawExpr::Binder {
                pi: kind == b"forallE",
                bi,
                name: p.nat_field(b"name")?,
                ty: p.nat_field(b"type")?,
                body: p.nat_field(b"body")?,
            }
        }
        b"const" => {
            let name = p.nat_field(b"name")?;
            let V::Arr(s, n) = p.field(b"us")? else {
                return None;
            };
            let start = batch.us.len();
            if start + n as usize > u32::MAX as usize {
                return None;
            }
            batch
                .us
                .extend_from_slice(&p.arr[s as usize..(s + n) as usize]);
            RawExpr::Const(name, start as u32, batch.us.len() as u32)
        }
        b"letE" => RawExpr::Let {
            name: p.nat_field(b"name")?,
            ty: p.nat_field(b"type")?,
            value: p.nat_field(b"value")?,
            body: p.nat_field(b"body")?,
            nondep: match p.field(b"nondep")? {
                V::Bool(b) => b,
                _ => return None,
            },
        },
        b"proj" => RawExpr::Proj(
            p.nat_field(b"typeName")?,
            u32::try_from(p.nat_field(b"idx")?).ok()?,
            p.nat_field(b"struct")?,
        ),
        _ => return None,
    })
}
