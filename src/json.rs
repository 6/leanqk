//! A small JSON parser for one NDJSON line, into a reusable flat tape.
//!
//! The export's records are small, shallow objects, so a general-purpose
//! JSON library would allocate per value for no gain. This parser keeps all
//! of its storage in a few `Vec`s that are reused from line to line: after
//! warm-up it does not allocate. Strings without escapes are borrowed from
//! the line; strings with escapes are decoded into a side buffer. Objects
//! with duplicate keys are rejected, as Lean's own reader does.

use std::fmt;

/// Maximum nesting depth. Export records nest at most four levels deep.
const MAX_DEPTH: usize = 64;

/// A parsed value. Containers index into the tape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Val {
    Null,
    Bool(bool),
    /// Byte range of a number's text in the line, validated per RFC 8259.
    Num(u32, u32),
    /// A string: byte range in the line, or in the decode buffer if escaped.
    Str {
        start: u32,
        end: u32,
        decoded: bool,
    },
    /// `len` elements starting at `start` in the element table.
    Arr {
        start: u32,
        len: u32,
    },
    /// `len` members starting at `start` in the member table.
    Obj {
        start: u32,
        len: u32,
    },
}

#[derive(Clone, Copy, Debug)]
pub struct Member {
    pub key: Val,
    pub val: Val,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JsonError {
    /// 1-based byte column.
    pub col: usize,
    pub msg: &'static str,
}

impl fmt::Display for JsonError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid JSON at column {}: {}", self.col, self.msg)
    }
}

/// Reusable parse state and the parsed tape of the last line.
#[derive(Default)]
pub struct Tape {
    elems: Vec<Val>,
    members: Vec<Member>,
    decoded: String,
    // Scratch stacks for building containers contiguously.
    elem_stack: Vec<Val>,
    member_stack: Vec<Member>,
}

/// A parsed line: the tape plus the line text it borrows from.
#[derive(Clone, Copy)]
pub struct Doc<'a> {
    tape: &'a Tape,
    line: &'a str,
}

impl Tape {
    pub fn new() -> Self {
        Self::default()
    }

    /// Parse `line` as exactly one JSON value surrounded by optional
    /// whitespace.
    pub fn parse<'a>(&'a mut self, line: &'a str) -> Result<(Doc<'a>, Val), JsonError> {
        self.elems.clear();
        self.members.clear();
        self.decoded.clear();
        self.elem_stack.clear();
        self.member_stack.clear();
        if line.len() >= u32::MAX as usize {
            return Err(JsonError {
                col: 1,
                msg: "line too long",
            });
        }
        let mut p = Parser {
            s: line.as_bytes(),
            line,
            pos: 0,
            tape: &mut *self,
        };
        p.ws();
        let v = p.value(0)?;
        p.ws();
        if p.pos != p.s.len() {
            return Err(p.err("trailing characters after the value"));
        }
        Ok((Doc { tape: self, line }, v))
    }
}

struct Parser<'a, 't> {
    s: &'a [u8],
    line: &'a str,
    pos: usize,
    tape: &'t mut Tape,
}

impl Parser<'_, '_> {
    fn err(&self, msg: &'static str) -> JsonError {
        JsonError {
            col: self.pos + 1,
            msg,
        }
    }

    #[inline]
    fn ws(&mut self) {
        while let Some(&c) = self.s.get(self.pos) {
            if matches!(c, b' ' | b'\t' | b'\n' | b'\r') {
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    #[inline]
    fn peek(&self) -> Option<u8> {
        self.s.get(self.pos).copied()
    }

    fn lit(&mut self, word: &'static [u8], v: Val) -> Result<Val, JsonError> {
        if self.s[self.pos..].starts_with(word) {
            self.pos += word.len();
            Ok(v)
        } else {
            Err(self.err("invalid literal"))
        }
    }

    fn value(&mut self, depth: usize) -> Result<Val, JsonError> {
        match self.peek() {
            None => Err(self.err("unexpected end of input")),
            Some(b'{') => self.object(depth + 1),
            Some(b'[') => self.array(depth + 1),
            Some(b'"') => self.string(),
            Some(b't') => self.lit(b"true", Val::Bool(true)),
            Some(b'f') => self.lit(b"false", Val::Bool(false)),
            Some(b'n') => self.lit(b"null", Val::Null),
            Some(b'-' | b'0'..=b'9') => self.number(),
            Some(_) => Err(self.err("unexpected character")),
        }
    }

    fn digits(&mut self) -> usize {
        let start = self.pos;
        while matches!(self.peek(), Some(b'0'..=b'9')) {
            self.pos += 1;
        }
        self.pos - start
    }

    fn number(&mut self) -> Result<Val, JsonError> {
        let start = self.pos;
        if self.peek() == Some(b'-') {
            self.pos += 1;
        }
        match self.peek() {
            Some(b'0') => {
                self.pos += 1;
                if matches!(self.peek(), Some(b'0'..=b'9')) {
                    return Err(self.err("leading zero in number"));
                }
            }
            Some(b'1'..=b'9') => {
                self.digits();
            }
            _ => return Err(self.err("invalid number")),
        }
        if self.peek() == Some(b'.') {
            self.pos += 1;
            if self.digits() == 0 {
                return Err(self.err("invalid number"));
            }
        }
        if matches!(self.peek(), Some(b'e' | b'E')) {
            self.pos += 1;
            if matches!(self.peek(), Some(b'+' | b'-')) {
                self.pos += 1;
            }
            if self.digits() == 0 {
                return Err(self.err("invalid number"));
            }
        }
        Ok(Val::Num(start as u32, self.pos as u32))
    }

    fn hex4(&mut self) -> Result<u32, JsonError> {
        let mut v = 0u32;
        for _ in 0..4 {
            let d = match self.peek() {
                Some(c @ b'0'..=b'9') => c - b'0',
                Some(c @ b'a'..=b'f') => c - b'a' + 10,
                Some(c @ b'A'..=b'F') => c - b'A' + 10,
                _ => return Err(self.err("invalid \\u escape")),
            };
            v = v * 16 + d as u32;
            self.pos += 1;
        }
        Ok(v)
    }

    fn string(&mut self) -> Result<Val, JsonError> {
        self.pos += 1; // opening quote
        let start = self.pos;
        // Fast path: scan for the closing quote; most strings have no escapes.
        loop {
            match self.peek() {
                None => return Err(self.err("unterminated string")),
                Some(b'"') => {
                    let end = self.pos;
                    self.pos += 1;
                    return Ok(Val::Str {
                        start: start as u32,
                        end: end as u32,
                        decoded: false,
                    });
                }
                Some(b'\\') => break,
                Some(c) if c < 0x20 => return Err(self.err("control character in string")),
                Some(_) => self.pos += 1,
            }
        }
        // Slow path: decode into the side buffer.
        let dstart = self.tape.decoded.len();
        self.tape.decoded.push_str(&self.line[start..self.pos]);
        loop {
            match self.peek() {
                None => return Err(self.err("unterminated string")),
                Some(b'"') => {
                    self.pos += 1;
                    let dend = self.tape.decoded.len();
                    if dend >= u32::MAX as usize {
                        return Err(self.err("string too long"));
                    }
                    return Ok(Val::Str {
                        start: dstart as u32,
                        end: dend as u32,
                        decoded: true,
                    });
                }
                Some(b'\\') => {
                    self.pos += 1;
                    let c = match self.peek() {
                        Some(b'"') => '"',
                        Some(b'\\') => '\\',
                        Some(b'/') => '/',
                        Some(b'b') => '\u{8}',
                        Some(b'f') => '\u{c}',
                        Some(b'n') => '\n',
                        Some(b'r') => '\r',
                        Some(b't') => '\t',
                        Some(b'u') => {
                            self.pos += 1;
                            let hi = self.hex4()?;
                            let cp = if (0xD800..0xDC00).contains(&hi) {
                                if !self.s[self.pos..].starts_with(b"\\u") {
                                    return Err(self.err("unpaired surrogate in \\u escape"));
                                }
                                self.pos += 2;
                                let lo = self.hex4()?;
                                if !(0xDC00..0xE000).contains(&lo) {
                                    return Err(self.err("unpaired surrogate in \\u escape"));
                                }
                                0x10000 + ((hi - 0xD800) << 10) + (lo - 0xDC00)
                            } else {
                                hi
                            };
                            let Some(c) = char::from_u32(cp) else {
                                return Err(self.err("unpaired surrogate in \\u escape"));
                            };
                            self.tape.decoded.push(c);
                            continue;
                        }
                        _ => return Err(self.err("invalid escape")),
                    };
                    self.pos += 1;
                    self.tape.decoded.push(c);
                }
                Some(c) if c < 0x20 => return Err(self.err("control character in string")),
                Some(_) => {
                    // Copy a run of plain bytes. The line is valid UTF-8 and
                    // the run stops at ASCII, so the slice is on boundaries.
                    let run = self.pos;
                    while let Some(c) = self.peek() {
                        if c == b'"' || c == b'\\' || c < 0x20 {
                            break;
                        }
                        self.pos += 1;
                    }
                    self.tape.decoded.push_str(&self.line[run..self.pos]);
                }
            }
        }
    }

    fn array(&mut self, depth: usize) -> Result<Val, JsonError> {
        if depth > MAX_DEPTH {
            return Err(self.err("nesting too deep"));
        }
        self.pos += 1;
        let base = self.tape.elem_stack.len();
        self.ws();
        if self.peek() == Some(b']') {
            self.pos += 1;
        } else {
            loop {
                self.ws();
                let v = self.value(depth)?;
                self.tape.elem_stack.push(v);
                self.ws();
                match self.peek() {
                    Some(b',') => self.pos += 1,
                    Some(b']') => {
                        self.pos += 1;
                        break;
                    }
                    _ => return Err(self.err("expected ',' or ']'")),
                }
            }
        }
        let start = self.tape.elems.len();
        let len = self.tape.elem_stack.len() - base;
        self.tape.elems.extend(self.tape.elem_stack.drain(base..));
        Ok(Val::Arr {
            start: start as u32,
            len: len as u32,
        })
    }

    fn object(&mut self, depth: usize) -> Result<Val, JsonError> {
        if depth > MAX_DEPTH {
            return Err(self.err("nesting too deep"));
        }
        self.pos += 1;
        let base = self.tape.member_stack.len();
        self.ws();
        if self.peek() == Some(b'}') {
            self.pos += 1;
        } else {
            loop {
                self.ws();
                if self.peek() != Some(b'"') {
                    return Err(self.err("expected a string key"));
                }
                let key_pos = self.pos;
                let key = self.string()?;
                let k = doc_str(self.tape, self.line, key);
                if self.tape.member_stack[base..]
                    .iter()
                    .any(|m| doc_str(self.tape, self.line, m.key) == k)
                {
                    return Err(JsonError {
                        col: key_pos + 1,
                        msg: "duplicate key in object",
                    });
                }
                self.ws();
                if self.peek() != Some(b':') {
                    return Err(self.err("expected ':'"));
                }
                self.pos += 1;
                self.ws();
                let val = self.value(depth)?;
                self.tape.member_stack.push(Member { key, val });
                self.ws();
                match self.peek() {
                    Some(b',') => self.pos += 1,
                    Some(b'}') => {
                        self.pos += 1;
                        break;
                    }
                    _ => return Err(self.err("expected ',' or '}'")),
                }
            }
        }
        let start = self.tape.members.len();
        let len = self.tape.member_stack.len() - base;
        self.tape
            .members
            .extend(self.tape.member_stack.drain(base..));
        Ok(Val::Obj {
            start: start as u32,
            len: len as u32,
        })
    }
}

fn doc_str<'a>(tape: &'a Tape, line: &'a str, v: Val) -> &'a str {
    match v {
        Val::Str {
            start,
            end,
            decoded,
        } => {
            let src = if decoded { &tape.decoded } else { line };
            &src[start as usize..end as usize]
        }
        _ => "",
    }
}

impl<'a> Doc<'a> {
    /// The text of a string value, or `None` if `v` is not a string.
    pub fn str(&self, v: Val) -> Option<&'a str> {
        match v {
            Val::Str { .. } => Some(doc_str(self.tape, self.line, v)),
            _ => None,
        }
    }

    /// The raw text of a number value.
    pub fn num_text(&self, v: Val) -> Option<&'a str> {
        match v {
            Val::Num(a, b) => Some(&self.line[a as usize..b as usize]),
            _ => None,
        }
    }

    /// A number written as a plain non-negative integer that fits a `u64`.
    pub fn nat(&self, v: Val) -> Option<u64> {
        let t = self.num_text(v)?;
        if t.is_empty() || !t.bytes().all(|c| c.is_ascii_digit()) {
            return None;
        }
        t.parse().ok()
    }

    pub fn elems(&self, v: Val) -> Option<&'a [Val]> {
        match v {
            Val::Arr { start, len } => {
                Some(&self.tape.elems[start as usize..(start + len) as usize])
            }
            _ => None,
        }
    }

    pub fn members(&self, v: Val) -> Option<&'a [Member]> {
        match v {
            Val::Obj { start, len } => {
                Some(&self.tape.members[start as usize..(start + len) as usize])
            }
            _ => None,
        }
    }

    pub fn key(&self, m: &Member) -> &'a str {
        doc_str(self.tape, self.line, m.key)
    }

    /// Look up a key in an object's members.
    pub fn get(&self, members: &[Member], key: &str) -> Option<Val> {
        members
            .iter()
            .find(|m| doc_str(self.tape, self.line, m.key) == key)
            .map(|m| m.val)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ok(s: &str) {
        let mut t = Tape::new();
        if let Err(e) = t.parse(s) {
            panic!("{s}: {e}");
        }
    }

    fn bad(s: &str) -> JsonError {
        let mut t = Tape::new();
        match t.parse(s) {
            Ok(_) => panic!("accepted {s}"),
            Err(e) => e,
        }
    }

    #[test]
    fn values() {
        let mut t = Tape::new();
        let line = r#" {"a":[1, 2 ,{"b":null}],"c":"x\"y\u00e9\ud83d\ude00","d":true,"e":-1.5e3} "#;
        let (doc, v) = t.parse(line).unwrap();
        let m = doc.members(v).unwrap();
        assert_eq!(m.len(), 4);
        let a = doc.elems(doc.get(m, "a").unwrap()).unwrap();
        assert_eq!(doc.nat(a[0]), Some(1));
        assert_eq!(doc.nat(a[1]), Some(2));
        let inner = doc.members(a[2]).unwrap();
        assert_eq!(doc.get(inner, "b"), Some(Val::Null));
        assert_eq!(
            doc.str(doc.get(m, "c").unwrap()),
            Some("x\"y\u{e9}\u{1F600}")
        );
        assert_eq!(doc.get(m, "d"), Some(Val::Bool(true)));
        let e = doc.get(m, "e").unwrap();
        assert_eq!(doc.num_text(e), Some("-1.5e3"));
        assert_eq!(doc.nat(e), None);
        assert_eq!(doc.get(m, "zz"), None);
    }

    #[test]
    fn grammar() {
        ok("{}");
        ok("[]");
        ok("0");
        ok("\"\"");
        ok(r#"{"a\u0062":1,"ab ":2}"#);
        bad("");
        bad("{");
        bad("{} {}");
        bad("01");
        bad("1.");
        bad("[1,]");
        bad("{\"a\":1,}");
        bad("{\"a\" 1}");
        bad("tru");
        bad("\"\\x\"");
        bad("\"\\ud800\"");
        bad("\"\\udc00\"");
        bad("\"a\u{1}\"");
        bad("\"abc");
        assert_eq!(bad(r#"{"a":1,"a":2}"#).msg, "duplicate key in object");
        assert_eq!(
            bad(r#"{"ab":1,"a\u0062":2}"#).msg,
            "duplicate key in object"
        );
        assert_eq!(bad(&"[".repeat(1000)).msg, "nesting too deep");
    }

    #[test]
    fn nat_range() {
        let mut t = Tape::new();
        let (doc, v) = t
            .parse("[18446744073709551615, 18446744073709551616]")
            .unwrap();
        let a = doc.elems(v).unwrap();
        assert_eq!(doc.nat(a[0]), Some(u64::MAX));
        assert_eq!(doc.nat(a[1]), None);
    }
}
