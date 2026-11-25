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

use super::{Comp, Fail, Item, R, RawExpr, RawLevel};
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

    /// Keep the failure of one of the above, for the caller of [`line`].
    fn fail(&mut self, f: Fail);
}

/// Whether `r` is a success; if not, its failure goes to `sink`.
#[inline(always)]
fn ok<S: Sink>(sink: &mut S, r: R<()>) -> bool {
    match r {
        Ok(()) => true,
        Err(f) => {
            sink.fail(f);
            false
        }
    }
}

/// A literal of `N` bytes (at most 16), as two little-endian words,
/// padded with zeros.
#[derive(Clone, Copy)]
struct Lit<const N: usize>([u64; 2]);

impl<const N: usize> Lit<N> {
    const fn new(w: &[u8; N]) -> Self {
        assert!(N <= 16);
        let mut pad = [0u8; 16];
        let mut i = 0;
        while i < N {
            pad[i] = w[i];
            i += 1;
        }
        let (mut lo, mut hi) = (0u64, 0u64);
        let mut i = 8;
        while i > 0 {
            i -= 1;
            lo = lo << 8 | pad[i] as u64;
            hi = hi << 8 | pad[i + 8] as u64;
        }
        Lit([lo, hi])
    }
}

/// The literals of the records (but the shortest) and the constants of
/// [`C::nat`]. The scanner reads them through a reference the compiler
/// cannot see through (see [`line`]), so that each is one load from the
/// cache, and not up to four instructions to build it again in every
/// line.
struct Keys {
    abbrev_word: Lit<8>,
    app_arg: Lit<12>,
    binder_info_str: Lit<14>,
    bvar: Lit<6>,
    close_next_ie: Lit<7>,
    const_name: Lit<15>,
    def_record: Lit<5>,
    default_word: Lit<8>,
    expr_id: Lit<4>,
    false_word: Lit<5>,
    forall_e_obj: Lit<10>,
    imax_list: Lit<7>,
    implicit_word: Lit<9>,
    inst_implicit_word: Lit<13>,
    lam_obj: Lit<6>,
    let_e_body: Lit<14>,
    level_id: Lit<4>,
    max_list: Lit<6>,
    name_id: Lit<4>,
    nat_val_str: Lit<9>,
    next_body: Lit<8>,
    next_fn: Lit<6>,
    next_hints: Lit<9>,
    next_ie: Lit<6>,
    next_level_params_list: Lit<16>,
    next_name: Lit<8>,
    next_nondep: Lit<10>,
    next_num_i: Lit<12>,
    next_pre: Lit<7>,
    next_safety_str: Lit<11>,
    next_str_pre: Lit<14>,
    next_str_str: Lit<8>,
    next_struct: Lit<10>,
    next_type: Lit<8>,
    next_type_name: Lit<12>,
    next_us_list: Lit<7>,
    next_value: Lit<9>,
    opaque_word: Lit<8>,
    open_all_list: Lit<8>,
    open_regular: Lit<11>,
    param: Lit<7>,
    partial_word: Lit<8>,
    proj_idx: Lit<13>,
    safe_word: Lit<5>,
    sort: Lit<6>,
    str_val_str: Lit<9>,
    strict_implicit_word: Lit<15>,
    succ: Lit<6>,
    thm_record: Lit<5>,
    true_word: Lit<4>,
    unsafe_word: Lit<7>,
    /// `0x76` in each byte: added to a digit (0 to 9), it stays below
    /// `0x80`.
    below_ten: u64,
    /// Joins two four-digit halves (`10000 << 32 | 1`).
    join: u64,
}

static KEYS: Keys = Keys {
    abbrev_word: Lit::new(b"\"abbrev\""),
    app_arg: Lit::new(b"app\":{\"arg\":"),
    binder_info_str: Lit::new(b"\"binderInfo\":\""),
    bvar: Lit::new(b"bvar\":"),
    close_next_ie: Lit::new(b"},\"ie\":"),
    const_name: Lit::new(b"const\":{\"name\":"),
    def_record: Lit::new(b"def\":"),
    default_word: Lit::new(b"default\""),
    expr_id: Lit::new(b"ie\":"),
    false_word: Lit::new(b"false"),
    forall_e_obj: Lit::new(b"forallE\":{"),
    imax_list: Lit::new(b"imax\":["),
    implicit_word: Lit::new(b"implicit\""),
    inst_implicit_word: Lit::new(b"instImplicit\""),
    lam_obj: Lit::new(b"lam\":{"),
    let_e_body: Lit::new(b"letE\":{\"body\":"),
    level_id: Lit::new(b"il\":"),
    max_list: Lit::new(b"max\":["),
    name_id: Lit::new(b"in\":"),
    nat_val_str: Lit::new(b"natVal\":\""),
    next_body: Lit::new(b",\"body\":"),
    next_fn: Lit::new(b",\"fn\":"),
    next_hints: Lit::new(b",\"hints\":"),
    next_ie: Lit::new(b",\"ie\":"),
    next_level_params_list: Lit::new(b",\"levelParams\":["),
    next_name: Lit::new(b",\"name\":"),
    next_nondep: Lit::new(b",\"nondep\":"),
    next_num_i: Lit::new(b",\"num\":{\"i\":"),
    next_pre: Lit::new(b",\"pre\":"),
    next_safety_str: Lit::new(b",\"safety\":\""),
    next_str_pre: Lit::new(b",\"str\":{\"pre\":"),
    next_str_str: Lit::new(b",\"str\":\""),
    next_struct: Lit::new(b",\"struct\":"),
    next_type: Lit::new(b",\"type\":"),
    next_type_name: Lit::new(b",\"typeName\":"),
    next_us_list: Lit::new(b",\"us\":["),
    next_value: Lit::new(b",\"value\":"),
    opaque_word: Lit::new(b"\"opaque\""),
    open_all_list: Lit::new(b"{\"all\":["),
    open_regular: Lit::new(b"{\"regular\":"),
    param: Lit::new(b"param\":"),
    partial_word: Lit::new(b"partial\""),
    proj_idx: Lit::new(b"proj\":{\"idx\":"),
    safe_word: Lit::new(b"safe\""),
    sort: Lit::new(b"sort\":"),
    str_val_str: Lit::new(b"strVal\":\""),
    strict_implicit_word: Lit::new(b"strictImplicit\""),
    succ: Lit::new(b"succ\":"),
    thm_record: Lit::new(b"thm\":"),
    true_word: Lit::new(b"true"),
    unsafe_word: Lit::new(b"unsafe\""),
    below_ten: 0x7676_7676_7676_7676,
    join: 42_949_672_960_001,
};

/// Bytes of the window a line is scanned from: a record the scanner
/// takes ends before byte [`MASK`], and loads at a position below that
/// reach at most 32 bytes further.
const W: usize = 288;
const MASK: usize = 255;

/// A cursor over a line. Bytes are read from `w`, the first [`W`] bytes
/// of the input from the line on (padded with zeros at the end of the
/// input), at positions masked with [`MASK`], so that no read needs a
/// bounds check. A position past [`MASK`] would read the wrong bytes, so
/// [`C::eol`] declines the line then (positions only grow); and it
/// declines a line that would end past `len`, the bytes really there.
#[derive(Clone, Copy)]
struct C<'a> {
    /// The rest of the input.
    s: &'a [u8],
    w: &'a [u8; W],
    p: usize,
    k: &'a Keys,
}

impl C<'_> {
    /// The byte `k` (below 32) past the cursor.
    #[inline(always)]
    fn at(&self, k: usize) -> u8 {
        self.w[self.p + k]
    }

    /// The eight bytes from `k` (below 24) past the cursor.
    #[inline(always)]
    fn word(&self, k: usize) -> u64 {
        let i = self.p + k;
        u64::from_le_bytes(self.w[i..i + 8].try_into().expect("8 bytes"))
    }

    /// Expect the bytes `w` (at most 16).
    #[inline(always)]
    fn lit<const N: usize>(&mut self, w: &[u8; N]) -> Option<()> {
        const { assert!(N <= 16) };
        if self.p > MASK {
            return None;
        }
        // Compare words: the literal, padded with zeros, against the
        // input with the bytes past the literal masked off.
        let mut pad = [0u8; 16];
        pad[..N].copy_from_slice(w);
        let lo = u64::from_le_bytes(pad[..8].try_into().expect("8"));
        let hi = u64::from_le_bytes(pad[8..].try_into().expect("8"));
        let mask = |n: usize| {
            if n >= 8 {
                u64::MAX
            } else {
                (1u64 << (8 * n)) - 1
            }
        };
        let x = self.word(0);
        let ok = if N <= 8 {
            x & mask(N) == lo
        } else {
            x == lo && self.word(8) & mask(N - 8) == hi
        };
        if ok {
            self.p += N;
            Some(())
        } else {
            None
        }
    }

    /// Expect the literal `w` (of more than two bytes: shorter ones are
    /// cheap to build, see [`Keys`]).
    #[inline(always)]
    fn key<const N: usize>(&mut self, w: Lit<N>) -> Option<()> {
        const { assert!(N > 2 && N <= 16) };
        if self.p > MASK {
            return None;
        }
        let mask = |n: usize| {
            if n >= 8 {
                u64::MAX
            } else {
                (1u64 << (8 * n)) - 1
            }
        };
        let x = self.word(0);
        let ok = if N <= 8 {
            x & mask(N) == w.0[0]
        } else {
            x == w.0[0] && self.word(8) & mask(N - 8) == w.0[1]
        };
        if ok {
            self.p += N;
            Some(())
        } else {
            None
        }
    }

    /// Whether the literal `w` comes next (and if so, skip it).
    #[inline(always)]
    fn opt_key<const N: usize>(&mut self, w: Lit<N>) -> bool {
        self.key(w).is_some()
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
        if self.p > MASK {
            return None;
        }
        let w = self.word(0);
        // Digits become 0 to 9, and every other byte something else (this
        // is one instruction, where a subtraction would take three).
        let x = w ^ 0x3030_3030_3030_3030;
        // The high bit of each byte that is not a digit. A byte below a
        // non-digit is a digit, so no carry reaches the first non-digit
        // from below.
        let t = (x | x.wrapping_add(self.k.below_ten)) & 0x8080_8080_8080_8080;
        // Eight times the number of leading digits (`t` has bits only at
        // 7, 15, ..., so this is 8n for n < 8, and 64 when t is 0).
        let n8 = t.trailing_zeros() & !7;
        // No digits, or a leading zero.
        if n8 == 0 || (n8 > 8 && w as u8 == b'0') {
            return None;
        }
        // The digits, most significant first, as eight digits with
        // leading zeros.
        // (Each step joins neighbours: `d * 10 + (d >> 8)` is
        // `(d * 2561) >> 8` in the bytes kept, without a constant to load.)
        let d = x << (64 - n8);
        let d = d.wrapping_mul(10).wrapping_add(d >> 8) & 0x00FF_00FF_00FF_00FF;
        let d = d.wrapping_mul(100).wrapping_add(d >> 16) & 0x0000_FFFF_0000_FFFF;
        let d = d.wrapping_mul(self.k.join) >> 32;
        if n8 == 64 {
            // A ninth digit (ids of a big export), or more.
            let c = self.at(8);
            if c.is_ascii_digit() {
                if self.at(9).is_ascii_digit() {
                    let (v, n) = nat_slow(self.w, self.p)?;
                    self.p += n;
                    return Some(v);
                }
                self.p += 9;
                return Some(d * 10 + (c - b'0') as u64);
            }
        }
        self.p += (n8 / 8) as usize;
        Some(d)
    }

    /// The contents of a string without escapes or control characters
    /// (the opening quote is already read), as a range of the line.
    #[inline(always)]
    fn string(&mut self) -> Option<(u32, u32)> {
        let start = self.p;
        // Eight bytes at a time: the first that is a quote, a backslash or
        // a control character (the lowest byte each test flags is exact,
        // as a test only flags a byte wrongly above one it flags rightly).
        const ONES: u64 = 0x0101_0101_0101_0101;
        const HIGH: u64 = 0x8080_8080_8080_8080;
        let zero = |x: u64| x.wrapping_sub(ONES) & !x & HIGH;
        loop {
            if self.p >= MASK {
                return None;
            }
            let x = self.word(0);
            let t = (x.wrapping_sub(0x20 * ONES) & !x & HIGH)
                | zero(x ^ (b'"' as u64 * ONES))
                | zero(x ^ (b'\\' as u64 * ONES));
            if t == 0 {
                self.p += 8;
                continue;
            }
            self.p += (t.trailing_zeros() / 8) as usize;
            if self.at(0) != b'"' {
                return None;
            }
            break;
        }
        let end = self.p;
        self.p += 1;
        let text = self.s.get(start..end)?;
        if !text.is_ascii() {
            std::str::from_utf8(text).ok()?;
        }
        Some((u32::try_from(start).ok()?, u32::try_from(end).ok()?))
    }

    #[inline(always)]
    fn binder_info(&mut self) -> Option<BinderInfo> {
        Some(match self.at(0) {
            b'd' if self.opt_key(self.k.default_word) => BinderInfo::Default,
            b'i' if self.opt_key(self.k.implicit_word) => BinderInfo::Implicit,
            b'i' if self.opt_key(self.k.inst_implicit_word) => BinderInfo::InstImplicit,
            b's' if self.opt_key(self.k.strict_implicit_word) => BinderInfo::StrictImplicit,
            _ => return None,
        })
    }

    /// `"binderInfo":"…","body":B,"name":N,"type":T}`, after the
    /// binder's opening brace: binder info, name, type and body.
    #[inline(always)]
    fn binder(&mut self) -> Option<(BinderInfo, u64, u64, u64)> {
        self.key(self.k.binder_info_str)?;
        let bi = self.binder_info()?;
        self.key(self.k.next_body)?;
        let body = self.nat()?;
        self.key(self.k.next_name)?;
        let name = self.nat()?;
        self.key(self.k.next_type)?;
        let ty = self.nat()?;
        self.lit(b"}")?;
        Some((bi, name, ty, body))
    }

    /// The end of a line: a newline, or the end of the input. This also
    /// checks that the line was read from the right bytes (see [`C`]).
    #[inline(always)]
    fn eol(&mut self) -> Option<()> {
        if self.p >= MASK || self.p > self.s.len() {
            return None;
        }
        if self.p == self.s.len() {
            return Some(());
        }
        if self.at(0) == b'\n' {
            self.p += 1;
            return Some(());
        }
        None
    }
}

impl C<'_> {
    /// A list of numbers (the opening bracket is already read), pushed to
    /// `us`: the range they take there.
    #[inline(always)]
    fn nats(&mut self, us: &mut Vec<u64>) -> Option<(usize, usize)> {
        let start = us.len();
        if !self.opt(b"]") {
            loop {
                if self.p >= MASK {
                    return None;
                }
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
    /// (This takes the cursor by value, so that the caller's stays in
    /// registers; the position after the line is the second result.)
    fn decl(mut self, thm: bool, us: &mut Vec<u64>) -> Option<(Decl, usize)> {
        us.clear();
        self.key(self.k.open_all_list)?;
        let all = self.nats(us)?;
        let mut hints = Hints::Opaque;
        if !thm {
            self.key(self.k.next_hints)?;
            hints = if self.opt_key(self.k.abbrev_word) {
                Hints::Abbrev
            } else if self.opt_key(self.k.opaque_word) {
                Hints::Opaque
            } else {
                self.key(self.k.open_regular)?;
                let h = u32::try_from(self.nat()?).ok()?;
                self.lit(b"}")?;
                Hints::Regular(h)
            };
        }
        self.key(self.k.next_level_params_list)?;
        let level_params = self.nats(us)?;
        self.key(self.k.next_name)?;
        let name = self.nat()?;
        let mut safety = Safety::Safe;
        if !thm {
            self.key(self.k.next_safety_str)?;
            safety = if self.opt_key(self.k.safe_word) {
                Safety::Safe
            } else if self.opt_key(self.k.unsafe_word) {
                Safety::Unsafe
            } else {
                self.key(self.k.partial_word)?;
                Safety::Partial
            };
        }
        self.key(self.k.next_type)?;
        let ty = self.nat()?;
        self.key(self.k.next_value)?;
        let value = self.nat()?;
        self.lit(b"}}")?;
        self.eol()?;
        let d = Decl {
            thm,
            all,
            level_params,
            name,
            ty,
            value,
            hints,
            safety,
        };
        Some((d, self.p))
    }
}

/// [`C::nat`] a digit at a time, from `p` (at most [`MASK`]): the value
/// and the number of digits.
#[cold]
#[inline(never)]
fn nat_slow(w: &[u8; W], p: usize) -> Option<(u64, usize)> {
    let w = &w[p.min(MASK)..];
    let mut v: u64 = 0;
    let mut n = 0;
    while w[n].is_ascii_digit() {
        if n == 19 {
            return None;
        }
        v = v * 10 + (w[n] - b'0') as u64;
        n += 1;
    }
    if n == 0 || (n > 1 && w[0] == b'0') {
        return None;
    }
    Some((v, n))
}

/// Read the record at the start of `s` (a line, and maybe more input
/// after it), and give it to `sink`. On success, the length of the line,
/// newline included, and whether the sink took it (if not, it was given
/// the failure). `us` is scratch space.
#[inline(always)]
pub(super) fn line<S: Sink>(s: &[u8], us: &mut Vec<u64>, sink: &mut S) -> Option<(usize, bool)> {
    // Opaque to the compiler, so that it loads the literals (see `Keys`).
    let k = std::hint::black_box(&KEYS);
    match s.first_chunk::<W>() {
        Some(w) => line_in(C { s, w, p: 0, k }, us, sink),
        None => line_padded(s, us, sink),
    }
}

/// [`line`] near the end of the input, with the window padded.
#[cold]
#[inline(never)]
fn line_padded<S: Sink>(s: &[u8], us: &mut Vec<u64>, sink: &mut S) -> Option<(usize, bool)> {
    let mut w = [0u8; W];
    w[..s.len()].copy_from_slice(s);
    line_in(
        C {
            s,
            w: &w,
            p: 0,
            k: std::hint::black_box(&KEYS),
        },
        us,
        sink,
    )
}

#[inline(always)]
fn line_in<S: Sink>(mut c: C<'_>, us: &mut Vec<u64>, sink: &mut S) -> Option<(usize, bool)> {
    let s = c.s;
    c.lit(b"{\"")?;
    let item = match c.at(0) {
        b'a' => {
            c.key(c.k.app_arg)?;
            let a = c.nat()?;
            c.key(c.k.next_fn)?;
            let f = c.nat()?;
            c.key(c.k.close_next_ie)?;
            let id = c.nat()?;
            c.lit(b"}")?;
            c.eol()?;
            let r = sink.app(id, f, a);
            return Some((c.p, ok(sink, r)));
        }
        b'f' => {
            c.key(c.k.forall_e_obj)?;
            let (bi, name, ty, body) = c.binder()?;
            c.key(c.k.next_ie)?;
            let id = c.nat()?;
            c.lit(b"}")?;
            c.eol()?;
            let r = sink.binder(id, true, bi, name, ty, body);
            return Some((c.p, ok(sink, r)));
        }
        b'c' => {
            c.key(c.k.const_name)?;
            let name = c.nat()?;
            c.key(c.k.next_us_list)?;
            us.clear();
            let (start, _) = c.nats(us)?;
            c.key(c.k.close_next_ie)?;
            let id = c.nat()?;
            c.lit(b"}")?;
            let (a, b) = (u32::try_from(start).ok()?, u32::try_from(us.len()).ok()?);
            Item::Expr {
                id,
                node: RawExpr::Const(name, a, b),
            }
        }
        b't' | b'd' => {
            let thm = c.at(0) == b't';
            if thm {
                c.key(c.k.thm_record)?;
            } else {
                c.key(c.k.def_record)?;
            }
            let (d, p) = c.decl(thm, us)?;
            c.p = p;
            let r = sink.decl(&d, us)?;
            return Some((c.p, ok(sink, r)));
        }
        b'b' => {
            c.key(c.k.bvar)?;
            let i = c.nat()?;
            c.key(c.k.next_ie)?;
            let id = c.nat()?;
            c.lit(b"}")?;
            Item::Expr {
                id,
                node: RawExpr::BVar(i),
            }
        }
        b'i' => match c.at(1) {
            b'e' => {
                c.key(c.k.expr_id)?;
                let id = c.nat()?;
                c.lit(b",\"")?;
                let node = match c.at(0) {
                    b'l' if c.opt_key(c.k.lam_obj) => {
                        let (bi, name, ty, body) = c.binder()?;
                        c.lit(b"}")?;
                        c.eol()?;
                        let r = sink.binder(id, false, bi, name, ty, body);
                        return Some((c.p, ok(sink, r)));
                    }
                    b'l' => {
                        c.key(c.k.let_e_body)?;
                        let body = c.nat()?;
                        c.key(c.k.next_name)?;
                        let name = c.nat()?;
                        c.key(c.k.next_nondep)?;
                        let nondep = if c.opt_key(c.k.false_word) {
                            false
                        } else {
                            c.key(c.k.true_word)?;
                            true
                        };
                        c.key(c.k.next_type)?;
                        let ty = c.nat()?;
                        c.key(c.k.next_value)?;
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
                        c.key(c.k.proj_idx)?;
                        let idx = u32::try_from(c.nat()?).ok()?;
                        c.key(c.k.next_struct)?;
                        let e = c.nat()?;
                        c.key(c.k.next_type_name)?;
                        let name = c.nat()?;
                        c.lit(b"}}")?;
                        RawExpr::Proj(name, idx, e)
                    }
                    b's' if c.opt_key(c.k.sort) => {
                        let l = c.nat()?;
                        c.lit(b"}")?;
                        RawExpr::Sort(l)
                    }
                    b's' => {
                        c.key(c.k.str_val_str)?;
                        let (a, b) = c.string()?;
                        c.lit(b"}")?;
                        RawExpr::Str(a, b)
                    }
                    b'n' => {
                        c.key(c.k.nat_val_str)?;
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
                c.key(c.k.name_id)?;
                let id = c.nat()?;
                let (pre, comp) = if c.opt_key(c.k.next_str_pre) {
                    let pre = c.nat()?;
                    c.key(c.k.next_str_str)?;
                    let (a, b) = c.string()?;
                    (pre, Comp::Str(a, b))
                } else {
                    c.key(c.k.next_num_i)?;
                    let i = c.nat()?;
                    c.key(c.k.next_pre)?;
                    (c.nat()?, Comp::Num(i))
                };
                c.lit(b"}}")?;
                Item::Name { id, pre, comp }
            }
            b'l' => {
                c.key(c.k.level_id)?;
                let id = c.nat()?;
                c.lit(b",\"")?;
                let node = match c.at(0) {
                    b's' => {
                        c.key(c.k.succ)?;
                        RawLevel::Succ(c.nat()?)
                    }
                    b'p' => {
                        c.key(c.k.param)?;
                        RawLevel::Param(c.nat()?)
                    }
                    k @ (b'm' | b'i') => {
                        if k == b'm' {
                            c.key(c.k.max_list)?;
                        } else {
                            c.key(c.k.imax_list)?;
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
    let r = sink.item(item, s, us);
    Some((c.p, ok(sink, r)))
}
