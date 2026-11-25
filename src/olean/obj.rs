//! A bounds-checked view of compacted Lean objects.
//!
//! A module's parts (`.olean`, `.olean.server`, `.olean.private`) are
//! compacted into one logical address space: a pointer is a logical address
//! in one of the parts. [`Heap`] resolves a pointer to the bytes of the
//! object it names, checking that it lies wholly inside a part's data
//! section, is aligned, and has a header that agrees with its size.
//!
//! The compactor writes every object after all the objects it points to
//! (`object_compactor::insert_constructor` in `src/runtime/compact.cpp`), and
//! later parts after earlier ones, so a pointer always names a lower address
//! than the object holding it. [`Heap::get`] enforces that: a file whose
//! pointers do not strictly decrease is rejected, so no walk over the object
//! graph can loop.

use super::Fail;
use super::file::OleanFile;

pub const MAX_CTOR_TAG: u8 = 243;
pub const TAG_ARRAY: u8 = 246;
pub const TAG_STRING: u8 = 249;
pub const TAG_MPZ: u8 = 250;

/// One part's data section, in logical addresses.
struct Part<'a> {
    bytes: &'a [u8],
    base: u64,
    lo: u64,
    hi: u64,
}

pub struct Heap<'a> {
    parts: Vec<Part<'a>>,
    pub gmp: bool,
}

/// A value of a Lean field: a boxed scalar or an object.
#[derive(Clone, Copy)]
pub enum Val<'a> {
    Scalar(u64),
    Obj(Obj<'a>),
}

/// A compacted object: its address, header and bytes (header included).
#[derive(Clone, Copy)]
pub struct Obj<'a> {
    pub addr: u64,
    pub tag: u8,
    pub other: u8,
    bytes: &'a [u8],
}

fn rd64(b: &[u8], off: usize) -> Option<u64> {
    Some(u64::from_le_bytes(b.get(off..off + 8)?.try_into().ok()?))
}

impl<'a> Heap<'a> {
    /// The heap of a module's parts, in order. Later parts may point into
    /// earlier ones.
    pub fn new(files: &[&'a OleanFile]) -> Result<Heap<'a>, Fail> {
        let mut parts = Vec::new();
        let mut gmp = None;
        for f in files {
            if *gmp.get_or_insert(f.gmp) != f.gmp {
                return Err(Fail::malformed(
                    "module parts disagree on the big number layout",
                ));
            }
            let lo = f.base + f.data_off as u64;
            parts.push(Part {
                bytes: f.bytes(),
                base: f.base,
                lo,
                hi: lo + f.data_len as u64,
            });
        }
        parts.sort_by_key(|p| p.lo);
        for w in parts.windows(2) {
            if w[0].hi > w[1].lo {
                return Err(Fail::malformed("module parts overlap in the address space"));
            }
        }
        Ok(Heap {
            parts,
            gmp: gmp.unwrap_or(true),
        })
    }

    /// The logical address ranges of the parts' data, in order.
    pub fn ranges(&self) -> impl Iterator<Item = (u64, u64)> + '_ {
        self.parts.iter().map(|p| (p.lo, p.hi))
    }

    /// The bytes from logical address `addr` to the end of its part's
    /// data, if it is in a part.
    pub fn raw(&self, addr: u64) -> Option<&'a [u8]> {
        let p = self.parts.iter().rev().find(|p| p.lo <= addr)?;
        if addr >= p.hi {
            return None;
        }
        p.bytes
            .get((addr - p.base) as usize..(p.hi - p.base) as usize)
    }

    /// Resolve the field value `ptr`, held by an object at address `holder`
    /// (`u64::MAX` for the root).
    pub fn get(&self, ptr: u64, holder: u64) -> Result<Val<'a>, Fail> {
        if ptr & 1 == 1 {
            return Ok(Val::Scalar(ptr >> 1));
        }
        if ptr >= holder {
            return Err(Fail::malformed(format!(
                "pointer {ptr:#x} does not point below its holder {holder:#x}"
            )));
        }
        self.obj(ptr).map(Val::Obj)
    }

    fn obj(&self, ptr: u64) -> Result<Obj<'a>, Fail> {
        let bad = |why: &str| Err(Fail::malformed(format!("bad pointer {ptr:#x}: {why}")));
        if !ptr.is_multiple_of(8) {
            return bad("misaligned");
        }
        // Parts are sorted; most objects are in the last one.
        let Some(p) = self.parts.iter().rev().find(|p| p.lo <= ptr) else {
            return bad("outside the module");
        };
        if ptr >= p.hi || p.hi - ptr < 8 {
            return bad("outside the module");
        }
        let off = (ptr - p.base) as usize;
        let end = (p.hi - p.base) as usize;
        let b = &p.bytes[off..end];
        let rc = i32::from_le_bytes(b[0..4].try_into().expect("4"));
        let cs_sz = u16::from_le_bytes(b[4..6].try_into().expect("2")) as usize;
        let other = b[6];
        let tag = b[7];
        if rc != 0 {
            return bad("not a compacted object");
        }
        let size: Option<usize> = match tag {
            0..=MAX_CTOR_TAG => (cs_sz >= 8 + 8 * other as usize).then_some(cs_sz),
            TAG_ARRAY => {
                rd64(b, 8).and_then(|n| usize::try_from(n).ok()?.checked_mul(8)?.checked_add(24))
            }
            TAG_STRING => rd64(b, 8).and_then(|n| usize::try_from(n).ok()?.checked_add(32)),
            TAG_MPZ => (cs_sz >= 24).then_some(cs_sz),
            _ => return bad(&format!("unexpected object kind {tag}")),
        };
        match size {
            Some(n) if n <= b.len() => Ok(Obj {
                addr: ptr,
                tag,
                other,
                bytes: &b[..n],
            }),
            _ => bad("object extends past the end of its part"),
        }
    }

    /// The limbs of a GMP-layout big number (`_mp_d` points just past the
    /// `mpz_object`, inside the same object).
    fn mpz_bytes(&self, o: &Obj<'a>) -> Result<(bool, Vec<u32>), Fail> {
        let b = o.bytes;
        if self.gmp {
            // mpz_object: header, then __mpz_struct { int _mp_alloc;
            // int _mp_size; mp_limb_t *_mp_d }.
            let size = i32::from_le_bytes(b[12..16].try_into().expect("4"));
            let d = rd64(b, 16).expect("24 bytes");
            let n = size.unsigned_abs() as usize;
            let want = o.addr + 24;
            if d != want || 24 + 8 * n > b.len() {
                return Err(Fail::malformed("malformed big number"));
            }
            let mut digits = Vec::with_capacity(2 * n);
            for i in 0..n {
                let l = rd64(b, 24 + 8 * i).expect("in bounds");
                digits.push(l as u32);
                digits.push((l >> 32) as u32);
            }
            Ok((size < 0, digits))
        } else {
            // Lean's own mpz: { bool m_sign; size_t m_size; unsigned *m_digits }.
            let sign = b[8];
            let n = rd64(b, 16).expect("24 bytes");
            if b.len() < 32 || sign > 1 {
                return Err(Fail::malformed("malformed big number"));
            }
            let d = rd64(b, 24).expect("32 bytes");
            let n = usize::try_from(n).map_err(|_| Fail::malformed("malformed big number"))?;
            match n.checked_mul(4).and_then(|x| x.checked_add(32)) {
                Some(end) if d == o.addr + 32 && end <= b.len() => {}
                _ => return Err(Fail::malformed("malformed big number")),
            }
            let digits = (0..n)
                .map(|i| u32::from_le_bytes(b[32 + 4 * i..36 + 4 * i].try_into().expect("4")))
                .collect();
            Ok((sign == 1, digits))
        }
    }

    /// A `Nat`: a boxed scalar, or a non-negative big number object, as
    /// little-endian 32-bit digits.
    pub fn nat(&self, v: Val<'a>) -> Result<NatVal, Fail> {
        match v {
            Val::Scalar(n) => Ok(NatVal::Small(n)),
            Val::Obj(o) if o.tag == TAG_MPZ => {
                let (neg, digits) = self.mpz_bytes(&o)?;
                if neg {
                    return Err(Fail::malformed("negative natural number"));
                }
                Ok(NatVal::Big(digits))
            }
            Val::Obj(_) => Err(Fail::malformed("expected a natural number")),
        }
    }
}

pub enum NatVal {
    Small(u64),
    Big(Vec<u32>),
}

impl<'a> Obj<'a> {
    /// Check that this is a constructor with tag `tag`, `nobjs` object
    /// fields and at least `scalars` bytes of scalar fields.
    pub fn ctor(&self, tag: u8, nobjs: u8, scalars: usize, what: &str) -> Result<(), Fail> {
        if self.tag != tag
            || self.other != nobjs
            || self.bytes.len() < 8 + 8 * nobjs as usize + scalars
        {
            return Err(Fail::malformed(format!(
                "malformed {what} at {:#x} (tag {}, {} fields)",
                self.addr, self.tag, self.other
            )));
        }
        Ok(())
    }

    /// The raw word of object field `i`. Callers have checked the shape.
    pub fn field(&self, i: usize) -> u64 {
        rd64(self.bytes, 8 + 8 * i).expect("field in bounds")
    }

    fn scalar_off(&self, off: usize) -> usize {
        8 + 8 * self.other as usize + off
    }

    pub fn u8_at(&self, off: usize) -> Result<u8, Fail> {
        self.bytes
            .get(self.scalar_off(off))
            .copied()
            .ok_or_else(|| Fail::malformed("scalar field out of bounds"))
    }

    pub fn bool_at(&self, off: usize) -> Result<bool, Fail> {
        match self.u8_at(off)? {
            0 => Ok(false),
            1 => Ok(true),
            b => Err(Fail::malformed(format!("bad Bool value {b}"))),
        }
    }

    pub fn u32_at(&self, off: usize) -> Result<u32, Fail> {
        let o = self.scalar_off(off);
        match self.bytes.get(o..o + 4) {
            Some(s) => Ok(u32::from_le_bytes(s.try_into().expect("4"))),
            None => Err(Fail::malformed("scalar field out of bounds")),
        }
    }

    /// The elements of an `Array`.
    pub fn array(&self) -> Result<impl Iterator<Item = u64> + 'a, Fail> {
        if self.tag != TAG_ARRAY {
            return Err(Fail::malformed(format!(
                "expected an array at {:#x}",
                self.addr
            )));
        }
        let b = self.bytes;
        Ok((24..b.len())
            .step_by(8)
            .map(move |o| rd64(b, o).expect("in bounds")))
    }

    /// The text of a `String`: `m_size` counts the terminating NUL.
    pub fn string(&self) -> Result<&'a str, Fail> {
        if self.tag != TAG_STRING {
            return Err(Fail::malformed(format!(
                "expected a string at {:#x}",
                self.addr
            )));
        }
        let b = &self.bytes[32..];
        match b.split_last() {
            Some((0, s)) => {
                std::str::from_utf8(s).map_err(|_| Fail::malformed("string is not UTF-8"))
            }
            _ => Err(Fail::malformed("string is not NUL-terminated")),
        }
    }
}
