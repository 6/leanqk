//! Opening an `.olean` file: the memory map and the fixed header.
//!
//! The layout is documented in `docs/olean-format.md`. This is the only
//! module of the crate with `unsafe` code: the memory map itself. Everything
//! read from the map goes through bounds-checked slices.

use std::fs::File;
use std::path::{Path, PathBuf};

use memmap2::Mmap;

use super::{Fail, OleanError};
use crate::reader::ErrorClass;

/// The Lean release whose object layout this reader knows.
pub const LEAN_VERSION: &str = "4.36.0";

/// Size of the fixed header: marker, version, flags, Lean version, githash
/// and base address.
pub const HEADER_LEN: usize = 5 + 1 + 1 + 33 + 40 + 8;

/// The bytes of a file: memory-mapped, or (for empty files, which cannot
/// be mapped) an empty slice.
enum Bytes {
    Map(Mmap),
    Empty,
}

/// An opened `.olean` file (one part of a module).
pub struct OleanFile {
    pub path: PathBuf,
    bytes: Bytes,
    /// Header format version: 2, or 3 for files with closures.
    pub version: u8,
    /// Whether big numbers use GMP's limb layout (header flag bit 0).
    pub gmp: bool,
    pub lean_version: String,
    pub githash: String,
    /// The logical address of the first byte of the file; pointers in the
    /// file are logical addresses.
    pub base: u64,
    /// File offset of the compacted data (the root slot is its first word).
    pub data_off: usize,
    /// Length of the compacted data in bytes.
    pub data_len: usize,
}

impl OleanFile {
    #[allow(unsafe_code)]
    pub fn open(path: &Path) -> Result<OleanFile, OleanError> {
        let io = |e: std::io::Error| OleanError {
            class: ErrorClass::Io,
            path: path.to_path_buf(),
            msg: e.to_string(),
        };
        let f = File::open(path).map_err(io)?;
        let len = f.metadata().map_err(io)?.len();
        let bytes = if len == 0 {
            Bytes::Empty
        } else {
            // SAFETY: the map is read-only and private. Lean writes `.olean`
            // files to a temporary name and renames them into place, so a
            // file is never modified once it has this name; if another
            // program truncates it anyway, reads past the new end fault
            // (SIGBUS), they cannot return wrong bytes silently. No
            // reference into the map outlives `OleanFile`.
            let m = unsafe { Mmap::map(&f) }.map_err(io)?;
            Bytes::Map(m)
        };
        let mut file = OleanFile {
            path: path.to_path_buf(),
            bytes,
            version: 0,
            gmp: false,
            lean_version: String::new(),
            githash: String::new(),
            base: 0,
            data_off: 0,
            data_len: 0,
        };
        file.parse_header().map_err(|f| f.at(path))?;
        Ok(file)
    }

    pub fn bytes(&self) -> &[u8] {
        match &self.bytes {
            Bytes::Map(m) => m,
            Bytes::Empty => &[],
        }
    }

    /// Drop the file's pages from this process's memory (they stay in the
    /// page cache, and are read back from there if the file is read
    /// again). Used for files kept open after loading, for their lazily
    /// read values, so that they do not count in the process's memory.
    #[allow(unsafe_code)]
    pub fn release(&self) {
        if let Bytes::Map(m) = &self.bytes {
            // SAFETY: the map is private, read-only and backed by a file
            // that is never modified (see `open`): after `MADV_DONTNEED`
            // its pages read back the same bytes from the file, so no
            // reference into the map sees different contents.
            let _ = unsafe { m.unchecked_advise(memmap2::UncheckedAdvice::DontNeed) };
        }
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.bytes().len()
    }

    fn parse_header(&mut self) -> Result<(), Fail> {
        let b = self.bytes();
        if b.len() < HEADER_LEN || &b[..5] != b"olean" {
            return Err(Fail::malformed("not an .olean file (bad header)"));
        }
        let version = b[5];
        let flags = b[6];
        let text = |s: &[u8]| {
            let end = s.iter().position(|&c| c == 0).unwrap_or(s.len());
            String::from_utf8_lossy(&s[..end]).into_owned()
        };
        let lean_version = text(&b[7..40]);
        let githash = text(&b[40..80]);
        let base = u64::from_le_bytes(b[80..88].try_into().expect("8 bytes"));
        if version != 2 && version != 3 {
            return Err(Fail::unsupported(format!(
                "unsupported .olean header version {version} (this reader knows 2 and 3)"
            )));
        }
        if flags & !1 != 0 {
            return Err(Fail::unsupported(format!(
                "unknown .olean header flags {flags:#04x}"
            )));
        }
        if lean_version != LEAN_VERSION {
            return Err(Fail::unsupported(format!(
                "written by Lean {lean_version}; this reader supports the object layout of Lean {LEAN_VERSION}"
            )));
        }
        if !base.is_multiple_of(8) {
            return Err(Fail::malformed("misaligned base address"));
        }
        let (data_off, data_len) = if version == 2 {
            (HEADER_LEN, b.len() - HEADER_LEN)
        } else {
            if b.len() < HEADER_LEN + 8 {
                return Err(Fail::malformed("truncated header"));
            }
            let n = u64::from_le_bytes(b[HEADER_LEN..HEADER_LEN + 8].try_into().expect("8"));
            let off = HEADER_LEN + 8;
            match usize::try_from(n) {
                Ok(n) if n <= b.len() - off => (off, n),
                _ => return Err(Fail::malformed("data size exceeds the file")),
            }
        };
        if data_len < 8 {
            return Err(Fail::malformed("no root object"));
        }
        if base.checked_add(b.len() as u64).is_none() {
            return Err(Fail::malformed("base address out of range"));
        }
        self.version = version;
        self.gmp = flags & 1 != 0;
        self.lean_version = lean_version;
        self.githash = githash;
        self.base = base;
        self.data_off = data_off;
        self.data_len = data_len;
        Ok(())
    }

    /// The logical address in the root slot.
    pub fn root(&self) -> u64 {
        let o = self.data_off;
        u64::from_le_bytes(self.bytes()[o..o + 8].try_into().expect("8 bytes"))
    }
}
