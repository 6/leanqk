//! Tests of the `.olean` reader on files written here, following
//! `docs/olean-format.md`: a small valid module, targeted malformations,
//! and every truncation and many corruptions of it, none of which may
//! panic.

use std::path::{Path, PathBuf};

use super::{Options, load};
use crate::env::DeclKind;
use crate::reader::ErrorClass;

/// Writes compacted objects into an `.olean` image.
struct W {
    buf: Vec<u8>,
    base: u64,
    version_str: &'static str,
}

const BASE: u64 = 0x1234_5600_0000;

impl W {
    fn new() -> Self {
        let mut w = W {
            buf: vec![0; super::file::HEADER_LEN],
            base: BASE,
            version_str: "4.36.0",
        };
        w.buf.extend_from_slice(&[0; 8]); // root slot
        w
    }

    fn addr(&self) -> u64 {
        self.base + self.buf.len() as u64
    }

    fn header(&mut self, tag: u8, other: u8, cs: u16) {
        self.buf.extend_from_slice(&0i32.to_le_bytes());
        self.buf.extend_from_slice(&cs.to_le_bytes());
        self.buf.push(other);
        self.buf.push(tag);
    }

    /// A constructor with pointer fields and scalar bytes (padded to 8).
    fn ctor(&mut self, tag: u8, ptrs: &[u64], scalars: &[u8]) -> u64 {
        let a = self.addr();
        let sc = scalars.len().div_ceil(8) * 8;
        let size = 8 + 8 * ptrs.len() + sc;
        self.header(tag, ptrs.len() as u8, size as u16);
        for p in ptrs {
            self.buf.extend_from_slice(&p.to_le_bytes());
        }
        self.buf.extend_from_slice(scalars);
        self.buf.resize(self.buf.len() + sc - scalars.len(), 0);
        a
    }

    fn string(&mut self, s: &str) -> u64 {
        let a = self.addr();
        self.header(249, 0, 1);
        let n = s.len() as u64 + 1;
        for x in [n, n, s.chars().count() as u64] {
            self.buf.extend_from_slice(&x.to_le_bytes());
        }
        self.buf.extend_from_slice(s.as_bytes());
        self.buf.push(0);
        while !self.buf.len().is_multiple_of(8) {
            self.buf.push(0);
        }
        a
    }

    fn array(&mut self, ptrs: &[u64]) -> u64 {
        let a = self.addr();
        self.header(246, 0, 1);
        let n = ptrs.len() as u64;
        self.buf.extend_from_slice(&n.to_le_bytes());
        self.buf.extend_from_slice(&n.to_le_bytes());
        for p in ptrs {
            self.buf.extend_from_slice(&p.to_le_bytes());
        }
        a
    }

    fn name(&mut self, parts: &[&str]) -> u64 {
        let mut p = boxed(0);
        for s in parts {
            let s = self.string(s);
            p = self.ctor(1, &[p, s], &[0; 8]);
        }
        p
    }

    fn list(&mut self, xs: &[u64]) -> u64 {
        let mut l = boxed(0);
        for &x in xs.iter().rev() {
            l = self.ctor(1, &[x, l], &[]);
        }
        l
    }

    fn finish(mut self, root: u64) -> Vec<u8> {
        let h = super::file::HEADER_LEN;
        self.buf[..5].copy_from_slice(b"olean");
        self.buf[5] = 2;
        self.buf[6] = 1;
        let v = self.version_str.as_bytes();
        self.buf[7..7 + v.len()].copy_from_slice(v);
        self.buf[80..88].copy_from_slice(&self.base.to_le_bytes());
        self.buf[h..h + 8].copy_from_slice(&root.to_le_bytes());
        self.buf
    }
}

fn boxed(n: u64) -> u64 {
    n << 1 | 1
}

/// A module with `axiom Foo : Sort 1`, `def Bar : Sort 2 := Sort 1` and
/// `def Baz : Foo → Foo := fun x => x`.
fn sample() -> Vec<u8> {
    let mut w = W::new();
    let zero = w.ctor(0, &[], &[0; 8]);
    let one = w.ctor(1, &[zero], &[0; 8]);
    let two = w.ctor(1, &[one], &[0; 8]);
    let sort1 = w.ctor(3, &[one], &[0; 8]);
    let sort2 = w.ctor(3, &[two], &[0; 8]);
    let foo = w.name(&["Foo"]);
    let bar = w.name(&["Bar"]);
    let baz = w.name(&["Baz"]);
    let x = w.name(&["x"]);
    let c_foo = w.ctor(4, &[foo, boxed(0)], &[0; 8]);
    let arrow = w.ctor(7, &[x, c_foo, c_foo], &[0; 9]);
    let bv0 = w.ctor(0, &[boxed(0)], &[0; 8]);
    let mdata_kv = boxed(0);
    let body = w.ctor(10, &[mdata_kv, bv0], &[0; 8]);
    let lam = w.ctor(6, &[x, c_foo, body], &[0; 9]);
    let cv_foo = w.ctor(0, &[foo, boxed(0), sort1], &[]);
    let ax = w.ctor(0, &[cv_foo], &[0]);
    let ci_foo = w.ctor(0, &[ax], &[]);
    let regular = w.ctor(2, &[], &1u32.to_le_bytes());
    let cv_bar = w.ctor(0, &[bar, boxed(0), sort2], &[]);
    let all_bar = w.list(&[bar]);
    let dv_bar = w.ctor(0, &[cv_bar, sort1, regular, all_bar], &[1]);
    let ci_bar = w.ctor(1, &[dv_bar], &[]);
    let cv_baz = w.ctor(0, &[baz, boxed(0), arrow], &[]);
    let all_baz = w.list(&[baz]);
    let dv_baz = w.ctor(0, &[cv_baz, lam, boxed(1), all_baz], &[1]);
    let ci_baz = w.ctor(1, &[dv_baz], &[]);
    let imports = w.array(&[]);
    let names = w.array(&[baz, foo, bar]);
    // Hash-map order: Baz first, though it uses Foo.
    let consts = w.array(&[ci_baz, ci_foo, ci_bar]);
    let extra = w.array(&[]);
    let entries = w.array(&[]);
    let root = w.ctor(0, &[imports, names, consts, extra, entries], &[0]);
    w.finish(root)
}

fn write(dir: &Path, name: &str, bytes: &[u8]) -> PathBuf {
    let p = dir.join(name);
    std::fs::write(&p, bytes).expect("write test file");
    p
}

fn tmpdir(tag: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("nitrolean-olean-{tag}-{}", std::process::id()));
    std::fs::create_dir_all(&d).expect("temp dir");
    d
}

fn opts(threads: usize) -> Options {
    Options {
        threads,
        no_toolchain: true,
        ..Options::default()
    }
}

fn load_bytes(
    dir: &Path,
    bytes: &[u8],
    threads: usize,
) -> Result<crate::env::Env, super::OleanError> {
    let p = write(dir, "M.olean", bytes);
    load(p.to_str().expect("utf-8 path"), &opts(threads)).map(|(e, _)| e)
}

#[test]
fn loads_and_checks_a_small_module() {
    let d = tmpdir("ok");
    for threads in [1, 2] {
        let env = load_bytes(&d, &sample(), threads).expect("loads");
        assert_eq!(env.decls.len(), 3);
        // Sorted by dependency: Foo before Baz.
        let pos = |s| {
            env.decls
                .iter()
                .position(|x| env.names.display(x.name).to_string() == s)
        };
        assert!(pos("Foo") < pos("Baz"));
        let baz = env.find_dotted("Baz").expect("Baz");
        let DeclKind::Definition { value, .. } = baz.kind else {
            panic!("Baz is a definition")
        };
        // The mdata around the bound variable is gone.
        let crate::expr::ExprNode::Lam(_, _, _, b) = env.exprs.get(value) else {
            panic!("a lambda")
        };
        assert_eq!(env.exprs.get(b), crate::expr::ExprNode::BVar(0));
        crate::check::check_env(&env).expect("accepted");
    }
}

#[test]
fn rejects_other_versions() {
    let d = tmpdir("ver");
    let mut b = sample();
    b[7..13].copy_from_slice(b"4.35.0");
    let e = load_bytes(&d, &b, 1).err().expect("error");
    assert_eq!(e.class, ErrorClass::Unsupported, "{e}");
    let mut b = sample();
    b[5] = 9;
    let e = load_bytes(&d, &b, 1).err().expect("error");
    assert_eq!(e.class, ErrorClass::Unsupported, "{e}");
    let e = load_bytes(&d, b"not an olean", 1).err().expect("error");
    assert_eq!(e.class, ErrorClass::Malformed, "{e}");
}

/// The offset of the first word holding `v` after the header.
fn find_word(b: &[u8], v: u64, from: usize) -> usize {
    (from..b.len() - 7)
        .step_by(8)
        .find(|&i| u64::from_le_bytes(b[i..i + 8].try_into().unwrap()) == v)
        .expect("word present")
}

#[test]
fn rejects_bad_pointers() {
    let d = tmpdir("ptr");
    let good = sample();
    let root = u64::from_le_bytes(good[88..96].try_into().unwrap());
    let consts_field = (root - BASE) as usize + 8 + 16;
    let consts = u64::from_le_bytes(good[consts_field..consts_field + 8].try_into().unwrap());
    for (what, v) in [
        ("misaligned", consts + 4),
        ("past the end", BASE + good.len() as u64 + 64),
        ("before the data", BASE + 8),
        ("into the header", BASE),
        ("upwards (a cycle)", root),
    ] {
        let mut b = good.clone();
        b[consts_field..consts_field + 8].copy_from_slice(&v.to_le_bytes());
        let e = load_bytes(&d, &b, 1)
            .err()
            .unwrap_or_else(|| panic!("{what}: accepted"));
        assert_eq!(e.class, ErrorClass::Malformed, "{what}: {e}");
    }
    // A constant array longer than the file.
    let mut b = good.clone();
    let a = (consts - BASE) as usize;
    b[a + 8..a + 16].copy_from_slice(&u64::MAX.to_le_bytes());
    assert!(load_bytes(&d, &b, 1).is_err());
    // A string that is not NUL-terminated.
    let mut b = good.clone();
    let s = find_word(&b, 4, 96) - 8; // the "Foo" string object: size 4
    b[s + 32 + 3] = b'!';
    assert!(load_bytes(&d, &b, 1).is_err());
    // A free variable in a type.
    let mut b = good.clone();
    let sort1 = b
        .windows(8)
        .position(|w| w == [0, 0, 0, 0, 24, 0, 1, 3])
        .expect("a sort object");
    b[sort1 + 7] = 1;
    let e = load_bytes(&d, &b, 1).err().expect("error");
    assert!(e.msg.contains("free variable"), "{e}");
}

#[test]
fn rejects_duplicate_constants() {
    // Two parts can't be written here, but two modules can: M imports N,
    // and both declare Foo.
    let d = tmpdir("dup");
    let n = sample();
    write(&d, "N.olean", &n);
    let mut w = W::new();
    w.base = BASE + 0x100_0000;
    let nn = w.name(&["N"]);
    let imp = w.ctor(0, &[nn], &[0, 1, 0]);
    let zero = w.ctor(0, &[], &[0; 8]);
    let one = w.ctor(1, &[zero], &[0; 8]);
    let sort1 = w.ctor(3, &[one], &[0; 8]);
    let foo = w.name(&["Foo"]);
    let cv = w.ctor(0, &[foo, boxed(0), sort1], &[]);
    let ax = w.ctor(0, &[cv], &[0]);
    let ci = w.ctor(0, &[ax], &[]);
    let imports = w.array(&[imp]);
    let names = w.array(&[foo]);
    let consts = w.array(&[ci]);
    let extra_names = w.array(&[]);
    let entries = w.array(&[]);
    let root = w.ctor(0, &[imports, names, consts, extra_names, entries], &[0]);
    let m = w.finish(root);
    let p = write(&d, "M.olean", &m);
    let o = Options {
        search_path: vec![d.clone()],
        ..opts(2)
    };
    let e = load(p.to_str().unwrap(), &o).err().expect("duplicate");
    assert_eq!(e.class, ErrorClass::Rejected, "{e}");
    assert!(e.msg.contains("declared twice"), "{e}");
}

/// Every truncation, and every byte of the data overwritten with a few
/// values: each load must end in a value or an error, never a panic.
#[test]
fn corrupt_files_never_panic() {
    let d = tmpdir("fuzz");
    let good = sample();
    for len in 0..good.len() {
        let _ = load_bytes(&d, &good[..len], 1);
    }
    for i in 0..good.len() {
        for v in [0x00, 0x01, 0xff] {
            if good[i] == v {
                continue;
            }
            let mut b = good.clone();
            b[i] = v;
            if let Ok(env) = load_bytes(&d, &b, 1) {
                // Whatever loads must be usable by the checker.
                let _ = crate::check::check_env(&env);
            }
        }
    }
}

/// The same on a real module, if a Lean v4.36.0 library is at
/// `NITROLEAN_LEAN_LIB` (its `lib/lean` directory).
#[test]
fn corrupt_real_files_never_panic() {
    let Some(lib) = std::env::var_os("NITROLEAN_LEAN_LIB") else {
        return;
    };
    let parts = ["olean", "olean.server", "olean.private"];
    let src = Path::new(&lib).join("Init/Prelude.olean");
    let Ok(good) = parts
        .iter()
        .map(|e| std::fs::read(src.with_extension(e)))
        .collect::<Result<Vec<_>, _>>()
    else {
        return;
    };
    let d = tmpdir("real");
    let put = |bs: &[Vec<u8>]| {
        for (e, b) in parts.iter().zip(bs) {
            write(&d, &format!("M.{e}"), b);
        }
        load(d.join("M.olean").to_str().unwrap(), &opts(2)).map(|(e, _)| e)
    };
    let env = put(&good).expect("Init.Prelude loads");
    assert!(env.decls.len() > 1000);
    let mut x: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut next = || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    for _ in 0..300 {
        let mut bs = good.clone();
        let k = next() as usize % 3;
        for _ in 0..4 {
            let r = next();
            let n = bs[k].len();
            let i = 88 + (r as usize % (n - 88));
            bs[k][i] = (r >> 40) as u8;
        }
        let _ = put(&bs);
    }
}

/// Loading with theorem values left in their files gives the same
/// declarations in the same order, and each value decodes to the one read
/// at load time; on a real library, if `NITROLEAN_LEAN_LIB` is set.
#[test]
fn lazy_values_match_eager_ones() {
    let Some(lib) = std::env::var_os("NITROLEAN_LEAN_LIB") else {
        return;
    };
    let module = std::env::var("NITROLEAN_LEAN_MODULE").unwrap_or_else(|_| "Init".into());
    let o = |lazy| Options {
        threads: 2,
        no_toolchain: true,
        search_path: vec![PathBuf::from(&lib)],
        lazy_proofs: lazy,
        ..Options::default()
    };
    let (eager, _) = load(&module, &o(false)).expect("loads");
    let (lazy, _) = load(&module, &o(true)).expect("loads");
    assert!(lazy.lazy_values() > 0);
    // Later copies of a theorem are kept when their values are lazy (see
    // `build`): compare the declarations found by name, in order.
    let main = |e: &crate::env::Env| -> Vec<String> {
        e.decls
            .iter()
            .enumerate()
            .filter(|&(j, d)| e.by_name.get(&d.name) == Some(&(j as u32)))
            .map(|(_, d)| e.names.display(d.name).to_string())
            .collect()
    };
    assert_eq!(main(&eager), main(&lazy), "same declarations, same order");
    let mut decoded = 0;
    let mut back = crate::compare::Tr::new(&lazy, &eager);
    for (j, d) in lazy.decls.iter().enumerate() {
        if lazy.by_name.get(&d.name) != Some(&(j as u32)) {
            continue;
        }
        let DeclKind::Theorem { value, .. } = d.kind else {
            continue;
        };
        if !crate::env::is_lazy(value) {
            continue;
        }
        let e = eager
            .find_dotted(&lazy.names.display(d.name).to_string())
            .expect("in both");
        let DeclKind::Theorem { value: want, .. } = e.kind else {
            panic!("a theorem in both");
        };
        let mut sink = crate::compare::IntoEnv {
            a: &eager,
            b: &lazy,
            missing: false,
            back: &mut back,
        };
        let got = lazy.value_into(d, &mut sink).expect("decodes");
        assert!(
            !sink.missing && got == Some(want),
            "value of {}",
            lazy.names.display(d.name)
        );
        decoded += 1;
    }
    assert!(decoded > 1000);
}
