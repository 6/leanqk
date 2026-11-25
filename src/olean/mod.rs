//! Loading Lean's compiled `.olean` files directly, without an export step.
//!
//! [`load`] takes a module name, an `.olean` file or a Lake project, finds
//! the import closure, and loads every module once, in import order, into
//! the same [`Env`] the NDJSON reader builds. Modules are decoded in
//! parallel ([`decode`]); the decoded modules are interned into the shared
//! arenas in import order ([`build`]).
//!
//! The format is documented in `docs/olean-format.md`. Files are untrusted:
//! every pointer is bounds-checked, and malformed input is an error, never
//! a crash.

use std::collections::HashMap;
use std::fmt;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::mpsc;
use std::time::{Duration, Instant};

use crate::env::Env;
use crate::name::NameId;
use crate::reader::ErrorClass;

mod build;
mod decode;
mod file;
mod lazy;
mod obj;
mod par;

pub use file::LEAN_VERSION;

use decode::{Decoder, Tape};
use file::OleanFile;
use obj::Heap;
use par::Par;

/// An error without its file.
#[derive(Debug)]
pub(crate) struct Fail {
    pub class: ErrorClass,
    pub msg: String,
}

impl Fail {
    pub fn malformed(msg: impl Into<String>) -> Fail {
        Fail {
            class: ErrorClass::Malformed,
            msg: msg.into(),
        }
    }

    pub fn unsupported(msg: impl Into<String>) -> Fail {
        Fail {
            class: ErrorClass::Unsupported,
            msg: msg.into(),
        }
    }

    pub fn at(self, path: &Path) -> OleanError {
        OleanError {
            class: self.class,
            path: path.to_path_buf(),
            msg: self.msg,
        }
    }
}

/// Why loading failed, and in which file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OleanError {
    pub class: ErrorClass,
    /// The file (or project, or module) the error is about; empty if none.
    pub path: PathBuf,
    pub msg: String,
}

impl fmt::Display for OleanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.path.as_os_str().is_empty() {
            f.write_str(&self.msg)
        } else {
            write!(f, "{}: {}", self.path.display(), self.msg)
        }
    }
}

impl std::error::Error for OleanError {}

fn err(class: ErrorClass, path: &Path, msg: impl Into<String>) -> OleanError {
    OleanError {
        class,
        path: path.to_path_buf(),
        msg: msg.into(),
    }
}

/// Where to look for modules, and how many threads to use.
#[derive(Clone, Debug, Default)]
pub struct Options {
    /// Directories searched for `A/B/C.olean`, in order, before those of
    /// the project, `LEAN_PATH` and the Lean toolchain.
    pub search_path: Vec<PathBuf>,
    /// Decoding threads; 0 means one per available core.
    pub threads: usize,
    /// Don't ask `lean --print-libdir` for the toolchain's library.
    pub no_toolchain: bool,
    /// Root modules to load instead of the target's own (for a project
    /// target: modules of the project or its packages).
    pub modules: Vec<String>,
    /// Leave theorem values in their files (an experiment: the checker
    /// cannot use such an environment yet).
    pub lazy_proofs: bool,
}

/// Statistics of a load.
#[derive(Clone, Debug, Default)]
pub struct Stats {
    pub modules: usize,
    pub files: usize,
    pub bytes: u64,
    pub threads: usize,
    /// Finding and reading the import closure.
    pub imports_time: Duration,
    /// Decoding and interning the modules (wall clock).
    pub load_time: Duration,
    /// Time spent appending declarations in import order.
    pub intern_time: Duration,
    /// Time spent moving the concurrent arenas into the environment.
    pub finish_time: Duration,
}

/// A module to load: its name and the path of its main `.olean`.
struct Module {
    name: String,
    path: PathBuf,
    /// Whether it uses the module system (has `.server` and `.private`
    /// parts); known once its main part has been read.
    is_module: bool,
}

/// Load `target` and its import closure. `target` is a Lake project
/// directory (all modules it built), an `.olean` file, or a module name.
pub fn load(target: &str, opts: &Options) -> Result<(Env, Stats), OleanError> {
    let threads = match opts.threads {
        0 => std::thread::available_parallelism().map_or(1, |n| n.get()),
        n => n,
    };
    let imports_start = Instant::now();
    let (roots, search) = resolve_target(target, opts)?;
    let mods = import_closure(&roots, &search, threads)?;
    let imports_time = imports_start.elapsed();
    let load_start = Instant::now();
    let (env, mut stats) = load_modules(&mods, threads, opts.lazy_proofs)?;
    stats.imports_time = imports_time;
    stats.load_time = load_start.elapsed();
    stats.threads = threads;
    Ok((env, stats))
}

/// Root modules (name, main file) and the search path.
fn resolve_target(target: &str, opts: &Options) -> Result<(Vec<Module>, Vec<PathBuf>), OleanError> {
    let p = Path::new(target);
    let mut search = opts.search_path.clone();
    let mut roots = Vec::new();
    let mut toolchain_dir: Option<PathBuf> = None;
    if p.is_dir() {
        let is_project = ["lakefile.lean", "lakefile.toml"]
            .iter()
            .any(|f| p.join(f).is_file());
        if !is_project {
            return Err(err(
                ErrorClass::Io,
                p,
                "a directory target must be a Lake project (with a lakefile)",
            ));
        }
        let lib = p.join(".lake/build/lib/lean");
        if !lib.is_dir() {
            return Err(err(
                ErrorClass::Io,
                p,
                "no build output in .lake/build/lib/lean (run `lake build` first)",
            ));
        }
        search.push(lib.clone());
        if let Ok(rd) = std::fs::read_dir(p.join(".lake/packages")) {
            let mut pkgs: Vec<PathBuf> = rd
                .filter_map(|e| e.ok())
                .map(|e| e.path().join(".lake/build/lib/lean"))
                .filter(|d| d.is_dir())
                .collect();
            pkgs.sort();
            search.extend(pkgs);
        }
        // The library roots: the modules at the top of the build directory
        // (`Mathlib` for Mathlib), else every module built. A project may
        // build libraries that are never imported together (Mathlib's
        // `Cache` tool redefines constants of `Mathlib`), so not every
        // module is a root.
        if opts.modules.is_empty() {
            let mut found = Vec::new();
            collect_modules(&lib, &lib, false, &mut found)
                .map_err(|e| err(ErrorClass::Io, &lib, e.to_string()))?;
            if found.is_empty() {
                collect_modules(&lib, &lib, true, &mut found)
                    .map_err(|e| err(ErrorClass::Io, &lib, e.to_string()))?;
            }
            found.sort();
            for (name, path) in found {
                roots.push(Module {
                    name,
                    path,
                    is_module: false,
                });
            }
            if roots.is_empty() {
                return Err(err(ErrorClass::Io, &lib, "no .olean files"));
            }
        }
        toolchain_dir = Some(p.to_path_buf());
    } else if target.ends_with(".olean") {
        if !p.is_file() {
            return Err(err(ErrorClass::Io, p, "no such file"));
        }
        let name = p
            .file_stem()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_default();
        roots.push(Module {
            name,
            path: p.to_path_buf(),
            is_module: false,
        });
    }
    if let Some(lp) = std::env::var_os("LEAN_PATH") {
        search.extend(std::env::split_paths(&lp).filter(|d| !d.as_os_str().is_empty()));
    }
    if !opts.no_toolchain
        && let Some(d) = toolchain_libdir(toolchain_dir.as_deref())
    {
        search.push(d);
    }
    let wanted: Vec<&str> = if !opts.modules.is_empty() {
        opts.modules.iter().map(|s| s.as_str()).collect()
    } else if roots.is_empty() {
        vec![target]
    } else {
        vec![]
    };
    for m in wanted {
        let path = find_module(m, &search).ok_or_else(|| {
            err(
                ErrorClass::Io,
                Path::new(""),
                format!("module {m} not found in the search path"),
            )
        })?;
        roots.push(Module {
            name: m.to_string(),
            path,
            is_module: false,
        });
    }
    Ok((roots, search))
}

/// The library directory of the Lean toolchain (`lean --print-libdir`, run
/// in `dir` so that elan picks the project's toolchain).
fn toolchain_libdir(dir: Option<&Path>) -> Option<PathBuf> {
    let mut c = std::process::Command::new("lean");
    c.arg("--print-libdir");
    if let Some(d) = dir {
        c.current_dir(d);
    }
    let out = c.stderr(std::process::Stdio::null()).output().ok()?;
    if !out.status.success() {
        return None;
    }
    let s = String::from_utf8(out.stdout).ok()?;
    let d = PathBuf::from(s.trim());
    d.is_dir().then_some(d)
}

fn collect_modules(
    root: &Path,
    dir: &Path,
    deep: bool,
    out: &mut Vec<(String, PathBuf)>,
) -> std::io::Result<()> {
    for e in std::fs::read_dir(dir)? {
        let e = e?;
        let path = e.path();
        let ft = e.file_type()?;
        if ft.is_dir() {
            if deep {
                collect_modules(root, &path, deep, out)?;
            }
        } else if path.extension().is_some_and(|x| x == "olean") {
            let rel = path
                .strip_prefix(root)
                .expect("under root")
                .with_extension("");
            let name: Vec<String> = rel
                .components()
                .map(|c| c.as_os_str().to_string_lossy().into_owned())
                .collect();
            out.push((name.join("."), path));
        }
    }
    Ok(())
}

/// `A.B.C` → `dir/A/B/C.olean` in the first directory that has it.
fn find_module(name: &str, search: &[PathBuf]) -> Option<PathBuf> {
    let mut rel = PathBuf::new();
    for c in name.split('.') {
        if c.is_empty() || c == ".." || c.contains(['/', '\\']) {
            return None;
        }
        rel.push(c);
    }
    rel.set_extension("olean");
    search.iter().map(|d| d.join(&rel)).find(|p| p.is_file())
}

/// The dotted form of a name, with Lean's escaping of components that are
/// not plain identifiers left out (module names are plain).
fn dotted(t: &Tape, n: NameId) -> String {
    use crate::name::NameNode;
    let mut parts = Vec::new();
    let mut cur = n;
    loop {
        match t.names[cur.index()] {
            NameNode::Anon => break,
            NameNode::Str(p, s) => {
                parts.push(t.str(s).to_string());
                cur = p;
            }
            NameNode::Num(p, k) => {
                parts.push(k.to_string());
                cur = p;
            }
        }
    }
    parts.reverse();
    parts.join(".")
}

/// A module's direct imports (dotted names) and whether it uses the
/// module system, from its main part.
fn read_imports(path: &Path) -> Result<(Vec<String>, bool), OleanError> {
    let f = OleanFile::open(path)?;
    let heap = Heap::new(&[&f]).map_err(|e| e.at(path))?;
    let mut d = Decoder::new(&heap);
    d.module(f.root(), true, false).map_err(|e| e.at(path))?;
    let t = d.finish();
    Ok((
        t.imports.iter().map(|&n| dotted(&t, n)).collect(),
        t.is_module,
    ))
}

/// The import closure of `roots`, each module after its imports. The
/// modules' headers are read on `threads` threads.
fn import_closure(
    roots: &[Module],
    search: &[PathBuf],
    threads: usize,
) -> Result<Vec<Module>, OleanError> {
    struct State {
        index: HashMap<String, usize>,
        mods: Vec<Module>,
        imports: Vec<Vec<usize>>,
        todo: Vec<usize>,
        busy: usize,
        error: Option<OleanError>,
    }
    let mut st = State {
        index: HashMap::new(),
        mods: Vec::new(),
        imports: Vec::new(),
        todo: Vec::new(),
        busy: 0,
        error: None,
    };
    for r in roots {
        if !st.index.contains_key(&r.name) {
            st.index.insert(r.name.clone(), st.mods.len());
            st.todo.push(st.mods.len());
            st.mods.push(Module {
                name: r.name.clone(),
                path: r.path.clone(),
                is_module: false,
            });
            st.imports.push(Vec::new());
        }
    }
    let state = std::sync::Mutex::new(st);
    let wake = std::sync::Condvar::new();
    let worker = || {
        let mut guard = state.lock().expect("lock");
        loop {
            if guard.error.is_some() {
                break;
            }
            let Some(i) = guard.todo.pop() else {
                if guard.busy == 0 {
                    break;
                }
                guard = wake.wait(guard).expect("lock");
                continue;
            };
            guard.busy += 1;
            let path = guard.mods[i].path.clone();
            drop(guard);
            let res = read_imports(&path);
            guard = state.lock().expect("lock");
            guard.busy -= 1;
            let (names, is_module) = match res {
                Ok(x) => x,
                Err(e) => {
                    guard.error.get_or_insert(e);
                    wake.notify_all();
                    break;
                }
            };
            guard.mods[i].is_module = is_module;
            let mut deps = Vec::with_capacity(names.len());
            for name in names {
                let j = match guard.index.get(&name) {
                    Some(&j) => j,
                    None => {
                        let Some(p) = find_module(&name, search) else {
                            guard.error.get_or_insert(err(
                                ErrorClass::Io,
                                &path,
                                format!("imported module {name} not found in the search path"),
                            ));
                            break;
                        };
                        let st = &mut *guard;
                        let j = st.mods.len();
                        st.index.insert(name.clone(), j);
                        st.mods.push(Module {
                            name,
                            path: p,
                            is_module: false,
                        });
                        st.imports.push(Vec::new());
                        st.todo.push(j);
                        j
                    }
                };
                deps.push(j);
            }
            guard.imports[i] = deps;
            wake.notify_all();
        }
        wake.notify_all();
    };
    if threads <= 1 {
        worker();
    } else {
        std::thread::scope(|s| {
            for _ in 0..threads {
                s.spawn(worker);
            }
        });
    }
    let st = state.into_inner().expect("lock");
    if let Some(e) = st.error {
        return Err(e);
    }
    let State { mods, imports, .. } = st;
    // Post-order DFS, with an explicit stack; a cycle is an error.
    let mut state = vec![0u8; mods.len()];
    let mut order = Vec::with_capacity(mods.len());
    for r in 0..roots.len().min(mods.len()) {
        if state[r] != 0 {
            continue;
        }
        let mut stack = vec![(r, 0usize)];
        state[r] = 1;
        while let Some((m, k)) = stack.last_mut() {
            let m = *m;
            if *k < imports[m].len() {
                let j = imports[m][*k];
                *k += 1;
                match state[j] {
                    0 => {
                        state[j] = 1;
                        stack.push((j, 0));
                    }
                    1 => {
                        return Err(err(
                            ErrorClass::Malformed,
                            &mods[m].path,
                            format!("import cycle through {}", mods[j].name),
                        ));
                    }
                    _ => {}
                }
            } else {
                state[m] = 2;
                order.push(m);
                stack.pop();
            }
        }
    }
    let mut slots: Vec<Option<Module>> = mods.into_iter().map(Some).collect();
    Ok(order
        .into_iter()
        .map(|i| slots[i].take().expect("once"))
        .collect())
}

/// The part files of a module: the `.olean`, and for a module-system
/// module its `.olean.server` and `.olean.private`, which may point into
/// the parts before them (`readModuleDataPartsOfMod` in
/// `src/Lean/Environment.lean`).
fn open_parts(m: &Module) -> Result<Vec<OleanFile>, OleanError> {
    let mut parts = vec![OleanFile::open(&m.path)?];
    if m.is_module {
        for ext in ["olean.server", "olean.private"] {
            parts.push(OleanFile::open(&m.path.with_extension(ext))?);
        }
    }
    Ok(parts)
}

/// Decode one module: the constants of its last part (the private part of
/// a module-system module holds all of them).
fn decode_module(m: &Module, lazy: bool) -> Result<(Tape, Vec<OleanFile>, u64), OleanError> {
    let parts = open_parts(m)?;
    let last = parts.last().expect("a part");
    let refs: Vec<&OleanFile> = parts.iter().collect();
    let heap = Heap::new(&refs).map_err(|e| e.at(&last.path))?;
    let mut d = Decoder::new(&heap);
    d.lazy_proofs = lazy;
    d.module(last.root(), false, true)
        .map_err(|e| e.at(&last.path))?;
    let bytes = parts.iter().map(|p| p.len() as u64).sum();
    let tape = d.finish();
    drop(heap);
    Ok((tape, parts, bytes))
}

fn new_env() -> Env {
    let mut env = Env::new();
    env.meta.format_version = "olean".into();
    env.meta.lean_version = Some(LEAN_VERSION.into());
    env
}

/// What a worker makes of a module: its declarations, its files if it
/// has lazily read values, its number of files and their size.
type Done = Result<(build::ModOut, Option<Vec<OleanFile>>, usize, u64), OleanError>;

/// Nanoseconds spent decoding and interning, over all threads (for
/// `NITROLEAN_OLEAN_PROFILE`).
static DECODE_NS: AtomicU64 = AtomicU64::new(0);
static INTERN_NS: AtomicU64 = AtomicU64::new(0);
static TAPE_EXPRS: AtomicU64 = AtomicU64::new(0);
static TAPE_NAMES: AtomicU64 = AtomicU64::new(0);

fn work(par: &Par, loc: &mut par::Local, m: &Module, lazy: bool) -> Done {
    let t = Instant::now();
    let (tape, parts, bytes) = decode_module(m, lazy)?;
    let d = t.elapsed();
    let files = parts.len();
    let keep = (!tape.lazy.is_empty()).then(|| {
        for p in &parts {
            p.release();
        }
        parts
    });
    TAPE_EXPRS.fetch_add(tape.exprs.len() as u64, Ordering::Relaxed);
    TAPE_NAMES.fetch_add(tape.names.len() as u64, Ordering::Relaxed);
    let out = build::intern_module(par, loc, &tape).map_err(|e| e.at(&m.path))?;
    DECODE_NS.fetch_add(d.as_nanos() as u64, Ordering::Relaxed);
    INTERN_NS.fetch_add((t.elapsed() - d).as_nanos() as u64, Ordering::Relaxed);
    Ok((out, keep, files, bytes))
}

/// Load `mods` (in import order) with `threads` workers. Workers decode
/// and intern whole modules, any number at once, into the concurrent
/// arenas; this thread appends their declarations in import order.
fn load_modules(mods: &[Module], threads: usize, lazy: bool) -> Result<(Env, Stats), OleanError> {
    // The parts' sizes, to size the arenas.
    let bytes: u64 = mods
        .iter()
        .flat_map(|m| {
            ["olean", "olean.server", "olean.private"]
                .map(|e| std::fs::metadata(m.path.with_extension(e)).map_or(0, |md| md.len()))
        })
        .sum();
    let par = Par::new(bytes, threads);
    let mut asm = build::Assembler::new(new_env(), &par);
    let mut stats = Stats {
        modules: mods.len(),
        ..Stats::default()
    };
    let names = |i: u32| mods[i as usize].name.clone();
    let mut intern = Duration::ZERO;
    let mut kept: Vec<Option<Vec<OleanFile>>> = Vec::new();
    let mut add = |asm: &mut build::Assembler<'_>, i: usize, r: Done| {
        let (out, keep, files, bytes) = r?;
        if keep.is_some() {
            kept.resize_with(i + 1, || None);
            kept[i] = keep;
        }
        stats.files += files;
        stats.bytes += bytes;
        let t = Instant::now();
        asm.add(&out, i as u32, &names)
            .map_err(|e| e.at(&mods[i].path))?;
        intern += t.elapsed();
        Ok::<(), OleanError>(())
    };
    if threads <= 1 {
        let mut loc = par::Local::default();
        for (i, m) in mods.iter().enumerate() {
            add(&mut asm, i, work(&par, &mut loc, m, lazy))?;
        }
    } else {
        let next = AtomicUsize::new(0);
        let failed = std::sync::atomic::AtomicBool::new(false);
        std::thread::scope(|s| {
            let (tx, rx) = mpsc::channel::<(usize, Done)>();
            for _ in 0..threads {
                let tx = tx.clone();
                let (next, failed, par) = (&next, &failed, &par);
                s.spawn(move || {
                    let mut loc = par::Local::default();
                    loop {
                        let i = next.fetch_add(1, Ordering::Relaxed);
                        if i >= mods.len() || failed.load(Ordering::Relaxed) {
                            break;
                        }
                        if tx.send((i, work(par, &mut loc, &mods[i], lazy))).is_err() {
                            break;
                        }
                    }
                });
            }
            drop(tx);
            let mut pending = HashMap::new();
            let mut want = 0;
            let out = (|| {
                for (i, r) in rx.iter() {
                    pending.insert(i, r);
                    while let Some(r) = pending.remove(&want) {
                        add(&mut asm, want, r)?;
                        want += 1;
                    }
                }
                Ok(())
            })();
            if out.is_err() {
                failed.store(true, Ordering::Relaxed);
            }
            out
        })?;
    }
    let t = Instant::now();
    if std::env::var_os("NITROLEAN_OLEAN_PROFILE").is_some() {
        eprintln!(
            "rss before finish: {:?} MiB, peak {:?}; decode {:.3} s, intern {:.3} s (all threads); module-local expressions {}, names {}",
            rss_now(),
            crate::stats::peak_rss_bytes(),
            DECODE_NS.load(Ordering::Relaxed) as f64 / 1e9,
            INTERN_NS.load(Ordering::Relaxed) as f64 / 1e9,
            TAPE_EXPRS.load(Ordering::Relaxed),
            TAPE_NAMES.load(Ordering::Relaxed),
        );
    }
    let build::Assembler {
        mut env, handles, ..
    } = asm;
    drop(add);
    if !handles.is_empty() {
        env.lazy = Some(Box::new(lazy::OleanValues {
            modules: kept,
            handles,
        }));
    }
    let (names, levels, exprs) = par.finish(threads).map_err(|o| {
        err(
            ErrorClass::Malformed,
            Path::new(""),
            format!("capacity exceeded: {}", o.0),
        )
    })?;
    env.names = names;
    env.names.strings.enable_late();
    env.levels = levels;
    env.exprs = exprs;
    stats.finish_time = t.elapsed();
    if std::env::var_os("NITROLEAN_OLEAN_PROFILE").is_some() {
        eprintln!(
            "rss after finish: {:?} peak {:?}",
            rss_now(),
            crate::stats::peak_rss_bytes()
        );
    }
    stats.intern_time = intern;
    Ok((env, stats))
}

fn rss_now() -> Option<u64> {
    let s = std::fs::read_to_string("/proc/self/status").ok()?;
    let l = s.lines().find(|l| l.starts_with("VmRSS:"))?;
    l.split_whitespace()
        .nth(1)?
        .parse::<u64>()
        .ok()
        .map(|k| k / 1024)
}

#[cfg(test)]
mod tests;
