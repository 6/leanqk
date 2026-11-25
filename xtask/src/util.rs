//! Helpers shared by the commands: paths, logging, hashing, running programs,
//! TSV files, globs and parallel maps.

use std::collections::HashMap;
use std::ffi::OsStr;
use std::fs;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::sync::mpsc;
use std::time::{SystemTime, UNIX_EPOCH};

use anyhow::{Context, Result, anyhow, bail};
use sha2::{Digest, Sha256};

/// The root of the repository.
pub fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("xtask lives in the repository root")
        .to_path_buf()
}

/// The time of day in UTC as HH:MM:SS, as `date -u +%H:%M:%S` prints it.
pub fn utc_hms() -> String {
    let s = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
        % 86400;
    format!("{:02}:{:02}:{:02}", s / 3600, s / 60 % 60, s % 60)
}

/// Prints `HH:MM:SS TOOL: MESSAGE` on stderr.
pub fn log(tool: &str, msg: &str) {
    eprintln!("{} {tool}: {msg}", utc_hms());
}

/// An error that ends the command with exit status `code` after printing
/// its message (if not empty) on stderr.
#[derive(Debug)]
pub struct Exit {
    pub code: i32,
    pub msg: String,
}

impl std::fmt::Display for Exit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.msg)
    }
}

impl std::error::Error for Exit {}

/// Ends the command with status `code`, printing `msg` (if not empty).
pub fn exit_with(code: i32, msg: impl Into<String>) -> anyhow::Error {
    Exit {
        code,
        msg: msg.into(),
    }
    .into()
}

pub fn sha256_hex(data: &[u8]) -> String {
    hex(&Sha256::digest(data))
}

pub fn hex(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        let _ = write!(s, "{b:02x}");
    }
    s
}

/// SHA-256 of a file, read in 4 MiB chunks.
pub fn sha256_file(path: &Path) -> Result<String> {
    let mut f = fs::File::open(path).with_context(|| format!("{}: cannot open", path.display()))?;
    let mut h = Sha256::new();
    let mut buf = vec![0u8; 1 << 22];
    loop {
        let n = f.read(&mut buf)?;
        if n == 0 {
            break;
        }
        h.update(&buf[..n]);
    }
    Ok(hex(&h.finalize()))
}

/// Every regular file under `dir/rel` (or `rel` itself if it is one), as
/// paths relative to `dir` spelled the way `find REL -type f` prints them.
/// Symbolic links are not followed and not listed. Directories in `skip`
/// (relative paths, spelled the same way) are pruned.
pub fn find_files(dir: &Path, rel: &str, skip: &[&str], out: &mut Vec<String>) -> Result<()> {
    let p = dir.join(rel);
    let md = fs::symlink_metadata(&p).with_context(|| format!("find: '{rel}': no such file"))?;
    if md.is_file() {
        out.push(rel.to_string());
    } else if md.is_dir() {
        if skip.contains(&rel) {
            return Ok(());
        }
        for e in fs::read_dir(&p)? {
            let e = e?;
            let name = e.file_name();
            let name = name.to_str().ok_or_else(|| anyhow!("non-UTF-8 file name"))?;
            let sub = if rel.ends_with('/') {
                format!("{rel}{name}")
            } else {
                format!("{rel}/{name}")
            };
            find_files(dir, &sub, skip, out)?;
        }
    }
    Ok(())
}

/// SHA-256 over the contents of the given paths under `dir`: the
/// `sha256sum` lines of their files sorted by path (bytewise), hashed again.
/// The same as
/// `(cd DIR && find PATHS -type f -print0 | LC_ALL=C sort -z | xargs -0 sha256sum) | sha256sum`.
pub fn content_sha256(dir: &Path, paths: &[&str], skip: &[&str]) -> Result<String> {
    let mut files = Vec::new();
    for p in paths {
        find_files(dir, p, skip, &mut files)?;
    }
    files.sort();
    let mut listing = String::new();
    for f in &files {
        listing.push_str(&sha256_file(&dir.join(f))?);
        listing.push_str("  ");
        listing.push_str(f);
        listing.push('\n');
    }
    Ok(sha256_hex(listing.as_bytes()))
}

/// Copies the directory tree `from` to `to` (which is removed first), leaving
/// out every entry named `.git`. Symbolic links are copied as links.
pub fn copy_tree(from: &Path, to: &Path, exclude_git: bool) -> Result<()> {
    if to.exists() {
        fs::remove_dir_all(to)?;
    }
    copy_into(from, to, exclude_git)
}

/// Copies the contents of `from` into `to`, creating it, over whatever is there.
pub fn copy_into(from: &Path, to: &Path, exclude_git: bool) -> Result<()> {
    fs::create_dir_all(to)?;
    for e in fs::read_dir(from).with_context(|| format!("{}: cannot read", from.display()))? {
        let e = e?;
        if exclude_git && e.file_name() == ".git" {
            continue;
        }
        let src = e.path();
        let dst = to.join(e.file_name());
        let ft = e.file_type()?;
        if ft.is_dir() {
            copy_into(&src, &dst, exclude_git)?;
        } else if ft.is_symlink() {
            let target = fs::read_link(&src)?;
            let _ = fs::remove_file(&dst);
            std::os::unix::fs::symlink(target, &dst)?;
        } else {
            fs::copy(&src, &dst)
                .with_context(|| format!("copying {} to {}", src.display(), dst.display()))?;
        }
    }
    Ok(())
}

/// The directory `p`, created if needed, as an absolute path.
pub fn abs_dir(p: &Path) -> Result<PathBuf> {
    fs::create_dir_all(p).with_context(|| format!("{}: cannot create", p.display()))?;
    Ok(fs::canonicalize(p)?)
}

/// `p` made absolute against the current directory (not resolving links).
pub fn absolute(p: &Path) -> PathBuf {
    std::path::absolute(p).unwrap_or_else(|_| p.to_path_buf())
}

/// Whether `name` is an executable on PATH (or a path to one).
pub fn which(name: &str) -> Option<PathBuf> {
    if name.contains('/') {
        let p = PathBuf::from(name);
        return is_executable(&p).then_some(p);
    }
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|d| d.join(name))
        .find(|p| is_executable(p))
}

pub fn is_executable(p: &Path) -> bool {
    use std::os::unix::fs::PermissionsExt;
    fs::metadata(p)
        .map(|m| m.is_file() && m.permissions().mode() & 0o111 != 0)
        .unwrap_or(false)
}

/// Fails with `TOOL: error: NAME not found (HINT)` unless every program is on PATH.
pub fn need(tool: &str, names: &[&str], hint: &str) -> Result<()> {
    for n in names {
        if which(n).is_none() {
            bail!("{tool}: error: {n} not found{hint}");
        }
    }
    Ok(())
}

/// A program and its arguments, for the error messages.
pub fn describe(cmd: &Command) -> String {
    let mut s = cmd.get_program().to_string_lossy().into_owned();
    for a in cmd.get_args() {
        s.push(' ');
        s.push_str(&a.to_string_lossy());
    }
    s
}

/// Runs `cmd`, failing unless it exits 0.
pub fn run(cmd: &mut Command) -> Result<()> {
    let st = cmd
        .status()
        .with_context(|| format!("cannot run {}", describe(cmd)))?;
    check_status(cmd, st)
}

pub fn check_status(cmd: &Command, st: ExitStatus) -> Result<()> {
    if st.success() {
        Ok(())
    } else {
        bail!("{} failed ({st})", describe(cmd))
    }
}

/// Runs `cmd` and returns its standard output, failing unless it exits 0.
/// Its standard error goes to ours.
pub fn output(cmd: &mut Command) -> Result<String> {
    let out = cmd
        .stderr(Stdio::inherit())
        .output()
        .with_context(|| format!("cannot run {}", describe(cmd)))?;
    check_status(cmd, out.status)?;
    String::from_utf8(out.stdout).with_context(|| format!("{}: output not UTF-8", describe(cmd)))
}

/// Runs `cmd` with its standard output and error going to the file `log`;
/// on failure prints the last 40 lines of the log and fails with `msg`.
pub fn run_logged(cmd: &mut Command, log: &Path, tail: usize, msg: &str) -> Result<()> {
    let f = fs::File::create(log).with_context(|| format!("{}: cannot create", log.display()))?;
    let st = cmd
        .stdout(f.try_clone()?)
        .stderr(f)
        .status()
        .with_context(|| format!("cannot run {}", describe(cmd)))?;
    if !st.success() {
        print_tail(log, tail);
        bail!("{msg}");
    }
    Ok(())
}

/// Prints the last `n` lines of a file on stderr, as `tail -n N FILE >&2`.
pub fn print_tail(path: &Path, n: usize) {
    if let Ok(data) = fs::read(path) {
        let text = String::from_utf8_lossy(&data);
        let lines: Vec<&str> = text.lines().collect();
        let mut err = std::io::stderr().lock();
        for l in &lines[lines.len().saturating_sub(n)..] {
            let _ = writeln!(err, "{l}");
        }
    }
}

/// A command with `cwd` as its working directory.
pub fn cmd_in(program: impl AsRef<OsStr>, cwd: &Path) -> Command {
    let mut c = Command::new(program);
    c.current_dir(cwd);
    c
}

/// `git -C DIR ARGS...`
pub fn git(dir: &Path) -> Command {
    let mut c = Command::new("git");
    c.arg("-C").arg(dir);
    c
}

/// `elan toolchain install TC`, quietly unless it fails, then retried loudly
/// (as `elan toolchain install TC >/dev/null 2>&1 || elan toolchain install TC`).
pub fn elan_install(tc: &str, loud_to_stderr: bool) -> Result<()> {
    let quiet = Command::new("elan")
        .args(["toolchain", "install", tc])
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status();
    if matches!(quiet, Ok(s) if s.success()) {
        return Ok(());
    }
    let mut c = Command::new("elan");
    c.args(["toolchain", "install", tc]);
    if loud_to_stderr {
        c.stdout(Stdio::from(std::io::stderr().as_fd().try_clone_to_owned()?));
    }
    run(&mut c)
}

use std::os::fd::AsFd;

/// The prefix of a toolchain: `elan run TC lean --print-prefix`.
pub fn lean_prefix(tc: &str) -> Result<PathBuf> {
    let out = output(Command::new("elan").args(["run", tc, "lean", "--print-prefix"]))?;
    Ok(PathBuf::from(out.trim()))
}

/// The directory holding a toolchain's `lean`, `lake` and `leanchecker`,
/// installing the toolchain if needed.
pub fn tc_bin(tc: &str) -> Result<PathBuf> {
    elan_install(tc, true)?;
    Ok(lean_prefix(tc)?.join("bin"))
}

/// PATH with `dir` in front.
pub fn path_with(dir: &Path) -> std::ffi::OsString {
    let mut parts = vec![dir.to_path_buf()];
    if let Some(p) = std::env::var_os("PATH") {
        parts.extend(std::env::split_paths(&p));
    }
    std::env::join_paths(parts).expect("PATH entries without ':'")
}

/// Sets the soft stack limit of the commands this process starts to the
/// hard limit (`ulimit -s unlimited` where the hard limit allows it).
pub fn unlimited_stack(cmd: &mut Command) {
    use std::os::unix::process::CommandExt;
    // SAFETY: only async-signal-safe libc calls between fork and exec.
    unsafe {
        cmd.pre_exec(|| {
            let mut r = libc::rlimit {
                rlim_cur: 0,
                rlim_max: 0,
            };
            if libc::getrlimit(libc::RLIMIT_STACK, &mut r) == 0 {
                r.rlim_cur = r.rlim_max;
                if libc::setrlimit(libc::RLIMIT_STACK, &r) != 0 {
                    return Err(std::io::Error::last_os_error());
                }
            }
            Ok(())
        });
    }
}

/// The rows of a TSV file with a header line, as maps from column to value.
/// Empty lines are skipped; missing trailing cells are left out of the map.
pub fn read_tsv(path: &Path) -> Result<Vec<HashMap<String, String>>> {
    let text =
        fs::read_to_string(path).with_context(|| format!("{}: cannot read", path.display()))?;
    Ok(parse_tsv(&text))
}

pub fn parse_tsv(text: &str) -> Vec<HashMap<String, String>> {
    let mut lines = text.lines();
    let head: Vec<&str> = lines.next().unwrap_or("").split('\t').collect();
    lines
        .filter(|l| !l.is_empty())
        .map(|l| {
            head.iter()
                .zip(l.split('\t'))
                .map(|(h, v)| (h.to_string(), v.to_string()))
                .collect()
        })
        .collect()
}

/// A cell of a TSV row, empty if absent.
pub fn cell<'a>(row: &'a HashMap<String, String>, col: &str) -> &'a str {
    row.get(col).map(String::as_str).unwrap_or("")
}

/// Whitespace runs collapsed to single spaces, as `" ".join(s.split())`.
pub fn squash(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The first `n` characters of `s`.
pub fn truncate(s: &str, n: usize) -> String {
    s.chars().take(n).collect()
}

/// Shell-style glob match (`*`, `?`, `[...]` with `!` or `^` and ranges),
/// where `*` also matches `/`, as Python's fnmatch and bash's `[[ == ]]`.
pub fn glob_match(pat: &str, s: &str) -> bool {
    let p: Vec<char> = pat.chars().collect();
    let t: Vec<char> = s.chars().collect();
    glob_at(&p, &t)
}

fn glob_at(p: &[char], t: &[char]) -> bool {
    match p.first() {
        None => t.is_empty(),
        Some('*') => (0..=t.len()).any(|i| glob_at(&p[1..], &t[i..])),
        Some('?') => !t.is_empty() && glob_at(&p[1..], &t[1..]),
        Some('[') => match class(p) {
            Some((len, set)) => !t.is_empty() && set(t[0]) && glob_at(&p[len..], &t[1..]),
            None => t.first() == Some(&'[') && glob_at(&p[1..], &t[1..]),
        },
        Some('\\') if p.len() > 1 => t.first() == Some(&p[1]) && glob_at(&p[2..], &t[1..]),
        Some(c) => t.first() == Some(c) && glob_at(&p[1..], &t[1..]),
    }
}

/// A bracket expression at the start of `p`: its length and a predicate.
#[allow(clippy::type_complexity)]
fn class(p: &[char]) -> Option<(usize, Box<dyn Fn(char) -> bool>)> {
    let mut i = 1;
    let neg = matches!(p.get(i), Some('!') | Some('^'));
    if neg {
        i += 1;
    }
    let start = i;
    let mut ranges = Vec::new();
    while i < p.len() && (p[i] != ']' || i == start) {
        if i + 2 < p.len() && p[i + 1] == '-' && p[i + 2] != ']' {
            ranges.push((p[i], p[i + 2]));
            i += 3;
        } else {
            ranges.push((p[i], p[i]));
            i += 1;
        }
    }
    if i >= p.len() {
        return None;
    }
    Some((
        i + 1,
        Box::new(move |c| ranges.iter().any(|&(a, b)| a <= c && c <= b) != neg),
    ))
}

/// `f` applied to every item on `jobs` threads; `sink` gets the results in
/// the order of the items, each as soon as it and those before it are done.
pub fn par_map_ordered<T, R, F, S>(items: Vec<T>, jobs: usize, f: F, mut sink: S)
where
    T: Send,
    R: Send,
    F: Fn(T) -> R + Sync,
    S: FnMut(R),
{
    let n = items.len();
    let queue = std::sync::Mutex::new(items.into_iter().enumerate());
    let (tx, rx) = mpsc::channel::<(usize, R)>();
    std::thread::scope(|s| {
        for _ in 0..jobs.max(1).min(n.max(1)) {
            let tx = tx.clone();
            let (queue, f) = (&queue, &f);
            s.spawn(move || {
                loop {
                    let next = queue.lock().unwrap().next();
                    let Some((i, item)) = next else { break };
                    if tx.send((i, f(item))).is_err() {
                        break;
                    }
                }
            });
        }
        drop(tx);
        let mut done: HashMap<usize, R> = HashMap::new();
        let mut next = 0;
        for (i, r) in rx {
            done.insert(i, r);
            while let Some(r) = done.remove(&next) {
                sink(r);
                next += 1;
            }
        }
    });
}

/// The number of CPUs, as `nproc` or `os.cpu_count()`.
pub fn nproc() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
}

/// Python's `format(x, "g")`: 6 significant digits, trailing zeros removed,
/// exponent form below 1e-4 and from 1e6.
pub fn fmt_g(x: f64) -> String {
    if x == 0.0 {
        return "0".into();
    }
    if !x.is_finite() {
        return if x.is_nan() {
            "nan".into()
        } else if x > 0.0 {
            "inf".into()
        } else {
            "-inf".into()
        };
    }
    let e = format!("{x:.5e}");
    let (mant, exp) = e.split_once('e').unwrap();
    let exp: i32 = exp.parse().unwrap();
    if !(-4..6).contains(&exp) {
        let mant = trim_zeros(mant);
        let sign = if exp < 0 { '-' } else { '+' };
        return format!("{mant}e{sign}{:02}", exp.abs());
    }
    let decimals = (5 - exp).max(0) as usize;
    trim_zeros(&format!("{x:.decimals$}")).to_string()
}

fn trim_zeros(s: &str) -> &str {
    if s.contains('.') {
        s.trim_end_matches('0').trim_end_matches('.')
    } else {
        s
    }
}

/// Writes `text` to `path`, creating its directory.
pub fn write_file(path: &Path, text: impl AsRef<[u8]>) -> Result<()> {
    if let Some(d) = path.parent() {
        fs::create_dir_all(d)?;
    }
    fs::write(path, text).with_context(|| format!("{}: cannot write", path.display()))
}

/// The size of a file in bytes.
pub fn file_size(path: &Path) -> Result<u64> {
    Ok(fs::metadata(path)
        .with_context(|| format!("{}: no such file", path.display()))?
        .len())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn globs() {
        assert!(glob_match("perf/*", "perf/a/b"));
        assert!(glob_match("std", "std"));
        assert!(!glob_match("std", "std2"));
        assert!(glob_match("a?c", "abc"));
        assert!(glob_match("[a-c]x", "bx"));
        assert!(!glob_match("[!a-c]x", "bx"));
        assert!(glob_match("*.bin", "dir/x.bin"));
    }

    #[test]
    fn format_g() {
        assert_eq!(fmt_g(120.0), "120");
        assert_eq!(fmt_g(1.5), "1.5");
        assert_eq!(fmt_g(360.0), "360");
        assert_eq!(fmt_g(0.1), "0.1");
        assert_eq!(fmt_g(1e6), "1e+06");
        assert_eq!(fmt_g(123456.7), "123457");
        assert_eq!(fmt_g(0.00001), "1e-05");
    }

    #[test]
    fn ordered_map() {
        let mut got = Vec::new();
        par_map_ordered((0..50).collect(), 4, |i: i32| i * 2, |r| got.push(r));
        assert_eq!(got, (0..50).map(|i| i * 2).collect::<Vec<_>>());
    }
}
