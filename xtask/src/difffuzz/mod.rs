//! Differential fuzzer: nitrolean against Lean's `leanchecker --from-export`
//! (`cargo xtask difffuzz ...`). See tests/fuzz/README.md.
//!
//!   seeds [--mathlib DIR] [--screen-only] [--jobs N]
//!   run --count N [--start S] [--base B] [--jobs N] [--categories a,b] [--only-seeds TEXT] [--out DIR]
//!   summary [--out DIR]
//!   triage [--out DIR]
//!   replay ID [--out DIR]
//!   minimize FILE [--to OUT]
//!   seed-corpus
//!
//! NITROLEAN, LEANCHECKER, FUZZ_TMP and FUZZ_MEMORY_MB override the defaults.

mod export;
mod minimize;
mod mutate;
mod oracle;
mod rng;

use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, mpsc};
use std::time::{Duration, Instant};

use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use oracle::{Checkers, disagree};

fn root() -> PathBuf {
    crate::util::root()
}

fn fuzz_dir() -> PathBuf {
    root().join("tests/fuzz")
}

fn out_dir() -> PathBuf {
    fuzz_dir().join("out")
}

fn die(msg: &str) -> ! {
    eprintln!("difffuzz: {msg}");
    std::process::exit(2)
}

// ---------------------------------------------------------------------------
// Arguments

struct Opts {
    pos: Vec<String>,
    opts: HashMap<String, String>,
    flags: Vec<String>,
}

impl Opts {
    fn parse(v: Vec<String>, flags: &[&str]) -> Opts {
        let mut a = Opts {
            pos: Vec::new(),
            opts: HashMap::new(),
            flags: Vec::new(),
        };
        let mut it = v.into_iter();
        while let Some(x) = it.next() {
            if let Some(k) = x.strip_prefix("--") {
                if flags.contains(&k) {
                    a.flags.push(k.to_string());
                } else {
                    let v = it
                        .next()
                        .unwrap_or_else(|| die(&format!("--{k} needs a value")));
                    a.opts.insert(k.to_string(), v);
                }
            } else {
                a.pos.push(x);
            }
        }
        a
    }

    fn get(&self, k: &str) -> Option<&str> {
        self.opts.get(k).map(String::as_str)
    }

    fn num(&self, k: &str, default: u64) -> u64 {
        self.get(k).map_or(default, |v| {
            v.parse()
                .unwrap_or_else(|_| die(&format!("--{k}: not a number")))
        })
    }

    fn out(&self) -> PathBuf {
        self.get("out")
            .map_or_else(|| out_dir().join("run"), PathBuf::from)
    }

    fn jobs(&self) -> usize {
        self.num(
            "jobs",
            std::thread::available_parallelism().map_or(2, |n| n.get()) as u64,
        ) as usize
    }
}

// ---------------------------------------------------------------------------
// Tools

fn lean_bin() -> PathBuf {
    if let Ok(p) = std::env::var("LEANCHECKER") {
        return Path::new(&p).parent().unwrap().to_path_buf();
    }
    let o = Command::new("elan")
        .args(["which", "lean"])
        .current_dir(root().join("tests/kernel"))
        .output()
        .unwrap_or_else(|e| die(&format!("elan: {e}")));
    let s = String::from_utf8_lossy(&o.stdout).trim().to_string();
    Path::new(&s)
        .parent()
        .unwrap_or_else(|| die("elan which lean gave nothing"))
        .to_path_buf()
}

fn checkers() -> Checkers {
    let nitrolean = std::env::var("NITROLEAN")
        .map_or_else(|_| root().join("target/release/nitrolean"), PathBuf::from);
    if !nitrolean.exists() {
        die(&format!(
            "{} not found: run cargo build --release",
            nitrolean.display()
        ));
    }
    Checkers {
        nitrolean,
        leanchecker: lean_bin().join("leanchecker"),
        timeout: Duration::from_secs(30),
        memory_mb: std::env::var("FUZZ_MEMORY_MB")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(6144),
    }
}

fn tmp_dir() -> PathBuf {
    std::env::var("FUZZ_TMP").map_or_else(|_| std::env::temp_dir(), PathBuf::from)
}

fn sha_hex(b: &[u8]) -> String {
    Sha256::digest(b)
        .iter()
        .map(|x| format!("{x:02x}"))
        .collect()
}

/// Run `f` over `items` on `jobs` threads; results in completion order through `sink`.
fn parallel<T: Send + Sync, R: Send>(
    items: &[T],
    jobs: usize,
    f: &(dyn Fn(&T) -> R + Sync),
    sink: &mut dyn FnMut(R),
) {
    let next = AtomicUsize::new(0);
    let (tx, rx) = mpsc::channel();
    std::thread::scope(|s| {
        for _ in 0..jobs.max(1) {
            let tx = tx.clone();
            let next = &next;
            s.spawn(move || {
                loop {
                    let i = next.fetch_add(1, Ordering::Relaxed);
                    if i >= items.len() {
                        break;
                    }
                    if tx.send(f(&items[i])).is_err() {
                        break;
                    }
                }
            });
        }
        drop(tx);
        for r in rx {
            sink(r);
        }
    });
}

// ---------------------------------------------------------------------------
// Seeds

const FEATURES: &[(&str, &str)] = &[
    ("quot", "\"quot\":{"),
    ("natlit", "\"natVal\""),
    ("let", "\"letE\""),
    ("proj", "\"proj\":{"),
    ("inductive", "\"inductive\":{"),
];

fn seed_dirs() -> Vec<PathBuf> {
    vec![
        out_dir().join("seeds"),
        root().join("corpus/exports"),
        root().join("tests/kernel/exports"),
    ]
}

fn walk(d: &Path, out: &mut Vec<PathBuf>) {
    let Ok(rd) = fs::read_dir(d) else { return };
    let mut es: Vec<PathBuf> = rd.filter_map(|e| e.ok()).map(|e| e.path()).collect();
    es.sort();
    for p in es {
        if p.is_dir() {
            walk(&p, out);
        } else if p.extension().is_some_and(|e| e == "ndjson") {
            out.push(p);
        }
    }
}

fn rel(p: &Path) -> String {
    p.strip_prefix(root())
        .unwrap_or(p)
        .to_string_lossy()
        .into_owned()
}

fn cmd_seeds(a: &Opts) {
    if !a.flags.iter().any(|f| f == "screen-only") {
        build_seeds(a);
    }
    screen(a);
}

fn build_seeds(a: &Opts) {
    let bin = lean_bin();
    let build = out_dir().join("build");
    let sdir = out_dir().join("seeds");
    fs::create_dir_all(&build).unwrap();
    fs::create_dir_all(&sdir).unwrap();
    let lean_path = format!("{}:{}", bin.join("../lib/lean").display(), build.display());
    let src = fuzz_dir().join("seeds/FuzzSeeds.lean");
    let st = Command::new(bin.join("lean"))
        .arg("-o")
        .arg(build.join("FuzzSeeds.olean"))
        .arg(&src)
        .env("LEAN_PATH", &lean_path)
        .status()
        .unwrap_or_else(|e| die(&format!("lean: {e}")));
    if !st.success() {
        die("compiling seeds/FuzzSeeds.lean failed");
    }
    let text = fs::read_to_string(&src).unwrap();
    let names: Vec<String> = text
        .lines()
        .filter_map(|l| l.strip_prefix("theorem "))
        .filter_map(|l| l.split_whitespace().next())
        .map(String::from)
        .collect();
    let jobs = a.jobs();
    parallel(
        &names,
        jobs,
        &|n: &String| {
            let o = Command::new(bin.join("leanexport"))
                .args(["FuzzSeeds", "--", &format!("FZ.{n}")])
                .env("LEAN_PATH", &lean_path)
                .output()
                .expect("leanexport");
            fs::write(sdir.join(format!("fz-{n}.ndjson")), &o.stdout).unwrap();
        },
        &mut |_| {},
    );
    if let Some(ml) = a.get("mathlib") {
        mathlib_slices(&bin, Path::new(ml), &sdir);
    }
}

/// Export the closures listed in seeds/mathlib-slices.txt from a built Mathlib checkout.
fn mathlib_slices(bin: &Path, mathlib: &Path, sdir: &Path) {
    let list = fs::read_to_string(fuzz_dir().join("seeds/mathlib-slices.txt")).unwrap();
    for ln in list.lines() {
        let ln = ln.split('#').next().unwrap().trim();
        let mut it = ln.split_whitespace();
        let Some(module) = it.next() else { continue };
        let consts: Vec<&str> = it.collect();
        let Some(first) = consts.first() else {
            continue;
        };
        let tag = first.replace(['.', '\''], "_");
        let o = Command::new("lake")
            .arg("env")
            .arg(bin.join("leanexport"))
            .arg(module)
            .arg("--")
            .args(&consts)
            .current_dir(mathlib)
            .output();
        match o {
            Ok(o) if o.status.success() => {
                fs::write(sdir.join(format!("ml-{tag}.ndjson")), &o.stdout).unwrap()
            }
            Ok(o) => eprintln!(
                "mathlib slice {tag} failed: {}",
                String::from_utf8_lossy(&o.stderr)
            ),
            Err(e) => eprintln!("mathlib slice {tag} failed: {e}"),
        }
    }
}

/// Write out/seeds.tsv: both verdicts per candidate; seeds both accept are fuzzed.
fn screen(a: &Opts) {
    let max = a.num("max-seed-bytes", 4 << 20);
    let mut files = Vec::new();
    for d in seed_dirs() {
        walk(&d, &mut files);
    }
    files.retain(|f| {
        let limit = if f.file_name().unwrap().to_string_lossy().starts_with("ml-") {
            max * 8
        } else {
            max
        };
        fs::metadata(f).is_ok_and(|m| m.len() <= limit)
    });
    let ck = checkers();
    let mut rows = Vec::new();
    parallel(
        &files,
        a.jobs(),
        &|f: &PathBuf| {
            let text = fs::read_to_string(f).unwrap_or_default();
            let feats: Vec<&str> = FEATURES
                .iter()
                .filter(|(_, s)| text.contains(s))
                .map(|x| x.0)
                .collect();
            (
                rel(f),
                ck.nitrolean(f).verdict,
                ck.lean(f).verdict,
                text.len(),
                feats.join(","),
            )
        },
        &mut |r| rows.push(r),
    );
    rows.sort();
    let mut s = String::from("path\tnitrolean\tlean\tbytes\tfeatures\n");
    let mut ok = 0;
    for (p, n, l, b, f) in &rows {
        ok += (n == "accept" && l == "accept") as usize;
        s.push_str(&format!("{p}\t{n}\t{l}\t{b}\t{f}\n"));
    }
    fs::create_dir_all(out_dir()).unwrap();
    fs::write(out_dir().join("seeds.tsv"), s).unwrap();
    println!("seeds: {} candidates, {ok} accepted by both", rows.len());
}

struct SeedList {
    paths: Vec<String>,
    features: HashMap<String, Vec<String>>,
}

fn load_seeds() -> SeedList {
    let p = out_dir().join("seeds.tsv");
    let text = fs::read_to_string(&p)
        .unwrap_or_else(|_| die("no out/seeds.tsv: run `difffuzz seeds` first"));
    let mut l = SeedList {
        paths: Vec::new(),
        features: HashMap::new(),
    };
    for ln in text.lines().skip(1) {
        let c: Vec<&str> = ln.split('\t').collect();
        if c.len() >= 5 && c[1] == "accept" && c[2] == "accept" {
            l.paths.push(c[0].to_string());
            l.features.insert(
                c[0].to_string(),
                c[4].split(',').map(String::from).collect(),
            );
        }
    }
    l
}

// ---------------------------------------------------------------------------
// Mutants

fn eval_seed(path: &str) -> bool {
    let b = Path::new(path)
        .file_name()
        .unwrap()
        .to_string_lossy()
        .into_owned();
    (b.starts_with("fz-")
        && b.as_bytes()
            .get(3)
            .is_some_and(|c| b"nrlbdasfuc".contains(c)))
        || b.contains("eval")
        || b.contains("decide")
        || b.starts_with("ml-")
}

/// Mutant number i: (seed, category, generator seed). Deterministic.
fn plan(seeds: &SeedList, i: u64, cats: &[String], base: u64) -> (String, String, u64) {
    let h = Sha256::digest(format!("{base}:{i}").as_bytes());
    let word = |k: usize| u64::from_be_bytes(h[k * 8..k * 8 + 8].try_into().unwrap());
    let cat = cats[(word(0) % cats.len() as u64) as usize].clone();
    let pool: Vec<&String> = if cat == "eval" {
        seeds.paths.iter().filter(|s| eval_seed(s)).collect()
    } else if FEATURES.iter().any(|f| f.0 == cat) {
        seeds
            .paths
            .iter()
            .filter(|s| seeds.features[*s].contains(&cat))
            .collect()
    } else {
        seeds.paths.iter().collect()
    };
    let pool = if pool.is_empty() {
        seeds.paths.iter().collect()
    } else {
        pool
    };
    let seed = pool[(word(1) % pool.len() as u64) as usize].clone();
    (seed, cat, word(2))
}

fn focus_of(path: &str) -> Option<&'static str> {
    Path::new(path)
        .file_name()
        .unwrap()
        .to_string_lossy()
        .starts_with("fz-")
        .then_some("FZ.")
}

struct SeedCache(Mutex<Vec<(String, Arc<export::Seed>)>>);

impl SeedCache {
    fn get(&self, path: &str) -> Arc<export::Seed> {
        if let Some(s) = self.0.lock().unwrap().iter().find(|x| x.0 == path) {
            return s.1.clone();
        }
        let text =
            fs::read_to_string(root().join(path)).unwrap_or_else(|e| die(&format!("{path}: {e}")));
        let s = Arc::new(export::Seed::parse(path, &text).unwrap_or_else(|e| die(&e)));
        let mut c = self.0.lock().unwrap();
        if c.len() > 24 {
            c.remove(0);
        }
        c.push((path.to_string(), s.clone()));
        s
    }
}

/// A tag for a disagreement of an already-understood class, or "".
fn known(
    nl: &str,
    lean: &str,
    nl_msg: &str,
    lean_msg: &str,
    decl: &str,
    text: &str,
) -> &'static str {
    let big = |key: &str| {
        text.match_indices(&format!("\"{key}\":")).any(|(i, m)| {
            let digits: String = text[i + m.len()..]
                .chars()
                .take_while(|c| c.is_ascii_digit())
                .collect();
            digits.parse::<u128>().is_ok_and(|v| v >= 1 << 32) || digits.len() > 20
        })
    };
    if nl == "reject" && lean == "accept" {
        if nl_msg.contains("is out of range") {
            // a UInt32 field past 2^32 - 1, which Lean v4.36.0 truncates (009_HB16279)
            return "u32-field-out-of-range";
        }
        if mutate::BUILTINS.contains(&decl) {
            return "redefined-builtin";
        }
        if [
            "numParams",
            "numIndices",
            "numFields",
            "numMotives",
            "numMinors",
            "numNested",
            "nfields",
            "cidx",
            "idx",
        ]
        .iter()
        .any(|k| big(k))
        {
            return "u32-field-out-of-range";
        }
        if nl_msg.contains("does not match the declaration derived from its inductive type") {
            return "ctor-or-rec-flags (open: fuzz-ctor-unsafe-flag, fuzz-rec-unsafe-flag)";
        }
    }
    if nl == "accept" && lean == "reject" && lean_msg.contains("No such constructor") {
        return "type-unsafe-flag (open: fuzz-type-unsafe-flag)";
    }
    ""
}

fn cmd_run(a: &Opts) {
    let seeds = load_seeds();
    let mut seeds = seeds;
    if let Some(f) = a.get("only-seeds") {
        seeds.paths.retain(|p| p.contains(f));
    }
    if seeds.paths.is_empty() {
        die("no seeds");
    }
    let cats: Vec<String> = a.get("categories").map_or_else(
        || mutate::CATEGORIES.iter().map(|s| s.to_string()).collect(),
        |c| c.split(',').map(String::from).collect(),
    );
    for c in &cats {
        if !mutate::CATEGORIES.contains(&c.as_str()) {
            die(&format!("unknown category {c}"));
        }
    }
    let out = a.out();
    fs::create_dir_all(&out).unwrap();
    let res = out.join("results.jsonl");
    let mut done = std::collections::HashSet::new();
    if let Ok(t) = fs::read_to_string(&res) {
        for ln in t.lines() {
            if let Ok(v) = serde_json::from_str::<Value>(ln) {
                done.insert(v["id"].as_u64().unwrap_or(u64::MAX));
            }
        }
    }
    let (start, count, base) = (a.num("start", 0), a.num("count", 0), a.num("base", 0));
    let mut tasks: Vec<(u64, String, String, u64)> = (start..start + count)
        .filter(|i| !done.contains(i))
        .map(|i| {
            let (s, c, r) = plan(&seeds, i, &cats, base);
            (i, s, c, r)
        })
        .collect();
    tasks.sort_by(|x, y| (&x.1, x.0).cmp(&(&y.1, y.0)));
    let ck = checkers();
    let cache = SeedCache(Mutex::new(Vec::new()));
    let mut file = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&res)
        .unwrap();
    let t0 = Instant::now();
    let total = tasks.len();
    let (mut n, mut dis) = (0, 0);
    parallel(
        &tasks,
        a.jobs(),
        &|t| work(t, &cache, &ck, &out),
        &mut |rec: Value| {
            writeln!(file, "{rec}").unwrap();
            n += 1;
            if disagree(
                rec["nl"].as_str().unwrap_or(""),
                rec["lean"].as_str().unwrap_or(""),
            ) {
                dis += 1;
                println!(
                    "DISAGREE {}: {} {} [{}] nitrolean={} lean={} {}",
                    rec["id"],
                    s(&rec["cat"]),
                    s(&rec["op"]),
                    rec["decl"].as_str().unwrap_or(""),
                    s(&rec["nl"]),
                    s(&rec["lean"]),
                    rec["known"].as_str().unwrap_or("")
                );
            }
            if n % 1000 == 0 {
                println!(
                    "{n}/{total} done, {dis} disagreements, {:.0}/s",
                    n as f64 / t0.elapsed().as_secs_f64()
                );
            }
        },
    );
    println!("finished: {n} mutants run, {dis} disagreements");
}

fn work(t: &(u64, String, String, u64), cache: &SeedCache, ck: &Checkers, out: &Path) -> Value {
    let (i, path, cat, rs) = t;
    let mut rec = json!({"id": i, "seed": path, "cat": cat, "rs": rs});
    let seed = cache.get(path);
    let mut rng = rng::Rng::new(*rs);
    let Some(m) = mutate::mutate(&seed, cat, &mut rng, focus_of(path)) else {
        rec["status"] = json!("nomutant");
        return rec;
    };
    let text = m.text();
    rec["op"] = json!(m.op);
    rec["decl"] = json!(m.decl);
    rec["note"] = json!(m.note);
    rec["expect"] = json!(m.expect);
    rec["digest"] = json!(sha_hex(text.as_bytes())[..20]);
    let tmp = tmp_dir().join(format!("difffuzz-{}-{i}.ndjson", std::process::id()));
    fs::write(&tmp, &text).unwrap();
    let nv = ck.nitrolean(&tmp);
    let lv = ck.lean(&tmp);
    rec["nl"] = json!(nv.verdict);
    rec["lean"] = json!(lv.verdict);
    rec["nl_t"] = json!((nv.secs * 1000.0).round() / 1000.0);
    rec["lean_t"] = json!((lv.secs * 1000.0).round() / 1000.0);
    rec["status"] = json!("ok");
    let normal = |v: &str| v == "accept" || v == "reject";
    let d = disagree(&nv.verdict, &lv.verdict);
    if d || !normal(&nv.verdict) || !normal(&lv.verdict) {
        rec["nl_msg"] = json!(nv.msg);
        rec["lean_msg"] = json!(lv.msg);
        rec["known"] = json!(if d {
            known(&nv.verdict, &lv.verdict, &nv.msg, &lv.msg, &m.decl, &text)
        } else {
            ""
        });
        let sub = out.join(if d { "disagree" } else { "anomaly" });
        fs::create_dir_all(&sub).unwrap();
        let keep = sub.join(format!("{cat}-{i}.ndjson"));
        fs::write(&keep, &text).unwrap();
        rec["file"] = json!(keep.strip_prefix(out).unwrap().to_string_lossy());
    }
    let _ = fs::remove_file(&tmp);
    rec
}

fn read_results(out: &Path) -> Vec<Value> {
    fs::read_to_string(out.join("results.jsonl"))
        .unwrap_or_else(|_| die("no results.jsonl"))
        .lines()
        .filter_map(|l| serde_json::from_str(l).ok())
        .collect()
}

fn s(v: &Value) -> &str {
    v.as_str().unwrap_or("")
}

fn cmd_summary(a: &Opts) {
    let mut by: BTreeMap<(String, String, String), u64> = BTreeMap::new();
    let mut seen = std::collections::HashSet::new();
    let mut dup = 0;
    let mut tot: BTreeMap<String, u64> = BTreeMap::new();
    for r in read_results(&a.out()) {
        if s(&r["status"]) != "ok" {
            *by.entry((s(&r["cat"]).into(), "-".into(), s(&r["status"]).into()))
                .or_default() += 1;
            continue;
        }
        if !seen.insert(s(&r["digest"]).to_string()) {
            dup += 1;
            continue;
        }
        let mut v = format!("{}/{}", s(&r["nl"]), s(&r["lean"]));
        if disagree(s(&r["nl"]), s(&r["lean"])) {
            v = format!("DISAGREE {v}");
            if !s(&r["known"]).is_empty() {
                v = format!("{v} known:{}", s(&r["known"]));
            }
        }
        *by.entry((s(&r["cat"]).into(), s(&r["op"]).into(), v))
            .or_default() += 1;
        *tot.entry(s(&r["cat"]).into()).or_default() += 1;
    }
    for ((c, o, v), k) in &by {
        println!("{c:<10} {o:<16} {v:<60} {k:>7}");
    }
    println!(
        "unique mutants per category: {} total {} duplicates {dup}",
        serde_json::to_string(&tot).unwrap(),
        tot.values().sum::<u64>()
    );
}

fn norm(m: &str) -> String {
    let mut out = String::new();
    let mut in_q = false;
    let mut last_digit = false;
    for c in m.chars() {
        if c == '\'' {
            if !in_q {
                out.push_str("'X'");
            }
            in_q = !in_q;
            continue;
        }
        if in_q {
            continue;
        }
        if c.is_ascii_digit() {
            if !last_digit {
                out.push('N');
            }
            last_digit = true;
            continue;
        }
        last_digit = false;
        out.push(c);
    }
    let out: String = out
        .split_whitespace()
        .filter(|w| !w.contains(".ndjson"))
        .collect::<Vec<_>>()
        .join(" ");
    out.chars().take(120).collect()
}

fn cmd_triage(a: &Opts) {
    let mut buckets: BTreeMap<String, Vec<Value>> = BTreeMap::new();
    for r in read_results(&a.out()) {
        if s(&r["status"]) == "ok" && disagree(s(&r["nl"]), s(&r["lean"])) {
            let sig = format!(
                "{}/{} {}.{} | {} | {}",
                s(&r["nl"]),
                s(&r["lean"]),
                s(&r["cat"]),
                s(&r["op"]),
                norm(s(&r["nl_msg"])),
                norm(s(&r["lean_msg"]))
            );
            buckets.entry(sig).or_default().push(r);
        }
    }
    let mut v: Vec<_> = buckets.into_iter().collect();
    v.sort_by_key(|(_, rs)| std::cmp::Reverse(rs.len()));
    for (sig, rs) in v {
        let e = &rs[0];
        println!(
            "{:>5}  {sig}\n       e.g. {} ({}, {}) known={}",
            rs.len(),
            s(&e["file"]),
            s(&e["seed"]),
            s(&e["note"]),
            s(&e["known"])
        );
    }
}

fn cmd_replay(a: &Opts) {
    let id: u64 = a
        .pos
        .first()
        .and_then(|x| x.parse().ok())
        .unwrap_or_else(|| die("replay ID"));
    let r = read_results(&a.out())
        .into_iter()
        .rfind(|r| r["id"].as_u64() == Some(id));
    let r = r.unwrap_or_else(|| die(&format!("no mutant {id} in results")));
    let cache = SeedCache(Mutex::new(Vec::new()));
    let seed = cache.get(s(&r["seed"]));
    let mut rng = rng::Rng::new(r["rs"].as_u64().unwrap());
    let m = mutate::mutate(&seed, s(&r["cat"]), &mut rng, focus_of(s(&r["seed"])))
        .unwrap_or_else(|| die("no mutant"));
    print!("{}", m.text());
}

fn cmd_minimize(a: &Opts) {
    let file = a.pos.first().unwrap_or_else(|| die("minimize FILE"));
    let text = fs::read_to_string(file).unwrap_or_else(|e| die(&format!("{file}: {e}")));
    let lines: Vec<String> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(String::from)
        .collect();
    let ck = checkers();
    let p = Path::new(file);
    let target = (ck.nitrolean(p).verdict, ck.lean(p).verdict);
    println!("verdicts: nitrolean={} lean={}", target.0, target.1);
    let tmp = tmp_dir().join(format!("difffuzz-min-{}.ndjson", std::process::id()));
    let mut calls = 0;
    let mut holds = |c: &[String]| {
        calls += 1;
        fs::write(&tmp, c.join("\n") + "\n").unwrap();
        (ck.nitrolean(&tmp).verdict, ck.lean(&tmp).verdict) == target
    };
    let out = minimize::minimize(lines, &mut holds, &|m| println!("{m}"));
    let _ = fs::remove_file(&tmp);
    let to = a
        .get("to")
        .map_or_else(|| file.replace(".ndjson", ".min.ndjson"), String::from);
    fs::write(&to, out.join("\n") + "\n").unwrap();
    println!("wrote {to}: {} lines ({calls} checks)", out.len());
}

/// Seed the cargo-fuzz corpora (fuzz/corpus/<target>/) from the corpus and the kernel cases.
fn cmd_seed_corpus() {
    let out = root().join("fuzz/corpus");
    for t in ["read_ndjson", "check_export", "read_olean"] {
        fs::create_dir_all(out.join(t)).unwrap();
    }
    let copy = |src: &Path, dir: &str| {
        let b = fs::read(src).unwrap();
        fs::write(out.join(dir).join(&sha_hex(&b)[..16]), b).unwrap();
    };
    let mut files = Vec::new();
    walk(&root().join("corpus/exports"), &mut files);
    walk(&root().join("tests/kernel/exports"), &mut files);
    if files.is_empty() {
        eprintln!("seed-corpus: no exports found; run scripts/fetch-corpus.sh");
    }
    for f in &files {
        let size = fs::metadata(f).unwrap().len();
        if size <= 1 << 20 {
            copy(f, "read_ndjson");
        }
        // the perf tests are slow and large on purpose: they would only report timeouts
        if size <= 64 << 10 && !rel(f).contains("/arena/perf/") {
            copy(f, "check_export");
        }
    }
    let bin = lean_bin();
    let tmp = tmp_dir().join(format!("difffuzz-tiny-{}.olean", std::process::id()));
    let st = Command::new(bin.join("lean"))
        .arg("-o")
        .arg(&tmp)
        .arg(root().join("fuzz/seeds/FuzzTiny.lean"))
        .status()
        .unwrap_or_else(|e| die(&format!("lean: {e}")));
    if !st.success() {
        die("compiling fuzz/seeds/FuzzTiny.lean failed");
    }
    copy(&tmp, "read_olean");
    let _ = fs::remove_file(&tmp);
    for t in ["read_ndjson", "check_export", "read_olean"] {
        println!(
            "seed-corpus: {t}: {} inputs",
            fs::read_dir(out.join(t)).unwrap().count()
        );
    }
}

/// `cargo xtask difffuzz`: the arguments are parsed here, as listed above.
#[derive(clap::Args)]
pub struct Args {
    /// The subcommand and its options (see `cargo xtask difffuzz help`).
    #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
    args: Vec<String>,
}

pub fn main(args: Args) -> anyhow::Result<()> {
    let mut argv = args.args;
    if argv.is_empty() || matches!(argv[0].as_str(), "-h" | "--help" | "help") {
        let doc: Vec<&str> = include_str!("mod.rs")
            .lines()
            .take(13)
            .map(|l| l.trim_start_matches("//!").trim_start_matches(' '))
            .collect();
        println!("{}", doc.join("\n"));
        return Ok(());
    }
    let cmd = argv.remove(0);
    let a = Opts::parse(argv, &["screen-only"]);
    match cmd.as_str() {
        "seeds" => cmd_seeds(&a),
        "run" => cmd_run(&a),
        "summary" => cmd_summary(&a),
        "triage" => cmd_triage(&a),
        "replay" => cmd_replay(&a),
        "minimize" => cmd_minimize(&a),
        "seed-corpus" => cmd_seed_corpus(),
        _ => die(&format!("unknown command {cmd}")),
    }
    Ok(())
}
