//! Print `src/check/fingerprint_table.rs` from an export of Lean's prelude:
//! the fingerprint of each operation with built-in `Nat` arithmetic and
//! of every declaration it depends on.
//!
//! Each EXPORT is the closure of the operations in that version's `Init`
//! (`lean4export Init -- Nat.add Nat.sub ...`, every name of `NAT_OPS`,
//! `ARRAY_OPS`, `LIST_OPS`, `DEC_EQ_OPS` and `BEQ_PROD`):
//!
//! ```text
//! cargo run --release --example fingerprints -- v4.36.0=init-4.36.ndjson \
//!     v4.34.0=init-4.34.ndjson > src/check/fingerprint_table.rs
//! ```

use std::collections::BTreeMap;

use nitrolean::check::ext::{ARRAY_OPS, BEQ_PROD, DEC_EQ_OPS, LIST_OPS, NAT_OPS};
use nitrolean::check::{Fingerprints, fingerprint_key, hex_digest};
use nitrolean::reader::read_file;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    assert!(
        !args.is_empty() && args.len() <= 32,
        "usage: fingerprints VERSION=EXPORT..."
    );
    // (key, digest) -> versions, as a bit mask over `args`.
    let mut table: BTreeMap<(String, String), u32> = BTreeMap::new();
    let mut versions = Vec::new();
    for (i, arg) in args.iter().enumerate() {
        let (version, path) = arg.split_once('=').expect("VERSION=EXPORT");
        versions.push(version.to_string());
        let (env, _) = read_file(path.as_ref()).unwrap_or_else(|e| panic!("{e}"));
        let fp = Fingerprints::new(&env);
        let mut seen = BTreeMap::new();
        let names = NAT_OPS
            .iter()
            .map(|x| x.0)
            .chain(ARRAY_OPS.iter().map(|x| x.0))
            .chain(LIST_OPS.iter().map(|x| x.0))
            .chain(DEC_EQ_OPS.iter().map(|x| x.0))
            .chain([BEQ_PROD]);
        for name in names {
            let n = env
                .names
                .find_dotted(name)
                .unwrap_or_else(|| panic!("{name} missing"));
            let mut stack = vec![n];
            while let Some(m) = stack.pop() {
                let k = fingerprint_key(&fp, m);
                if seen.contains_key(&k) {
                    continue;
                }
                let d = env.find(m).unwrap_or_else(|| panic!("{k} missing"));
                let digest = hex_digest(&fp.decl(d));
                seen.insert(k.clone(), ());
                *table.entry((k, digest)).or_default() |= 1 << i;
                fp.deps(d, &mut stack);
            }
        }
    }
    println!("//! Fingerprints of the prelude declarations with built-in operations and");
    println!("//! of everything they depend on, per Lean version. Written by");
    println!("//! `cargo run --release --example fingerprints -- VERSION=EXPORT...`");
    println!("//! (see `examples/fingerprints.rs`).");
    println!();
    println!("/// The Lean versions, in the order of the bits of `TABLE`'s masks.");
    println!("pub static VERSIONS: &[&str] = &[");
    for v in &versions {
        println!("    {v:?},");
    }
    println!("];");
    println!();
    println!("/// (key, digest, versions): sorted by key, then digest.");
    println!("pub static TABLE: &[(&str, &str, u32)] = &[");
    for ((k, v), m) in &table {
        println!("    ({k:?}, {v:?}, {m:#x}),");
    }
    println!("];");
}
