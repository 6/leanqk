//! Print `src/check/fingerprint_table.rs` from an export of Lean's prelude:
//! the fingerprint of each operation with built-in `Nat` arithmetic and
//! of every declaration it depends on.
//!
//! ```text
//! cargo run --release --example fingerprints -- init.ndjson > src/check/fingerprint_table.rs
//! ```

use std::collections::BTreeMap;

use nitrolean::check::ext::NAT_OPS;
use nitrolean::check::{Fingerprints, fingerprint_key, hex_digest};
use nitrolean::reader::read_file;

fn main() {
    let path = std::env::args().nth(1).expect("usage: fingerprints EXPORT");
    let (env, _) = read_file(path.as_ref()).unwrap_or_else(|e| panic!("{e}"));
    let fp = Fingerprints::new(&env);
    let mut table = BTreeMap::new();
    for (name, _) in NAT_OPS {
        let n = env
            .names
            .find_dotted(name)
            .unwrap_or_else(|| panic!("{name} missing"));
        let mut stack = vec![n];
        while let Some(m) = stack.pop() {
            let k = fingerprint_key(&fp, m);
            if table.contains_key(&k) {
                continue;
            }
            let d = env.find(m).unwrap_or_else(|| panic!("{k} missing"));
            table.insert(k, hex_digest(&fp.decl(d)));
            fp.deps(d, &mut stack);
        }
    }
    println!("//! Fingerprints of the prelude declarations with built-in arithmetic and");
    println!("//! of everything they depend on, from Lean v4.36.0. Written by");
    println!("//! `cargo run --release --example fingerprints -- init.ndjson`.");
    println!();
    println!("pub static TABLE: &[(&str, &str)] = &[");
    for (k, v) in &table {
        println!("    ({k:?}, {v:?}),");
    }
    println!("];");
}
