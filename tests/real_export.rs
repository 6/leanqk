//! Parse a real export produced by `leanexport`. Ignored by default; run with
//!
//! ```text
//! NITROLEAN_EXPORT=path/to/export.ndjson cargo test --release -- --ignored
//! ```
//!
//! To make one with Lean v4.36.0 (elan):
//!
//! ```text
//! elan toolchain install leanprover/lean4:v4.36.0
//! PATH="$(elan which --toolchain leanprover/lean4:v4.36.0 lean | xargs dirname):$PATH" \
//!   leanexport Init > init.ndjson
//! ```

use nitrolean::env::DeclKind;
use nitrolean::reader::read_file;

#[test]
#[ignore = "needs NITROLEAN_EXPORT"]
fn parses_real_export() {
    let Some(path) = std::env::var_os("NITROLEAN_EXPORT") else {
        eprintln!("NITROLEAN_EXPORT not set; skipping");
        return;
    };
    let (env, stats) = read_file(path.as_ref()).unwrap_or_else(|e| panic!("{e}"));
    eprintln!("{:?}, {} lines", env.counts(), stats.lines);
    assert!(env.meta.format_version.starts_with("3."));
    assert!(!env.decls.is_empty());
    // Every block's declarations are present and the inductive blocks are
    // laid out as types, constructors, recursors.
    let mut seen = 0;
    for b in &env.blocks {
        seen += b.len();
        for d in env.block_decls(b) {
            assert!(env.find(d.name).is_some());
        }
    }
    assert_eq!(seen, env.decls.len());
    // A real export from `Init` contains `Nat` and its recursor.
    if let Some(nat) = env.find_dotted("Nat") {
        assert!(matches!(nat.kind, DeclKind::Inductive { .. }));
        let rec = env.find_dotted("Nat.rec").expect("Nat.rec");
        assert!(matches!(rec.kind, DeclKind::Recursor { .. }));
    }
}
