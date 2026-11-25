//! `matcert`: makes the MatCert matrix certificates, states and exports them as Lean
//! theorems, runs the checkers on them and tabulates the results.
//!
//! ```text
//! matcert gen inverse P N SEED OUT [--corrupt]
//! matcert gen nonsingular N BOUND SEED OUT [--corrupt]
//! matcert exports [--out DIR] [--cache DIR] [--only LABEL,...] [--update-pins]
//! matcert measure [--out DIR] [--cache DIR] [--only LABEL,...] [measure.sh options...]
//! matcert table MEASUREMENTS.tsv MANIFEST.tsv
//! ```
//!
//! `gen` writes one certificate (see `certgen.rs`). `exports` does it for every row of
//! `data/certificates.tsv`, checks the pinned SHA-256, states the certificate with the
//! `mat_cert` command of the Lean package and exports the theorem's closure with the
//! lean4export of the toolchain. `measure` runs `bench/kernel-compute/measure.sh` on the
//! exports. `table` prints the measurements as a Markdown table, one row per export and one
//! column per checker. `--help` on a subcommand prints the details.

mod certgen;
mod exports;
mod table;

use std::process::ExitCode;

const USAGE: &str = "usage:
  matcert gen inverse P N SEED OUT [--corrupt]
  matcert gen nonsingular N BOUND SEED OUT [--corrupt]
  matcert exports [--out DIR] [--cache DIR] [--only LABEL,...] [--update-pins]
  matcert measure [--out DIR] [--cache DIR] [--only LABEL,...] [measure.sh options...]
  matcert table MEASUREMENTS.tsv MANIFEST.tsv";

fn num<T: std::str::FromStr>(s: &str) -> Result<T, String> {
    s.parse().map_err(|_| format!("not a number: {s}"))
}

fn gen_cmd(args: &[String]) -> Result<(), String> {
    let mut args = args.to_vec();
    let corrupt = args.last().is_some_and(|a| a == "--corrupt");
    if corrupt {
        args.pop();
    }
    let (mut cert, out) = match args.as_slice() {
        [k, p, n, seed, out] if k == "inverse" => {
            (certgen::inverse(num(p)?, num(n)?, num(seed)?)?, out)
        }
        [k, n, b, seed, out] if k == "nonsingular" => {
            (certgen::nonsingular(num(n)?, num(b)?, num(seed)?)?, out)
        }
        _ => return Err(gen_help().into()),
    };
    if corrupt {
        cert.corrupt();
    }
    std::fs::write(out, cert.render()).map_err(|e| format!("{out}: {e}"))
}

fn gen_help() -> &'static str {
    "usage: matcert gen inverse P N SEED OUT [--corrupt]
       matcert gen nonsingular N BOUND SEED OUT [--corrupt]

inverse:     a pseudo-random N x N matrix A with entries in [0, P) and its inverse B modulo
             the prime P (Gauss-Jordan elimination mod P), so that A * B = 1 (mod P).
nonsingular: a pseudo-random N x N integer matrix A with entries in [-BOUND, BOUND], its
             determinant d and its adjugate B (fraction-free Gauss-Jordan elimination), so
             that A * B = d * 1 over the integers, d != 0.
--corrupt:   add 1 to the last entry of B after checking (a wrong certificate).

The entries come from splitmix64 seeded with SEED, so the output depends only on the
arguments; a seed whose matrix is singular is refused. The certificate is checked by
multiplying it out before it is written. Output: a header line `inverse P N` or
`nonsingular N D`, then the N rows of A and the N rows of B, one row per line, entries
separated by single spaces."
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let help = args.iter().any(|a| a == "-h" || a == "--help");
    let r = match args.first().map(String::as_str) {
        Some("gen") if help => {
            println!("{}", gen_help());
            Ok(())
        }
        Some("gen") => gen_cmd(&args[1..]),
        Some("exports") => exports::exports(&args[1..]),
        Some("measure") => exports::measure(&args[1..]),
        Some("table") => table::table(&args[1..]),
        _ => Err(USAGE.into()),
    };
    match r {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("matcert: {e}");
            ExitCode::FAILURE
        }
    }
}
