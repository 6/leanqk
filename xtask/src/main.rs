//! The repository's tooling, run as `cargo xtask <command>` (see README.md).
#![allow(dead_code)] // TEMP while porting

mod arena;
mod ci;
mod corpus;
mod kc;
mod kernel_cases;
mod oracle;
mod proc;
mod public_check;
mod selfcheck;
mod util;

use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(name = "cargo xtask", about = "The repository's tooling", version)]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Check that the repository holds nothing that shouldn't be public.
    PublicCheck(public_check::Args),
    /// Test public-check on planted violations in a temporary repository.
    PublicCheckTest,
    /// Consistency checks of the correctness harness, without Lean or the corpus.
    Selfcheck,
    /// Run nitrolean on every export of the corpus and compare the verdicts.
    Corpus(corpus::RunArgs),
    /// Fetch the kernel-checker test corpus and export it as NDJSON.
    FetchCorpus(corpus::FetchArgs),
    /// Print or check the SHA-256 of every export of the corpus.
    CorpusChecksums(corpus::ChecksumArgs),
    /// Record Lean's verdict on every export of the corpus, and derive nitrolean's.
    LeanVerdicts(corpus::VerdictArgs),
    /// Check that the .olean reader gives the same environment as Lean's export.
    OleanEquivalence(corpus::OleanArgs),
    /// Install elan from its pinned release archive (for CI).
    InstallElan(ci::InstallElanArgs),
    /// Generate the kernel test cases under tests/kernel.
    KernelCases(kernel_cases::Args),
    /// The kernel-computation benchmarks (bench/kernel-compute).
    #[command(subcommand)]
    Kc(kc::Cmd),
    /// The Lean Kernel Arena benchmark (bench/arena).
    #[command(subcommand)]
    Arena(arena::Cmd),
    /// The per-declaration oracle against Lean's checker (bench/oracle).
    #[command(subcommand)]
    Oracle(oracle::Cmd),
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.first().and_then(|a| a.rsplit('/').next()) == Some("nitrolean") {
        selfcheck::fake_nitrolean(&args);
    }
    let cli = Cli::parse();
    let r = match cli.cmd {
        Cmd::PublicCheck(a) => public_check::main(a),
        Cmd::PublicCheckTest => public_check::self_test(),
        Cmd::Selfcheck => selfcheck::main(),
        Cmd::Corpus(a) => corpus::run_main(a),
        Cmd::FetchCorpus(a) => corpus::fetch_main(a),
        Cmd::CorpusChecksums(a) => corpus::checksums_main(a),
        Cmd::LeanVerdicts(a) => corpus::verdicts_main(a),
        Cmd::OleanEquivalence(a) => corpus::olean_main(a),
        Cmd::InstallElan(a) => ci::install_elan(a),
        Cmd::KernelCases(a) => kernel_cases::main(a),
        Cmd::Kc(c) => kc::main(c),
        Cmd::Arena(c) => arena::main(c),
        Cmd::Oracle(c) => oracle::main(c),
    };
    if let Err(e) = r {
        match e.downcast_ref::<util::Exit>() {
            Some(x) => {
                if !x.msg.is_empty() {
                    eprintln!("{}", x.msg);
                }
                std::process::exit(x.code);
            }
            None => {
                eprintln!("{e:#}");
                std::process::exit(1);
            }
        }
    }
}
