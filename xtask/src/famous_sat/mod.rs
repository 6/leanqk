//! `cargo xtask famous-sat`: kernel-only LRAT exports of cubes of famous
//! cube-and-conquer SAT proofs, and their measurement (bench/famous-sat).

mod fetch;
mod parallel;
mod pins;
mod report;
mod sat;
mod survey;
mod util;

use std::path::PathBuf;

use anyhow::Result;
use clap::Subcommand;

#[derive(clap::Args)]
pub struct Dirs {
    /// Sources, build trees and checker binaries (default: KC_CACHE, else
    /// bench/kernel-compute/cache).
    #[arg(long, value_name = "DIR")]
    cache: Option<PathBuf>,
    /// Generated exports and tables (default: KC_OUT, else
    /// bench/kernel-compute/out).
    #[arg(long, value_name = "DIR")]
    out: Option<PathBuf>,
}

#[derive(Subcommand)]
pub enum Cmd {
    /// Build the exports of bench/famous-sat/data/cubes.tsv into
    /// OUT/famous-sat/, with manifest.tsv (label, set, problem, cube,
    /// theorems, CNF bytes, LRAT bytes as stated, raw LRAT bytes as CaDiCaL
    /// wrote it, export bytes, CaDiCaL seconds). Needs git, curl, make, a C++
    /// compiler and elan.
    Fetch {
        #[command(flatten)]
        dirs: Dirs,
        /// Only these labels (and bundle sets), comma-separated.
        #[arg(long, value_delimiter = ',')]
        only: Vec<String>,
        /// Leave out the bundles.
        #[arg(long)]
        no_bundles: bool,
        /// Report a content hash that differs from its pin instead of
        /// stopping (also KC_UPDATE_PINS=1).
        #[arg(long)]
        update_pins: bool,
    },
    /// Check one export with 1, 2, 4, 8 and 12 threads (`nitrolean check
    /// --jobs N`), under a time and memory limit.
    Parallel {
        #[command(flatten)]
        dirs: Dirs,
        #[arg(long, value_delimiter = ',', default_values_t = [1, 2, 4, 8, 12])]
        jobs: Vec<usize>,
        #[arg(long, default_value_t = 3)]
        repeat: usize,
        #[arg(long, default_value_t = 600.0)]
        timeout: f64,
        #[arg(long, default_value_t = 16384)]
        mem_mib: i64,
        /// NITROLEAN_MEM_BUDGET_MIB for the runs (default: nitrolean's).
        #[arg(long)]
        mem_budget_mib: Option<u64>,
        /// The TSV (default OUT/famous-sat/parallel.tsv).
        #[arg(long)]
        tsv: Option<PathBuf>,
        export: PathBuf,
    },
    /// Solve a sample of cubes with a time limit and record their proof
    /// sizes (how data/cubes.tsv was chosen).
    Survey {
        cadical: PathBuf,
        formula: PathBuf,
        cubes: PathBuf,
        /// random:SEED:COUNT or a file of cube indices.
        picks: String,
        limit_s: u64,
        tsv: PathBuf,
        work: PathBuf,
    },
    /// The sample's share of each whole proof and the whole proof's time
    /// at nitrolean's rate, from `cargo xtask kc measure` TSVs.
    Coverage {
        manifest: PathBuf,
        survey: PathBuf,
        /// CACHE/famous-sat/src.
        src: PathBuf,
        measurements: Vec<PathBuf>,
    },
    /// Speedup per thread count from a `parallel` TSV.
    Scaling {
        tsv: PathBuf,
        decl_times: Option<PathBuf>,
    },
    /// A cube's subproblem: the formula and the cube's literals as units.
    CubeCnf {
        formula: PathBuf,
        cubes: PathBuf,
        index: usize,
        out: PathBuf,
    },
    /// Restrict a formula and trimmed proof to the clauses the proof uses.
    LratCore {
        cnf: PathBuf,
        lrat: PathBuf,
        cnf_out: PathBuf,
        lrat_out: PathBuf,
    },
    /// Rename the variables of a formula and proof to 1, 2, ...
    Renumber {
        cnf: PathBuf,
        lrat: PathBuf,
        cnf_out: PathBuf,
        lrat_out: PathBuf,
    },
}

pub fn main(c: Cmd) -> Result<()> {
    let dirs = |d: Dirs| pins::Dirs::new(d.cache, d.out);
    match c {
        Cmd::Fetch {
            dirs: d,
            only,
            no_bundles,
            update_pins,
        } => {
            let update_pins =
                update_pins || std::env::var("KC_UPDATE_PINS").is_ok_and(|v| v == "1");
            fetch::fetch(
                &dirs(d)?,
                &fetch::Opts {
                    only,
                    bundles: !no_bundles,
                    update_pins,
                },
            )
        }
        Cmd::Parallel {
            dirs: d,
            jobs,
            repeat,
            timeout,
            mem_mib,
            mem_budget_mib,
            tsv,
            export,
        } => parallel::parallel(
            &dirs(d)?,
            &parallel::Opts {
                jobs,
                repeat,
                timeout_s: timeout,
                mem_mib,
                mem_budget_mib,
                out: tsv,
                export,
            },
        ),
        Cmd::Survey {
            cadical,
            formula,
            cubes,
            picks,
            limit_s,
            tsv,
            work,
        } => survey::survey(&cadical, &formula, &cubes, &picks, limit_s, &tsv, &work),
        Cmd::Coverage {
            manifest,
            survey,
            src,
            measurements,
        } => report::coverage(&manifest, &survey, &src, &measurements),
        Cmd::Scaling { tsv, decl_times } => report::scaling(&tsv, decl_times.as_deref()),
        Cmd::CubeCnf {
            formula,
            cubes,
            index,
            out,
        } => sat::cube_cnf(&formula, &cubes, index, &out),
        Cmd::LratCore {
            cnf,
            lrat,
            cnf_out,
            lrat_out,
        } => sat::lrat_core(&cnf, &lrat, &cnf_out, &lrat_out),
        Cmd::Renumber {
            cnf,
            lrat,
            cnf_out,
            lrat_out,
        } => sat::renumber(&cnf, &lrat, &cnf_out, &lrat_out),
    }
}
