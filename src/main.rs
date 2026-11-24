use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, Subcommand};

/// Lean quick kernel: an independent proof checker for Lean 4.
#[derive(Parser)]
#[command(name = "leanqk", version, about)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Check the declarations in an exported Lean 4 environment.
    Check {
        /// File to check.
        file: PathBuf,
    },
}

fn main() -> ExitCode {
    match Cli::parse().command {
        Command::Check { file } => {
            eprintln!("leanqk: check {}: not implemented yet", file.display());
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Cli;
    use clap::CommandFactory;

    #[test]
    fn cli_is_well_formed() {
        Cli::command().debug_assert();
    }
}
