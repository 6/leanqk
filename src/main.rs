use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Instant;

use clap::{Parser, Subcommand};

use leanqk::check::{self, FailKind};
use leanqk::reader::{self, ErrorClass, ReadError};
use leanqk::stats::{human_bytes, peak_rss_bytes};

const EXIT_STATUS: &str = "\
Exit status:
  0  accepted: every declaration type-checks (with --parse-only: the export
     parsed, and nothing was checked)
  1  rejected: a declaration does not check (the message names it and gives
     the reason), or the input is not a valid environment, including any
     malformed export (bad JSON, undefined or duplicate ids, missing fields,
     unknown record kinds, constants declared twice; the message gives the
     line)
  2  declined or usage error: bad arguments, an unreadable file, an export
     format version this checker does not support, or a resource limit hit
     while checking";

/// Lean quick kernel: an independent proof checker for Lean 4.
#[derive(Parser)]
#[command(name = "leanqk", version, about, after_help = EXIT_STATUS)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Check the declarations in an exported Lean 4 environment.
    #[command(after_help = EXIT_STATUS)]
    Check {
        /// NDJSON export (format 3.x, as written by `leanexport`); `-` reads
        /// standard input.
        file: PathBuf,
        /// Also print timings and peak memory.
        #[arg(long)]
        stats: bool,
        /// Stop after parsing and exit 0 if the export is well-formed.
        /// This does not type-check anything.
        #[arg(long)]
        parse_only: bool,
    },
}

const ACCEPTED: u8 = 0;
const REJECTED: u8 = 1;
const DECLINED: u8 = 2;

fn main() -> ExitCode {
    match Cli::parse().command {
        Command::Check {
            file,
            stats,
            parse_only,
        } => ExitCode::from(check(&file, stats, parse_only)),
    }
}

fn check(file: &Path, show_stats: bool, parse_only: bool) -> u8 {
    let t0 = Instant::now();
    let res = if file.as_os_str() == "-" {
        reader::read_stdin()
    } else {
        reader::read_file(file)
    };
    let elapsed = t0.elapsed();
    let (env, rs) = match res {
        Ok(x) => x,
        Err(e) => return report_error(file, &e),
    };
    let c = env.counts();
    let mut out = String::new();
    let m = &env.meta;
    out.push_str(&format!("format {}", m.format_version));
    if let (Some(n), Some(v)) = (&m.exporter_name, &m.exporter_version) {
        out.push_str(&format!(", exporter {n} {v}"));
    }
    if let Some(v) = &m.lean_version {
        out.push_str(&format!(", Lean {v}"));
    }
    out.push('\n');
    out.push_str(&format!("declarations  {}\n", env.decls.len()));
    for (k, n) in [
        ("axioms", c.axioms),
        ("definitions", c.definitions),
        ("theorems", c.theorems),
        ("opaques", c.opaques),
        ("quotients", c.quotients),
        ("inductives", c.inductives),
        ("constructors", c.constructors),
        ("recursors", c.recursors),
    ] {
        out.push_str(&format!("  {k:<14}{n}\n"));
    }
    out.push_str(&format!(
        "names {}, levels {}, expressions {}, strings {}\n",
        env.names.len(),
        env.levels.len(),
        env.exprs.len(),
        env.names.strings.len(),
    ));
    if show_stats {
        let secs = elapsed.as_secs_f64();
        let mibs = rs.bytes as f64 / (1024.0 * 1024.0) / secs.max(1e-9);
        out.push_str(&format!(
            "parse time    {secs:.3} s ({} lines, {}, {mibs:.0} MiB/s)\n",
            rs.lines,
            human_bytes(rs.bytes)
        ));
        match peak_rss_bytes() {
            Some(b) => out.push_str(&format!("peak RSS      {}\n", human_bytes(b))),
            None => out.push_str("peak RSS      unavailable on this platform\n"),
        }
        out.push_str(&format!(
            "arena heap    {} (id maps {})\n",
            human_bytes(env.heap_bytes() as u64),
            human_bytes(rs.id_map_bytes as u64)
        ));
    }
    if parse_only {
        // A closed stdout (e.g. piped to `head`) does not change the verdict.
        let _ = io::stdout().lock().write_all(out.as_bytes());
        return ACCEPTED;
    }
    let _ = io::stdout().lock().write_all(out.as_bytes());
    let t1 = Instant::now();
    let res = check::check_env(&env);
    let secs = t1.elapsed().as_secs_f64();
    let mut out = String::new();
    let code = match res {
        Ok(rep) => {
            if show_stats {
                for n in &rep.notes {
                    out.push_str(&format!("note: {n}\n"));
                }
            }
            out.push_str(&format!(
                "accepted: {} declarations checked\n",
                rep.declarations
            ));
            ACCEPTED
        }
        Err(f) => {
            let (verdict, code) = match f.kind {
                FailKind::Rejected => ("rejected", REJECTED),
                FailKind::Resource => ("declined", DECLINED),
            };
            if f.decl.is_empty() {
                eprintln!("leanqk: {verdict}: {}", f.msg);
            } else {
                eprintln!("leanqk: {verdict}: declaration '{}': {}", f.decl, f.msg);
            }
            code
        }
    };
    if show_stats {
        out.push_str(&format!("check time    {secs:.3} s\n"));
        if let Some(b) = peak_rss_bytes() {
            out.push_str(&format!("peak RSS      {}\n", human_bytes(b)));
        }
    }
    let _ = io::stdout().lock().write_all(out.as_bytes());
    code
}

fn report_error(file: &Path, e: &ReadError) -> u8 {
    let code = match e.class {
        ErrorClass::Rejected | ErrorClass::Malformed => REJECTED,
        ErrorClass::Unsupported | ErrorClass::Io => DECLINED,
    };
    let verdict = if code == REJECTED {
        "rejected"
    } else {
        "error"
    };
    if e.class == ErrorClass::Io {
        eprintln!("leanqk: {verdict}: {e}");
    } else {
        eprintln!("leanqk: {verdict}: {}: {e}", file.display());
    }
    code
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
