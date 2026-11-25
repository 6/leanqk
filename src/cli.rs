use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Instant;

use clap::{Parser, Subcommand};

use crate::check::{self, FailKind};
use crate::reader::{self, ErrorClass, ReadError};
use crate::stats::{human_bytes, peak_rss_bytes};
use crate::{compare, olean};

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

/// nitrolean: an independent Lean 4 proof checker.
#[derive(Parser)]
#[command(name = "nitrolean", version, about, after_help = EXIT_STATUS)]
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
        /// Read Lean's compiled .olean files instead of an export: FILE is a
        /// module name (e.g. `Mathlib`), an .olean file, or a Lake project
        /// directory (every module it built). Imports are found in
        /// --search-path, the project's packages, LEAN_PATH and the library
        /// of the `lean` on PATH.
        #[arg(long)]
        olean: bool,
        /// Directory to search for imported modules (repeatable).
        #[arg(long, value_name = "DIR")]
        search_path: Vec<PathBuf>,
        /// Threads for loading .olean files (default: all cores).
        #[arg(long, default_value_t = 0)]
        threads: usize,
        /// Threads for checking declarations (default: NITROLEAN_JOBS, else
        /// all cores). The verdict does not depend on it.
        #[arg(long, short = 'j', default_value_t = 0)]
        jobs: usize,
        /// With --olean and a project: load this module (repeatable)
        /// instead of the project's top-level modules.
        #[arg(long, value_name = "MODULE")]
        module: Vec<String>,
    },
    /// Compare an NDJSON export with the environment loaded from .olean
    /// files: every exported declaration must be in the oleans with the
    /// same type, value and other fields (up to binder names and
    /// annotations, and mdata). Exit 0 if so, 1 if not, 2 on errors.
    Compare {
        /// NDJSON export.
        export: PathBuf,
        /// Module name, .olean file or Lake project, as for `check --olean`.
        target: String,
        /// Directory to search for imported modules (repeatable).
        #[arg(long, value_name = "DIR")]
        search_path: Vec<PathBuf>,
        /// Threads for loading .olean files (default: all cores).
        #[arg(long, default_value_t = 0)]
        threads: usize,
        /// How many names to list per kind of difference.
        #[arg(long, default_value_t = 20)]
        show: usize,
    },
}

fn compare(export: &Path, target: &str, opts: &olean::Options, show: usize) -> u8 {
    let start = Instant::now();
    let a = match reader::read_file(export) {
        Ok((env, _)) => env,
        Err(e) => {
            report_error(export, &e);
            return DECLINED;
        }
    };
    let export_read = Instant::now();
    let b = match olean::load(target, opts) {
        Ok((env, _)) => env,
        Err(e) => {
            eprintln!("nitrolean: {e}");
            return DECLINED;
        }
    };
    let oleans_loaded = Instant::now();
    let d = compare::compare(&a, &b);
    let compared = Instant::now();
    let mut out = String::new();
    out.push_str(&format!(
        "export {} declarations ({:.2} s), oleans {} declarations ({:.2} s), compared in {:.2} s\n",
        a.decls.len(),
        (export_read - start).as_secs_f64(),
        b.decls.len(),
        (oleans_loaded - export_read).as_secs_f64(),
        (compared - oleans_loaded).as_secs_f64(),
    ));
    out.push_str(&format!(
        "identical     {}\n",
        d.common - d.differ.len() - d.later_copy.len()
    ));
    out.push_str(&format!(
        "identical to a later copy  {} (theorems with a proof in several modules)\n",
        d.later_copy.len()
    ));
    for n in d.later_copy.iter().take(show) {
        out.push_str(&format!("  {n}\n"));
    }
    out.push_str(&format!("different     {}\n", d.differ.len()));
    for (n, f) in d.differ.iter().take(show) {
        out.push_str(&format!("  {n}: {f}\n"));
    }
    out.push_str(&format!("only export   {}\n", d.only_a.len()));
    for n in d.only_a.iter().take(show) {
        out.push_str(&format!("  {n}\n"));
    }
    out.push_str(&format!("only oleans   {}\n", d.only_b.len()));
    let mut cats: Vec<&str> = d.only_b.iter().map(|x| x.1).collect();
    cats.sort();
    cats.dedup();
    for c in cats {
        let ns: Vec<&String> = d.only_b.iter().filter(|x| x.1 == c).map(|x| &x.0).collect();
        out.push_str(&format!("  {c}: {}\n", ns.len()));
        for n in ns.iter().take(show) {
            out.push_str(&format!("    {n}\n"));
        }
    }
    let _ = io::stdout().lock().write_all(out.as_bytes());
    if d.a_matches() { ACCEPTED } else { REJECTED }
}

const ACCEPTED: u8 = 0;
const REJECTED: u8 = 1;
const DECLINED: u8 = 2;

/// The command-line program, shared by the `nitrolean` and `nlean`
/// binaries: parses the process arguments, runs the command and returns
/// its exit status.
pub fn main() -> ExitCode {
    match Cli::parse().command {
        Command::Check {
            file,
            stats,
            parse_only,
            olean,
            search_path,
            threads,
            jobs,
            module,
        } => {
            let src = if olean {
                Source::Olean(olean::Options {
                    search_path,
                    threads,
                    no_toolchain: false,
                    modules: module,
                    // An experiment for measuring load times: the checker
                    // cannot use such an environment yet.
                    lazy_proofs: parse_only && std::env::var_os("NITROLEAN_LAZY_PROOFS").is_some(),
                })
            } else {
                Source::Export
            };
            let jobs = if jobs == 0 {
                check::default_jobs()
            } else {
                jobs
            };
            ExitCode::from(check(&file, &src, stats, parse_only, jobs))
        }
        Command::Compare {
            export,
            target,
            search_path,
            threads,
            show,
        } => ExitCode::from(compare(
            &export,
            &target,
            &olean::Options {
                search_path,
                threads,
                ..Default::default()
            },
            show,
        )),
    }
}

enum Source {
    Export,
    Olean(olean::Options),
}

fn check(file: &Path, src: &Source, show_stats: bool, parse_only: bool, jobs: usize) -> u8 {
    let start = Instant::now();
    let opts = match src {
        Source::Export => None,
        Source::Olean(o) => Some(o),
    };
    let (env, rs, os) = if let Some(opts) = opts {
        match olean::load(&file.to_string_lossy(), opts) {
            Ok((env, st)) => (env, None, Some(st)),
            Err(e) => {
                eprintln!("nitrolean: {e}");
                return match e.class {
                    ErrorClass::Rejected => REJECTED,
                    _ => DECLINED,
                };
            }
        }
    } else {
        let res = if file.as_os_str() == "-" {
            reader::read_stdin()
        } else {
            reader::read_file(file)
        };
        match res {
            Ok((env, rs)) => (env, Some(rs), None),
            Err(e) => return report_error(file, &e),
        }
    };
    let elapsed = start.elapsed();
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
        if let Some(rs) = &rs {
            let mibs = rs.bytes as f64 / (1024.0 * 1024.0) / secs.max(1e-9);
            out.push_str(&format!(
                "parse time    {secs:.3} s ({} lines, {}, {mibs:.0} MiB/s)\n",
                rs.lines,
                human_bytes(rs.bytes)
            ));
        }
        if let Some(st) = &os {
            out.push_str(&format!(
                "load time     {secs:.3} s ({} modules, {} files, {}, {} threads; imports {:.3} s, ordering {:.3} s, arenas {:.3} s)\n",
                st.modules,
                st.files,
                human_bytes(st.bytes),
                st.threads,
                st.imports_time.as_secs_f64(),
                st.intern_time.as_secs_f64(),
                st.finish_time.as_secs_f64(),
            ));
        }
        match peak_rss_bytes() {
            Some(b) => out.push_str(&format!("peak RSS      {}\n", human_bytes(b))),
            None => out.push_str("peak RSS      unavailable on this platform\n"),
        }
        out.push_str(&format!(
            "arena heap    {} (id maps {})\n",
            human_bytes(env.heap_bytes() as u64),
            human_bytes(rs.as_ref().map_or(0, |r| r.id_map_bytes) as u64)
        ));
    }
    if parse_only {
        // A closed stdout (e.g. piped to `head`) does not change the verdict.
        let _ = io::stdout().lock().write_all(out.as_bytes());
        return ACCEPTED;
    }
    let _ = io::stdout().lock().write_all(out.as_bytes());
    let start = Instant::now();
    let res = check::check_env_jobs(&env, jobs);
    let secs = start.elapsed().as_secs_f64();
    let mut out = String::new();
    let code = match res {
        Ok(rep) => {
            if show_stats {
                for n in &rep.notes {
                    out.push_str(&format!("note: {n}\n"));
                }
                out.push_str(&format!("{}\n", check::eval_stats()));
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
                eprintln!("nitrolean: {verdict}: {}", f.msg);
            } else {
                eprintln!("nitrolean: {verdict}: declaration '{}': {}", f.decl, f.msg);
            }
            code
        }
    };
    if show_stats {
        out.push_str(&format!("check time    {secs:.3} s ({jobs} threads)\n"));
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
        eprintln!("nitrolean: {verdict}: {e}");
    } else {
        eprintln!("nitrolean: {verdict}: {}: {e}", file.display());
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
