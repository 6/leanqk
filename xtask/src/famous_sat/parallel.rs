//! `parallel`: nitrolean on one export with 1, 2, 4, 8 and 12 checking
//! threads (`--jobs`), under `crate::limited`'s time and memory limits.

use std::ffi::OsString;
use std::path::PathBuf;

use super::pins::Dirs;
use super::util::{Res, err, log, mkdir, write};

pub struct Opts {
    pub jobs: Vec<usize>,
    pub repeat: usize,
    pub timeout_s: f64,
    pub mem_mib: i64,
    /// NITROLEAN_MEM_BUDGET_MIB for the runs (none: nitrolean's default).
    pub mem_budget_mib: Option<u64>,
    pub out: Option<PathBuf>,
    pub export: PathBuf,
}

/// `nitrolean check --stats --jobs N` for each N, `repeat` times. Run 0, on
/// one thread, writes each declaration's check time to OUT.decl-times.tsv
/// (NITROLEAN_DECL_TIMES). Columns: export, jobs, mem_budget_mib, run,
/// verdict, wall_s, parse_s, check_s, peak_rss_mib.
pub fn parallel(d: &Dirs, o: &Opts) -> Res<()> {
    let bin = d.cache.join("bin/nitrolean");
    if !bin.is_file() {
        return err(format!(
            "{}: run cargo xtask kc build-checkers",
            bin.display()
        ));
    }
    let f = o.export.canonicalize()?;
    let name = f
        .file_stem()
        .unwrap_or_default()
        .to_string_lossy()
        .into_owned();
    let tsv = o
        .out
        .clone()
        .unwrap_or_else(|| d.out.join("famous-sat/parallel.tsv"));
    let decl_times = tsv.with_extension("decl-times.tsv");
    let logs = d.out.join("logs");
    mkdir(&logs)?;
    let budget = o
        .mem_budget_mib
        .map_or("default".to_string(), |b| b.to_string());
    // The children inherit these; set before any thread is started.
    if let Some(b) = o.mem_budget_mib {
        // SAFETY: this process has no other threads.
        unsafe { std::env::set_var("NITROLEAN_MEM_BUDGET_MIB", b.to_string()) };
    }
    let mut text = String::from(
        "export\tjobs\tmem_budget_mib\trun\tverdict\twall_s\tparse_s\tcheck_s\tpeak_rss_mib\n",
    );
    write(&tsv, &text)?;
    let mut one = |n: usize, run: usize| -> Res<()> {
        log(format!(
            "{name}: --jobs {n}, memory budget {budget} (run {run})"
        ));
        let logf = logs.join(format!("{name}.parallel.{budget}.{n}.{run}.log"));
        let cmd: Vec<OsString> = vec![
            bin.clone().into(),
            "check".into(),
            "--stats".into(),
            "--jobs".into(),
            n.to_string().into(),
            f.clone().into(),
        ];
        let out = crate::limited::run_limited(&cmd, &logf, o.timeout_s, o.mem_mib, None, false)?;
        let log_text = std::fs::read_to_string(&logf).unwrap_or_default();
        let v = match out.status.as_str() {
            "exited" if log_text.lines().any(|l| l.starts_with("accepted")) => "accepted",
            "exited" if log_text.lines().any(|l| l.starts_with("rejected")) => "rejected",
            "exited" => "error",
            s => s,
        };
        let secs = |key: &str| {
            log_text
                .lines()
                .find_map(|l| l.strip_prefix(key))
                .and_then(|r| r.split_whitespace().next().map(str::to_string))
                .unwrap_or_default()
        };
        text.push_str(&format!(
            "{name}\t{n}\t{budget}\t{run}\t{v}\t{:.2}\t{}\t{}\t{}\n",
            out.wall_s,
            secs("parse time"),
            secs("check time"),
            out.peak_mib
        ));
        write(&tsv, &text)
    };
    // SAFETY: as above.
    unsafe { std::env::set_var("NITROLEAN_DECL_TIMES", &decl_times) };
    one(1, 0)?;
    unsafe { std::env::remove_var("NITROLEAN_DECL_TIMES") };
    for r in 1..=o.repeat {
        for &n in &o.jobs {
            one(n, r)?;
        }
    }
    log(format!("wrote {}", tsv.display()));
    Ok(())
}
