//! `cargo xtask perf-lines`: where a command's loads that missed L2 and its
//! mispredicted branches fall, by source line (the Mathlib benchmark's
//! profile step, bench/mathlib-ci/profile.sh), and `cargo xtask
//! perf-lines-test`: the same on a fake `perf`.
//!
//! Each event is first tried on its own, on a small command, at the most
//! precise level `perf record` takes: `:upp`, `:up`, then `:u`, whose
//! samples may land some instructions after the event (the report marks
//! those approximate). perf's error for each refused level goes to the
//! notes. The command is then recorded with every event that worked; if
//! perf refuses them together, with each one alone, keeping those that
//! record. Into `--raw`: the reports by source line (`report-NAME.txt`) and
//! by symbol and source line (`report-sym-NAME.txt`), a copy of the binary
//! (`bin-NAME`, for perf annotate), the notes (appended to
//! `record-notes.txt`) and a Markdown table of the 50 lines with the most
//! samples of the first event (`lines-NAME.md`).

use std::collections::HashMap;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use anyhow::{Context, Result, bail};

/// The events, without their level.
const EVENTS: [&str; 2] = ["mem_load_retired.l2_miss", "br_misp_retired.all_branches"];

/// The levels tried, most precise first.
const LEVELS: [&str; 3] = ["upp", "up", "u"];

/// Lines in the Markdown table.
const TOP: usize = 50;

/// Seconds a report by source line may take (reading the debug
/// information can stall), and one by symbol and source line.
const REPORT_SECS: u64 = 2400;
const SYM_REPORT_SECS: u64 = 1200;

/// Runs `cmd` with its standard output into `out` (standard error
/// discarded), killing it after `secs` seconds: whether it finished in time
/// and succeeded.
fn bounded(cmd: &mut Command, out: &Path, secs: u64) -> Result<bool> {
    let f = fs::File::create(out).with_context(|| format!("{}: cannot create", out.display()))?;
    let mut child = cmd
        .stdin(Stdio::null())
        .stdout(f)
        .stderr(Stdio::null())
        .spawn()
        .with_context(|| format!("cannot run {}", crate::util::describe(cmd)))?;
    let end = std::time::Instant::now() + std::time::Duration::from_secs(secs);
    loop {
        if let Some(st) = child.try_wait()? {
            return Ok(st.success());
        }
        if std::time::Instant::now() >= end {
            let _ = child.kill();
            let _ = child.wait();
            return Ok(false);
        }
        std::thread::sleep(std::time::Duration::from_millis(200));
    }
}

#[derive(clap::Args)]
pub struct Args {
    /// Directory for the reports, the notes and the table.
    #[arg(long)]
    raw: PathBuf,
    /// The run's name in the table's heading (its file names use it too).
    #[arg(long)]
    name: String,
    /// The binary whose lines are reported, copied into `--raw`.
    #[arg(long)]
    bin: Option<PathBuf>,
    /// One sample every this many events.
    #[arg(long, default_value_t = 20011)]
    period: u64,
    /// The perf program.
    #[arg(long, default_value = "perf")]
    perf: PathBuf,
    /// Directory to run the command in.
    #[arg(long)]
    dir: Option<PathBuf>,
    /// The command (program and arguments).
    #[arg(last = true, required = true)]
    cmd: Vec<String>,
}

pub fn main(a: Args) -> Result<()> {
    let mut a = a;
    fs::create_dir_all(&a.raw).with_context(|| format!("{}: cannot create", a.raw.display()))?;
    // Absolute: perf record runs in `--dir`, and its -o names a file here.
    a.raw =
        fs::canonicalize(&a.raw).with_context(|| format!("{}: cannot resolve", a.raw.display()))?;
    let tag = tag(&a.name);
    let mut notes = Vec::new();
    let events = probe(&a.perf, a.period, &a.raw, &mut notes)?;
    let mut reports = Vec::new();
    if events.is_empty() {
        notes.push(format!("{}: no event recorded (none was taken)", a.name));
    } else {
        reports = record_all(&a, &tag, &events, &mut notes)?;
    }
    let mut f = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(a.raw.join("record-notes.txt"))?;
    for n in &notes {
        writeln!(f, "{n}")?;
    }
    let md = a.raw.join(format!("lines-{tag}.md"));
    if reports.is_empty() {
        let _ = fs::remove_file(&md);
        return Ok(());
    }
    let mut counts = Counts::default();
    let mut recorded = Vec::new();
    for (evs, path) in &reports {
        let text = fs::read_to_string(path)?;
        counts.add(&text);
        recorded.extend(evs.iter().cloned());
    }
    fs::write(&md, table(&a.name, &recorded, &counts, a.period))?;
    if let Some(b) = &a.bin {
        fs::copy(b, a.raw.join(format!("bin-{tag}")))
            .with_context(|| format!("{}: cannot copy", b.display()))?;
    }
    Ok(())
}

/// A name as a file name part: lower case letters and digits, the rest `-`.
fn tag(name: &str) -> String {
    name.chars()
        .map(|c| {
            if c.is_ascii_lowercase() || c.is_ascii_digit() {
                c
            } else {
                '-'
            }
        })
        .collect()
}

/// The first three non-blank lines of perf's error output, on one line.
fn first_lines(err: &[u8]) -> String {
    let s = String::from_utf8_lossy(err);
    let v: Vec<&str> = s
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .take(3)
        .collect();
    let mut out = v.join(" ");
    if let Some((k, _)) = out.char_indices().nth(300) {
        out.truncate(k);
    }
    out
}

/// Each event at the most precise level perf takes on a small command.
fn probe(perf: &Path, period: u64, raw: &Path, notes: &mut Vec<String>) -> Result<Vec<String>> {
    let data = raw.join("perf-lines-probe.data");
    let mut out = Vec::new();
    for base in EVENTS {
        let mut taken = false;
        for lvl in LEVELS {
            let ev = format!("{base}:{lvl}");
            let o = Command::new(perf)
                .args(["record", "-q", "-e", &ev, "-c", &period.to_string(), "-o"])
                .arg(&data)
                .args([
                    "--",
                    "sh",
                    "-c",
                    "i=0; while [ $i -lt 200000 ]; do i=$((i+1)); done",
                ])
                .stdin(Stdio::null())
                .stdout(Stdio::null())
                .output()
                .with_context(|| format!("cannot run {}", perf.display()))?;
            if o.status.success() {
                out.push(ev);
                taken = true;
                break;
            }
            notes.push(format!(
                "perf record -e {ev} refused: {}",
                first_lines(&o.stderr)
            ));
        }
        if !taken {
            notes.push(format!("{base}: no level taken; left out"));
        }
    }
    let _ = fs::remove_file(&data);
    Ok(out)
}

/// Records the command with `events` together, or else with each alone;
/// gives each recording's events and its report by source line.
fn record_all(
    a: &Args,
    tag: &str,
    events: &[String],
    notes: &mut Vec<String>,
) -> Result<Vec<(Vec<String>, PathBuf)>> {
    if let Some(r) = record(a, tag, events, notes)? {
        return Ok(vec![(events.to_vec(), r)]);
    }
    let mut out = Vec::new();
    if events.len() > 1 {
        for (i, e) in events.iter().enumerate() {
            let one = std::slice::from_ref(e);
            if let Some(r) = record(a, &format!("{tag}-{i}"), one, notes)? {
                out.push((one.to_vec(), r));
            }
        }
    }
    Ok(out)
}

/// One recording of the command with `events`, reported by source line.
fn record(
    a: &Args,
    tag: &str,
    events: &[String],
    notes: &mut Vec<String>,
) -> Result<Option<PathBuf>> {
    let data = a.raw.join(format!("perf-{tag}.data"));
    let mut cmd = Command::new(&a.perf);
    cmd.args(["record", "-q"]);
    for e in events {
        cmd.args(["-e", e]);
    }
    cmd.args(["-c", &a.period.to_string(), "-o"])
        .arg(&data)
        .arg("--")
        .args(&a.cmd);
    if let Some(d) = &a.dir {
        cmd.current_dir(d);
    }
    let o = cmd
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .output()
        .with_context(|| format!("cannot run {}", a.perf.display()))?;
    if !o.status.success() {
        notes.push(format!(
            "{}: perf record -e {} failed: {}",
            a.name,
            events.join(","),
            first_lines(&o.stderr)
        ));
        let _ = fs::remove_file(&data);
        return Ok(None);
    }
    let report = a.raw.join(format!("report-{tag}.txt"));
    let mut by_line = Command::new(&a.perf);
    by_line.args(["report", "-i"]).arg(&data).args([
        "--stdio",
        "--no-children",
        "-n",
        "--sort",
        "srcline",
    ]);
    if !bounded(&mut by_line, &report, REPORT_SECS)? {
        notes.push(format!(
            "{}: perf report by source line failed or did not finish within {REPORT_SECS} s",
            a.name
        ));
        let _ = fs::remove_file(&report);
        return Ok(None);
    }
    let by_sym = a.raw.join(format!("report-sym-{tag}.txt"));
    let mut cmd = Command::new(&a.perf);
    cmd.args(["report", "-i"]).arg(&data).args([
        "--stdio",
        "--no-children",
        "-n",
        "--sort",
        "symbol,srcline",
        "--percent-limit",
        "0.05",
    ]);
    if !bounded(&mut cmd, &by_sym, SYM_REPORT_SECS)? {
        notes.push(format!(
            "{}: perf report by symbol and source line failed or did not finish within {SYM_REPORT_SECS} s",
            a.name
        ));
        let _ = fs::remove_file(&by_sym);
    }
    Ok(Some(report))
}

/// Samples by event and source line, from perf reports.
#[derive(Default)]
struct Counts {
    by: HashMap<(String, String), u64>,
}

impl Counts {
    /// Adds a report: sections headed `# Samples: N of event 'E'`, then
    /// lines `PCT SAMPLES WHERE`.
    fn add(&mut self, report: &str) {
        let mut ev = String::new();
        for l in report.lines() {
            if let Some(i) = l.find(" of event ") {
                if l.starts_with("# Samples") {
                    ev = l[i + " of event ".len()..]
                        .trim()
                        .trim_matches('\'')
                        .to_string();
                }
                continue;
            }
            if l.starts_with('#') || ev.is_empty() {
                continue;
            }
            let mut f = l.split_whitespace();
            let (Some(pct), Some(n)) = (f.next(), f.next()) else {
                continue;
            };
            let (true, Ok(n)) = (pct.ends_with('%'), n.parse::<u64>()) else {
                continue;
            };
            let at: Vec<&str> = f.collect();
            if at.is_empty() {
                continue;
            }
            *self.by.entry((ev.clone(), at.join(" "))).or_default() += n;
        }
    }

    fn get(&self, ev: &str, at: &str) -> u64 {
        self.by
            .get(&(ev.to_string(), at.to_string()))
            .copied()
            .unwrap_or(0)
    }
}

/// The Markdown table: the lines with the most samples of the first event,
/// in billions of events.
fn table(name: &str, events: &[String], c: &Counts, period: u64) -> String {
    let mut lines: Vec<(&str, u64)> =
        c.by.iter()
            .filter(|((e, _), _)| *e == events[0])
            .map(|((_, at), n)| (at.as_str(), *n))
            .collect();
    lines.sort_by(|x, y| y.1.cmp(&x.1).then(x.0.cmp(y.0)));
    let mut s = format!(
        "### {name} by source line (top {TOP} by the first event; billions of: {})\n\n",
        events.join(", ")
    );
    let rough: Vec<&str> = events
        .iter()
        .filter(|e| e.ends_with(":u"))
        .map(String::as_str)
        .collect();
    if !rough.is_empty() {
        s += &format!(
            "Approximate: {} sampled without precision (:u), so a sample's line may be some instructions after its event's.\n\n",
            rough.join(", ")
        );
    }
    s += &format!("| source line | {} |\n", events.join(" | "));
    s += &format!("|---|{}\n", "--:|".repeat(events.len()));
    for (at, _) in lines.iter().take(TOP) {
        s += &format!("| {at} |");
        for e in events {
            s += &format!(" {:.3} |", c.get(e, at) as f64 * period as f64 / 1e9);
        }
        s += "\n";
    }
    s + "\n"
}

/// When this program is called as `perf` (a link `perf-lines-test` makes),
/// it is a fake perf: `record` succeeds when every `-e` event is in
/// `FAKE_PERF_TAKES` (comma-separated), writing the events to its `-o`
/// file, and fails with perf's message otherwise (also, with
/// `FAKE_PERF_ONE` set, for more than one event at once); `report -i FILE` prints a
/// report with a section of two lines per event recorded.
pub fn fake_perf(args: &[String]) -> ! {
    let takes = std::env::var("FAKE_PERF_TAKES").unwrap_or_default();
    let takes: Vec<&str> = takes.split(',').filter(|s| !s.is_empty()).collect();
    let mut evs = Vec::new();
    let mut out = None;
    let mut input = None;
    let mut i = 2;
    while i < args.len() {
        match args[i].as_str() {
            "-e" => evs.push(args[i + 1].clone()),
            "-o" => out = Some(args[i + 1].clone()),
            "-i" => input = Some(args[i + 1].clone()),
            "--" => break,
            _ => {
                i += 1;
                continue;
            }
        }
        i += 2;
    }
    match args.get(1).map(String::as_str) {
        Some("record") => {
            if std::env::var_os("FAKE_PERF_ONE").is_some() && evs.len() > 1 {
                eprintln!("event syntax error: '{}'", evs.join(","));
                eprintln!("                     \\___ too many events at once");
                std::process::exit(129);
            }
            if let Some(e) = evs.iter().find(|e| !takes.contains(&e.as_str())) {
                eprintln!("event syntax error: '{e}'");
                eprintln!("                     \\___ unsupported in this machine");
                std::process::exit(129);
            }
            let _ = fs::write(out.expect("-o"), evs.join("\n"));
            std::process::exit(0);
        }
        Some("report") => {
            let evs = fs::read_to_string(input.expect("-i")).unwrap_or_default();
            for e in evs.lines() {
                println!("# Samples: 3  of event '{e}'");
                println!("#");
                println!("    66.67%             2  src/check/nbe/eval.rs:101");
                println!("    33.33%             1  src/expr.rs:7");
                println!();
            }
            std::process::exit(0);
        }
        _ => std::process::exit(2),
    }
}

/// Runs `perf-lines` on a fake perf in a temporary directory: every event
/// precise; the first refused at `:upp` and `:up` (taken at `:u`); the
/// second refused at every level; and both taken alone but not together.
/// Each with `--raw` relative to the caller and `--dir` another directory.
pub fn self_test() -> Result<()> {
    struct Case {
        name: &'static str,
        takes: String,
        one_at_a_time: bool,
        table: Vec<String>,
        rough: bool,
        notes: Vec<&'static str>,
    }
    let tmp = std::env::temp_dir().join(format!("perf-lines-test-{}", std::process::id()));
    let _ = fs::remove_dir_all(&tmp);
    fs::create_dir_all(&tmp)?;
    let perf = tmp.join("perf");
    std::os::unix::fs::symlink(std::env::current_exe()?, &perf)?;
    let (l2, br) = (EVENTS[0], EVENTS[1]);
    let cases = [
        Case {
            name: "precise",
            takes: format!("{l2}:upp,{br}:upp"),
            one_at_a_time: false,
            table: vec![format!("| source line | {l2}:upp | {br}:upp |")],
            rough: false,
            notes: vec![],
        },
        Case {
            name: "fallback",
            takes: format!("{l2}:u,{br}:upp"),
            one_at_a_time: false,
            table: vec![format!("| source line | {l2}:u | {br}:upp |")],
            rough: true,
            notes: vec![
                "-e mem_load_retired.l2_miss:upp refused: event syntax error",
                "l2_miss:up refused",
            ],
        },
        Case {
            name: "partial",
            takes: format!("{l2}:upp"),
            one_at_a_time: false,
            table: vec![format!("| source line | {l2}:upp |")],
            rough: false,
            notes: vec!["br_misp_retired.all_branches: no level taken"],
        },
        Case {
            name: "split",
            takes: format!("{l2}:upp,{br}:upp"),
            one_at_a_time: true,
            table: vec![format!("| source line | {l2}:upp | {br}:upp |")],
            rough: false,
            notes: vec!["failed: event syntax error"],
        },
    ];
    // `--raw` relative to the caller, the command run elsewhere (`--dir`),
    // as the profile step runs it.
    let elsewhere = tmp.join("elsewhere");
    fs::create_dir_all(&elsewhere)?;
    let mut failed = Vec::new();
    for c in &cases {
        let raw = tmp.join(c.name);
        let mut cmd = Command::new(std::env::current_exe()?);
        cmd.current_dir(&tmp)
            .args(["perf-lines", "--raw", c.name, "--dir"])
            .arg(&elsewhere)
            .args(["--name", c.name, "--period", "20000000", "--perf"])
            .arg(&perf)
            .args(["--", "true"])
            .env("FAKE_PERF_TAKES", &c.takes);
        if c.one_at_a_time {
            cmd.env("FAKE_PERF_ONE", "1");
        }
        let st = cmd.status()?;
        let md = fs::read_to_string(raw.join(format!("lines-{}.md", c.name))).unwrap_or_default();
        let notes = fs::read_to_string(raw.join("record-notes.txt")).unwrap_or_default();
        let cells = if c.table[0].matches('|').count() == 4 {
            "| 0.040 | 0.040 |"
        } else {
            "| 0.040 |"
        };
        let ok = st.success()
            && md.contains(&format!("| src/check/nbe/eval.rs:101 {cells}"))
            && c.table.iter().all(|w| md.contains(w.as_str()))
            && md.contains("Approximate") == c.rough
            && c.notes.iter().all(|w| notes.contains(w));
        println!(
            "perf-lines-test: {}: {}",
            c.name,
            if ok { "ok" } else { "FAILED" }
        );
        if !ok {
            println!("{md}\n{notes}");
            failed.push(c.name);
        }
    }
    let _ = fs::remove_dir_all(&tmp);
    if !failed.is_empty() {
        bail!("perf-lines-test: failed: {}", failed.join(", "));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn first_lines_cuts_at_a_character() {
        let err = "\u{e9}".repeat(400);
        let s = first_lines(err.as_bytes());
        assert_eq!(s.chars().count(), 300);
    }

    #[test]
    fn bounded_stops_a_stalled_command() {
        let out = std::env::temp_dir().join(format!("perf-lines-bounded-{}", std::process::id()));
        let t = std::time::Instant::now();
        let mut cmd = Command::new("sleep");
        cmd.arg("30");
        assert!(!bounded(&mut cmd, &out, 1).unwrap());
        assert!(t.elapsed() < std::time::Duration::from_secs(10));
        let mut cmd = Command::new("echo");
        cmd.arg("done");
        assert!(bounded(&mut cmd, &out, 10).unwrap());
        assert_eq!(fs::read_to_string(&out).unwrap(), "done\n");
        let _ = fs::remove_file(&out);
    }
}
