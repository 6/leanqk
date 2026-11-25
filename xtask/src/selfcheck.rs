//! `cargo xtask selfcheck`: consistency checks of the correctness harness
//! that need neither Lean nor the corpus: nothing private in the tree, the
//! verdict tables agree with each other and with corpus/divergences.md, and
//! the corpus runner classifies results correctly (on a fake checker).

use std::fs;
use std::path::Path;
use std::process::{Command, Stdio};

use anyhow::Result;

use crate::util::{exit_with, root};
use crate::{corpus, public_check};

fn fail(msg: impl std::fmt::Display) -> anyhow::Error {
    exit_with(1, format!("selfcheck: {msg}"))
}

/// The sorted first column of a TSV after its header.
fn ids(text: &str) -> Vec<String> {
    let mut v: Vec<String> = text
        .lines()
        .skip(1)
        .map(|l| l.split('\t').next().unwrap_or("").to_string())
        .collect();
    v.sort();
    v
}

pub fn main() -> Result<()> {
    let root = root();

    // Nothing private in the public tree, and (when origin/main is known) in
    // the messages of the commits on top of it.
    let have_main = Command::new("git")
        .arg("-C")
        .arg(&root)
        .args(["rev-parse", "-q", "--verify", "origin/main"])
        .stdout(Stdio::null())
        .status()?
        .success();
    let r = public_check::check(&root, have_main.then_some("origin/main..HEAD"))?;
    for e in &r.errors {
        eprintln!("public-check: {e}");
    }
    if !r.errors.is_empty() {
        eprintln!("public-check: {} violation(s)", r.errors.len());
        return Err(fail("public-check failed"));
    }
    println!("{}", r.ok_line);

    // Every test has an export checksum, a Lean verdict and a nitrolean verdict.
    let lean_tsv = "corpus/expected-lean-v4.36.0.tsv";
    let read = |p: &str| fs::read_to_string(root.join(p));
    let sums = read("corpus/exports.sha256")?;
    let mut ids_sums: Vec<String> = sums
        .lines()
        .map(|l| {
            let b = l.as_bytes();
            let hex = b.len() > 66
                && b[..64]
                    .iter()
                    .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(c))
                && &b[64..66] == b"  "
                && l.ends_with(".ndjson");
            if hex {
                l[66..l.len() - ".ndjson".len()].to_string()
            } else {
                l.to_string()
            }
        })
        .collect();
    ids_sums.sort();
    let lean_text = read(lean_tsv)?;
    let ids_lean = ids(&lean_text);
    let ids_nitrolean = ids(&read("corpus/expected-nitrolean.tsv")?);
    if ids_sums != ids_lean {
        return Err(fail(format!(
            "{lean_tsv} and corpus/exports.sha256 list different tests"
        )));
    }
    if ids_lean != ids_nitrolean {
        return Err(fail("the two expected-*.tsv list different tests"));
    }
    if ids_lean.windows(2).any(|w| w[0] == w[1]) {
        return Err(fail("duplicate test ids"));
    }
    let mut bad = false;
    for row in lean_text.lines().skip(1) {
        let f: Vec<&str> = if row.is_empty() {
            Vec::new()
        } else {
            row.split('\t').collect()
        };
        let ok = f.len() == 5
            && ["accept", "reject", "either"].contains(&f[2])
            && ["accept", "reject", "timeout", "error"].contains(&f[3]);
        if !ok {
            println!("selfcheck: bad row in '{lean_tsv}': {row}");
            bad = true;
        }
    }
    if bad {
        return Err(exit_with(1, ""));
    }
    corpus::expected_nitrolean(
        &root.join(lean_tsv),
        &root.join("corpus/divergences.md"),
        &root.join("corpus/expected-nitrolean.tsv"),
        true,
    )?;

    // Every source in the tables is described in corpus/SOURCES.md.
    let sources_md = read("corpus/SOURCES.md")?;
    let mut sources: Vec<&str> = lean_text
        .lines()
        .skip(1)
        .map(|l| l.split('\t').nth(1).unwrap_or(""))
        .collect();
    sources.sort();
    sources.dedup();
    for s in sources {
        let tag = format!("(`{s}`)");
        if !sources_md
            .lines()
            .any(|l| l.starts_with("## ") && l[3..].contains(&tag))
        {
            return Err(fail(format!(
                "source {s} is not described in corpus/SOURCES.md"
            )));
        }
    }

    // The runner, on a fake checker.
    let tmp = corpus::temp_path("selfcheck-", "");
    fs::create_dir_all(&tmp)?;
    let r = runner_self_test(&tmp);
    let _ = fs::remove_dir_all(&tmp);
    r?;

    println!("selfcheck: OK ({} tests)", ids_lean.len().max(1));
    Ok(())
}

fn runner_self_test(tmp: &Path) -> Result<()> {
    let c = tmp.join("c");
    fs::create_dir_all(c.join("t"))?;
    fs::write(
        c.join("manifest.tsv"),
        "id\tsource\texpected\ttimeout\torigin\nt/slow\tt\taccept\t1\t-\n",
    )?;
    let mut e = String::from("test_id\tverdict\tbasis\n");
    for t in [
        "good:accept",
        "bad:reject",
        "wrong:accept",
        "todo:accept",
        "todo2:reject",
        "declined:accept",
        "boom:reject",
        "slow:accept",
        "malformed:reject",
    ] {
        let (name, v) = t.split_once(':').unwrap();
        fs::write(c.join(format!("t/{name}.ndjson")), format!("{name}\n"))?;
        e.push_str(&format!("t/{name}\t{v}\tx\n"));
    }
    e.push_str("t/absent\taccept\tx\n");
    fs::write(tmp.join("e.tsv"), e)?;
    // The fake checker is this program, called as `nitrolean`.
    let fake = tmp.join("nitrolean");
    std::os::unix::fs::symlink(std::env::current_exe()?, &fake)?;

    let corpus_run = |extra: &[&str]| -> Result<(i32, String)> {
        let out = Command::new(std::env::current_exe()?)
            .arg("corpus")
            .arg("--nitrolean")
            .arg(&fake)
            .arg("--corpus")
            .arg(&c)
            .arg("--expected")
            .arg(tmp.join("e.tsv"))
            .args(extra)
            .env_remove("GITHUB_STEP_SUMMARY")
            .output()?;
        let text = String::from_utf8_lossy(&out.stdout).into_owned()
            + &String::from_utf8_lossy(&out.stderr);
        Ok((out.status.code().unwrap_or(-1), text))
    };
    // `tail -n +2 TSV | cut -f COLS | LC_ALL=C sort | tr '\t\n' ': '`
    let cols = |path: &Path, cols: &[usize]| -> Result<String> {
        let text = fs::read_to_string(path)?;
        let mut rows: Vec<String> = text
            .lines()
            .skip(1)
            .map(|l| {
                let f: Vec<&str> = l.split('\t').collect();
                cols.iter()
                    .map(|&i| f.get(i).copied().unwrap_or(""))
                    .collect::<Vec<_>>()
                    .join("\t")
            })
            .collect();
        rows.sort();
        Ok(rows
            .iter()
            .map(|r| format!("{} ", r.replace('\t', ":")))
            .collect())
    };

    let r_tsv = tmp.join("r.tsv");
    let (code, out) = corpus_run(&["--results", r_tsv.to_str().unwrap(), "-j", "4"])?;
    let got = cols(&r_tsv, &[0, 2]).unwrap_or_default();
    let want = "t/absent:missing t/bad:pass t/boom:crash t/declined:pending t/good:pass t/malformed:pass t/slow:timeout t/todo:pending t/todo2:pending t/wrong:fail ";
    if got != want || code != 1 {
        print!("{out}");
        return Err(fail(format!("runner self-test: got '{got}' (exit {code})")));
    }
    if !out.contains("10 tests: 3 pass, 3 pending, 1 fail, 1 crash, 1 timeout, 1 missing") {
        print!("{out}");
        return Err(fail("runner self-test: unexpected summary"));
    }
    if corpus_run(&["--filter", "good|bad|todo"])?.0 != 0 {
        return Err(fail("runner self-test: pending must not fail the run"));
    }
    if corpus_run(&["--filter", "todo", "--strict"])?.0 == 0 {
        return Err(fail("runner self-test: --strict must fail on pending"));
    }
    let p_tsv = tmp.join("p.tsv");
    let (code, _) = corpus_run(&[
        "--parse-only",
        "--filter",
        "good|bad|malformed|wrong",
        "--results",
        p_tsv.to_str().unwrap(),
    ])?;
    if code == 0 {
        return Err(fail("runner self-test: parse-only must fail on t/wrong"));
    }
    let got = cols(&p_tsv, &[0, 2, 3])?;
    if got
        != "t/bad:pass:parsed t/good:pass:parsed t/malformed:pass:malformed t/wrong:fail:malformed "
    {
        return Err(fail(format!("runner self-test: parse-only got '{got}'")));
    }
    Ok(())
}

/// When this program is called as `nitrolean` (a link the runner self-test
/// makes), it is a fake checker whose verdict is the content of its file.
pub fn fake_nitrolean(args: &[String]) -> ! {
    let read = |p: Option<&String>| {
        p.and_then(|p| fs::read_to_string(p).ok())
            .unwrap_or_default()
            .trim_end_matches('\n')
            .to_string()
    };
    if args.get(2).map(String::as_str) == Some("--parse-only") {
        let code = match read(args.get(3)).as_str() {
            "malformed" | "wrong" => 1,
            _ => 0,
        };
        std::process::exit(code);
    }
    let code = match read(args.get(2)).as_str() {
        "good" => 0,
        "bad" | "wrong" => 1,
        "todo" | "todo2" => {
            eprintln!("nitrolean: check: not implemented yet");
            1
        }
        "declined" => {
            eprintln!("nitrolean: declined");
            2
        }
        "malformed" => {
            eprintln!("nitrolean: malformed input");
            1
        }
        "boom" => {
            // SAFETY: plain libc calls; the default action ends the process.
            unsafe {
                libc::signal(libc::SIGSEGV, libc::SIG_DFL);
                libc::raise(libc::SIGSEGV);
            }
            1
        }
        "slow" => {
            std::thread::sleep(std::time::Duration::from_secs(30));
            0
        }
        _ => 0,
    };
    std::process::exit(code);
}
