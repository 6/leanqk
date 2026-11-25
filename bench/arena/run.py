#!/usr/bin/env python3
"""Run checkers on the Lean Kernel Arena's test set, the way the arena does.

  run.py run [options]            check every export, append rows to a TSV
  run.py report TSV... [options]  print a Markdown table of results

The arena calls a checker as a shell command (`sh -c CMD`) with the export's
path in $IN, and reads its verdict from the exit code alone: 0 accepted,
1 rejected, 2 declined, anything else an error; past the test's timeout it is
killed and the run counts as a timeout (scored like an error). A verdict is
correct when it matches the test's expected outcome (`accept` or `reject`);
tests whose outcome is `either` accept both verdicts. This runner does the
same, and measures each run as the arena does with GNU time: wall time, CPU
time (user + system, of the command and every child it waited for) and peak
resident memory, all from wait4(2).

Checkers (`--checker NAME`, repeatable; default: nitrolean):

  nitrolean   nitrolean check "$IN"        (--nitrolean PATH; default
              target/release/nitrolean, else `nitrolean` on PATH)
  official    leanchecker --from-export "$IN", Lean's own checker; the arena
              uses Lean v4.35.0's ($LEANCHECKER, else that toolchain's from
              elan, else `leanchecker` on PATH)
  gruszka     scripts/arena-run "$IN" 4, in a built checkout ($GRUSZKA_DIR)
  nano-lean   target/release/nl-fast -q -j 4 "$IN", in a built checkout
              ($NANO_LEAN_DIR), else `nl-fast` on PATH
  NAME=CMD    any other command, run with $IN set

--competitors adds official, gruszka and nano-lean where they are installed
and skips the others with a note.
"""

import argparse
import fnmatch
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
COLUMNS = ["checker", "test", "group", "expected", "status", "correctness", "exit_code",
           "wall_s", "cpu_s", "max_rss_mib", "ginstructions", "timeout_s", "note"]
COMPETITORS = ["official", "gruszka", "nano-lean"]
OFFICIAL_TOOLCHAIN = "leanprover--lean4---v4.35.0"


def read_tsv(path: Path) -> list[dict]:
    lines = path.read_text(encoding="utf-8").splitlines()
    head = lines[0].split("\t")
    return [dict(zip(head, line.split("\t"))) for line in lines[1:] if line]


def resolve_checker(spec: str, nitrolean: str | None) -> tuple[str, str, Path | None] | str:
    """(name, command, cwd), or a string saying why the checker is unavailable."""
    if "=" in spec:
        name, cmd = spec.split("=", 1)
        return name, cmd, None
    if spec == "nitrolean":
        exe = nitrolean or (str(ROOT / "target/release/nitrolean")
                            if (ROOT / "target/release/nitrolean").exists() else shutil.which("nitrolean"))
        if not exe:
            return "nitrolean not found (cargo build --release, or pass --nitrolean)"
        return "nitrolean", f'{sh_quote(exe)} check "$IN"', None
    if spec == "official":
        exe = os.environ.get("LEANCHECKER")
        if not exe:
            elan_home = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan"))
            cand = elan_home / "toolchains" / OFFICIAL_TOOLCHAIN / "bin" / "leanchecker"
            exe = str(cand) if cand.exists() else shutil.which("leanchecker")
        if not exe:
            return ("leanchecker not found (elan toolchain install leanprover/lean4:v4.35.0, "
                    "or set LEANCHECKER)")
        return "official", f'{sh_quote(exe)} --from-export "$IN"', None
    if spec == "gruszka":
        d = os.environ.get("GRUSZKA_DIR")
        if not d or not (Path(d) / "scripts/arena-run").exists():
            return "gruszka not found (set GRUSZKA_DIR to a built checkout)"
        return "gruszka", 'scripts/arena-run "$IN" 4', Path(d)
    if spec == "nano-lean":
        d = os.environ.get("NANO_LEAN_DIR")
        if d and (Path(d) / "target/release/nl-fast").exists():
            return "nano-lean", 'target/release/nl-fast -q -j 4 "$IN"', Path(d)
        exe = shutil.which("nl-fast")
        if not exe:
            return "nano-lean not found (set NANO_LEAN_DIR to a built checkout)"
        return "nano-lean", f'{sh_quote(exe)} -q -j 4 "$IN"', None
    return f"unknown checker {spec} (use NAME=CMD for others)"


def sh_quote(s: str) -> str:
    return "'" + s.replace("'", "'\\''") + "'"


def gnu_time() -> str | None:
    """GNU time, which the arena measures peak memory with. A process forked
    from Python starts with Python's resident pages counted in its peak, so
    without it the peak of a small run reads some 20 MiB too high."""
    exe = shutil.which("time") or ("/usr/bin/time" if Path("/usr/bin/time").exists() else None)
    if not exe:
        return None
    r = subprocess.run([exe, "--version"], capture_output=True, text=True)
    return exe if "GNU" in r.stdout + r.stderr else None


GNU_TIME = gnu_time()


def perf_ok() -> bool:
    """Whether `perf stat` can count instructions here, as the arena does when
    it ranks checkers (by Mathlib's instruction count)."""
    if not shutil.which("perf"):
        return False
    r = subprocess.run(["perf", "stat", "-x,", "-e", "instructions", "--", "true"],
                       capture_output=True, text=True)
    return r.returncode == 0 and "not supported" not in r.stderr and "<not" not in r.stderr


PERF = perf_ok()


def run_one(cmd: str, export: Path, cwd: Path | None, timeout: float | None) -> dict:
    env = dict(os.environ, IN=str(export))
    with tempfile.TemporaryFile() as err, tempfile.NamedTemporaryFile("r") as tf, \
            tempfile.NamedTemporaryFile("r") as pf:
        argv = ["sh", "-c", cmd]
        if GNU_TIME:
            argv = [GNU_TIME, "-q", "-f", "%M", "-o", tf.name, "--"] + argv
        if PERF:
            argv = ["perf", "stat", "-x,", "-e", "instructions", "-o", pf.name, "--"] + argv
        start = time.monotonic()
        proc = subprocess.Popen(argv, cwd=cwd, env=env, stdin=subprocess.DEVNULL,
                                stdout=subprocess.DEVNULL, stderr=err, start_new_session=True)
        timed_out = threading.Event()

        def kill():
            timed_out.set()
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass

        timer = threading.Timer(timeout, kill) if timeout else None
        if timer:
            timer.start()
        _, status, ru = os.wait4(proc.pid, 0)
        wall = time.monotonic() - start
        if timer:
            timer.cancel()
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        proc.returncode = os.waitstatus_to_exitcode(status)
        err.seek(0)
        stderr = err.read(1 << 16).decode("utf-8", "replace")
        maxrss_kib = ru.ru_maxrss
        if GNU_TIME:
            try:
                maxrss_kib = int(tf.read().split()[-1])
            except (ValueError, IndexError):
                pass
        instructions = ""
        if PERF:
            for line in pf.read().splitlines():
                f = line.split(",")
                if len(f) > 2 and f[2].startswith("instructions") and f[0].isdigit():
                    # In billions, as a long bare count reads like an id.
                    instructions = f"{int(f[0]) / 1e9:.3f}"
    code = proc.returncode
    if timed_out.is_set():
        verdict = "timeout"
    else:
        verdict = {0: "accepted", 1: "rejected", 2: "declined"}.get(code, "error")
    note = next((ln.strip() for ln in stderr.splitlines() if ln.strip()), "")
    note = note.replace(str(export), "$IN")
    # Long digit runs (hygiene hashes in names) are noise and read like ids.
    note = re.sub(r"\d{9,}", "#", note)
    return {"status": verdict, "exit_code": code, "wall_s": f"{wall:.3f}",
            "cpu_s": f"{ru.ru_utime + ru.ru_stime:.3f}",
            "max_rss_mib": f"{maxrss_kib / 1024:.1f}", "ginstructions": instructions, "note": " ".join(note.split())[:160]}


def correctness(expected: str, status: str) -> str:
    """As the arena scores a result."""
    if status == "declined":
        return "declined"
    if status in ("error", "timeout"):
        return "error"
    if expected == "either":
        return "either"
    return "correct" if (expected, status) in (("accept", "accepted"), ("reject", "rejected")) \
        else "incorrect"


def cmd_run(a: argparse.Namespace) -> None:
    tests = read_tsv(a.tests)
    specs = list(a.checker or ["nitrolean"])
    if a.competitors:
        specs += [c for c in COMPETITORS if c not in specs]
    checkers = []
    for spec in specs:
        r = resolve_checker(spec, a.nitrolean)
        if isinstance(r, str):
            print(f"run: skipping {spec}: {r}", file=sys.stderr)
        else:
            checkers.append(r)
    if not checkers:
        sys.exit("run: no checker to run")

    done = set()
    if a.out.exists() and a.out.stat().st_size:
        done = {(r["checker"], r["test"]) for r in read_tsv(a.out)}
    else:
        a.out.parent.mkdir(parents=True, exist_ok=True)
        a.out.write_text("\t".join(COLUMNS) + "\n", encoding="utf-8")

    selected = []
    for t in tests:
        if a.test and not any(fnmatch.fnmatch(t["test"], p) for p in a.test):
            continue
        export = a.exports / f"{t['test']}.ndjson"
        if not export.exists():
            continue
        if a.max_bytes is not None and export.stat().st_size > a.max_bytes:
            continue
        selected.append((t, export))
    print(f"run: {len(selected)} exports, checkers: {', '.join(c[0] for c in checkers)}",
          file=sys.stderr)

    counts: dict[str, int] = {}
    for name, cmd, cwd in checkers:
        for t, export in selected:
            if (name, t["test"]) in done:
                continue
            timeout = None
            if t["timeout"] and not a.no_timeout:
                timeout = float(t["timeout"]) * a.timeout_scale
            r = run_one(cmd, export, cwd, timeout)
            row = {"checker": name, "test": t["test"], "group": t["group"],
                   "expected": t["expected"], **r,
                   "correctness": correctness(t["expected"], r["status"]),
                   "timeout_s": f"{timeout:g}" if timeout else ""}
            with open(a.out, "a", encoding="utf-8") as f:
                f.write("\t".join(str(row[c]).replace("\t", " ") for c in COLUMNS) + "\n")
            counts[row["correctness"]] = counts.get(row["correctness"], 0) + 1
            flag = "  <-- MISMATCH" if row["correctness"] == "incorrect" else ""
            if not a.quiet or flag or row["correctness"] == "error":
                print(f"{name:10} {t['test']:50} {t['expected']:7} {r['status']:9} "
                      f"{r['wall_s']:>9}s {r['max_rss_mib']:>9} MiB{flag}", file=sys.stderr)
    print("run: " + ", ".join(f"{k} {v}" for k, v in sorted(counts.items())), file=sys.stderr)


def fmt_time(s: str) -> str:
    if not s:
        return ""
    v = float(s)
    return f"{v:.2f}" if v < 10 else f"{v:.1f}" if v < 100 else f"{v:.0f}"


def fmt_mib(mib: float) -> str:
    return f"{mib:.0f} MiB" if mib < 1024 else f"{mib / 1024:.1f} GiB"


def cmd_report(a: argparse.Namespace) -> None:
    tests = {t["test"]: t for t in read_tsv(a.tests)}
    rows: dict[tuple[str, str], dict] = {}
    for path in a.results:
        for r in read_tsv(path):
            rows[(r["checker"], r["test"])] = r
    published = {(r["checker"], r["test"]): r for r in read_tsv(a.published)}
    main = a.main
    others = sorted({c for c, _ in rows} - {main}, key=lambda c: (COMPETITORS.index(c) if c in COMPETITORS else len(COMPETITORS), c))
    names = sorted({t for c, t in rows if c == main},
                   key=lambda n: (list(tests).index(n) if n in tests else 0))
    if a.group:
        names = [n for n in names if tests[n]["group"] in a.group]

    def short(status: str) -> str:
        return {"accepted": "accept", "rejected": "reject"}.get(status, status)

    head = ["test", "expected", main, "wall s", "CPU s", "peak RSS"]
    for o in others:
        head += [f"{o} (here)"]
    head += [f"{c} (arena)" for c in COMPETITORS]
    print("| " + " | ".join(head) + " |")
    print("|" + "---|" * len(head))
    tally: dict[str, int] = {}
    for n in names:
        r = rows[(main, n)]
        tally[r["correctness"]] = tally.get(r["correctness"], 0) + 1
        verdict = short(r["status"])
        if r["correctness"] == "incorrect":
            verdict = f"**{verdict} MISMATCH**"
        elif r["correctness"] == "error":
            verdict = f"**{verdict}**"
        # A run killed at its timeout leaves no usable CPU time or peak.
        killed = r["status"] == "timeout"
        cells = [n, tests[n]["expected"], verdict, fmt_time(r["wall_s"]),
                 "" if killed else fmt_time(r["cpu_s"]),
                 "" if killed else fmt_mib(float(r["max_rss_mib"]))]
        for o in others:
            x = rows.get((o, n))
            cells.append(f"{short(x['status'])} {fmt_time(x['wall_s'])} s, "
                         f"{fmt_mib(float(x['max_rss_mib']))}" if x else "")
        for c in COMPETITORS:
            p = published.get((c, n))
            cells.append(f"{short(p['status'])} {fmt_time(p['wall_s'])} s, "
                         f"{fmt_mib(int(p['max_rss_bytes']) / 2**20)}" if p else "")
        print("| " + " | ".join(cells) + " |")
    print()
    print(f"{main}: " + ", ".join(f"{k} {v}" for k, v in sorted(tally.items())))


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run", help="run checkers")
    r.add_argument("--exports", type=Path, default=HERE / "data/exports")
    r.add_argument("--tests", type=Path, default=HERE / "tests.tsv")
    r.add_argument("--out", type=Path, default=HERE / "results/results.tsv",
                   help="TSV to append to; pairs already in it are skipped (default: %(default)s)")
    r.add_argument("--checker", action="append", help="nitrolean, official, gruszka, nano-lean or NAME=CMD")
    r.add_argument("--competitors", action="store_true", help="also run the installed competitors")
    r.add_argument("--nitrolean", help="path of the nitrolean binary")
    r.add_argument("--test", action="append", help="only tests matching this glob (repeatable)")
    r.add_argument("--max-bytes", type=int, help="skip exports larger than this")
    r.add_argument("--timeout-scale", type=float, default=1.0,
                   help="multiply the arena's timeouts (set for its 8-core runner) by this")
    r.add_argument("--no-timeout", action="store_true", help="ignore the arena's timeouts")
    r.add_argument("--quiet", action="store_true", help="print only mismatches and errors")
    q = sub.add_parser("report", help="Markdown table of results")
    q.add_argument("results", type=Path, nargs="+")
    q.add_argument("--tests", type=Path, default=HERE / "tests.tsv")
    q.add_argument("--published", type=Path, default=HERE / "published.tsv")
    q.add_argument("--main", default="nitrolean", help="the checker the table is about")
    q.add_argument("--group", action="append", help="only tests of this group (repeatable)")
    a = p.parse_args()
    cmd_run(a) if a.cmd == "run" else cmd_report(a)


if __name__ == "__main__":
    main()
