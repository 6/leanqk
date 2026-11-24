#!/usr/bin/env python3
"""Run `leanqk check` on every export of the corpus and compare the verdicts.

  scripts/run-corpus.py [--leanqk BIN] [--corpus DIR] [--expected TSV] [--jobs N]
                        [--timeout S] [--filter REGEX] [--results TSV] [--strict]

Each test's expected verdict comes from corpus/expected-leanqk.tsv, its export
from DIR/<test id>.ndjson (made by scripts/fetch-corpus.sh) and its timeout from
DIR/manifest.tsv (the Arena's per-test timeout, else --timeout).

`leanqk check FILE` exits 0 for accepted, 1 for rejected (malformed input
included) and 2 for declined (usage or I/O errors, an unsupported format, or a
check it cannot do yet). A test is

  pass     the verdict is the expected one
  fail     the other verdict
  pending  leanqk declined (exit 2), or said "not implemented"; listed and
           counted, but not a failure unless --strict
  crash    any other exit status, or killed by a signal
  timeout  no verdict within the timeout
  missing  the export is not there (fetch the corpus first)

and the run exits 1 if any test fails, crashes, times out or is missing (or is
pending, with --strict).

With --parse-only, it runs `leanqk check --parse-only FILE` instead, which
exits 0 once the file has been read: every test expected to be accepted must
then exit 0, and a test expected to be rejected may exit 0 or 1 (its export
may be well formed or not).

Standard library only; run with `python3 -I`.
"""

from __future__ import annotations

import argparse
import concurrent.futures
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

ROOT = Path(__file__).resolve().parent.parent
NOT_IMPLEMENTED = re.compile(r"not (yet )?implemented", re.IGNORECASE)
FAILING = ("fail", "crash", "timeout", "missing")
STATUSES = ("pass", "pending") + FAILING


def read_tsv(path: Path) -> list[dict]:
    lines = path.read_text().splitlines()
    header = lines[0].split("\t")
    return [dict(zip(header, line.split("\t"))) for line in lines[1:] if line]


def gnu_time() -> str | None:
    """GNU time, which measures the peak memory of leanqk alone.

    The resource usage that wait4 reports for a direct child of this process
    includes the memory the child had as a fork of this Python process, before
    it ran leanqk, which is more than a small test needs.
    """
    for path in ("/usr/bin/time", shutil.which("gtime")):
        if path and os.path.isfile(path):
            r = subprocess.run([path, "--version"], capture_output=True, text=True)
            if "GNU" in r.stdout + r.stderr:
                return path
    return None


TERMINATED = re.compile(r"Command terminated by signal (\d+)")


def run_one(leanqk: str, export: Path, timeout: float, time_bin: str | None,
            parse_only: bool = False) -> dict:
    """Run leanqk on one export: exit status, wall time, peak RSS, stderr."""
    with tempfile.NamedTemporaryFile(prefix="run-corpus-", suffix=".time") as tf:
        cmd = [leanqk, "check"] + (["--parse-only"] if parse_only else []) + [str(export)]
        if time_bin:
            cmd = [time_bin, "-f", "%M", "-o", tf.name] + cmd
        start = time.monotonic()
        proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                                stderr=subprocess.PIPE, start_new_session=True)
        timed_out = threading.Event()

        def kill():
            timed_out.set()
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass

        timer = threading.Timer(timeout, kill)
        timer.start()
        stderr_chunks = []
        reader = threading.Thread(target=lambda: stderr_chunks.append(proc.stderr.read()))
        reader.start()
        _, status, usage = os.wait4(proc.pid, 0)
        elapsed = time.monotonic() - start
        timer.cancel()
        reader.join()
        proc.stderr.close()
        code = os.waitstatus_to_exitcode(status)
        # ru_maxrss is in KiB on Linux, in bytes on macOS.
        rss = usage.ru_maxrss * (1 if sys.platform == "darwin" else 1024)
        if time_bin:
            report = Path(tf.name).read_text().split()
            text = " ".join(report)
            m = TERMINATED.search(text)
            if m:
                code = -int(m.group(1))
            rss = int(report[-1]) * 1024 if report and report[-1].isdigit() else 0
    stderr = b"".join(stderr_chunks).decode(errors="replace")
    return {"code": code, "timed_out": timed_out.is_set(), "time": elapsed,
            "rss": rss, "stderr": stderr}


def classify(expected: str, r: dict, parse_only: bool = False) -> tuple[str, str]:
    """Status and observed verdict of one run."""
    code = r["code"]
    if r["timed_out"]:
        return "timeout", "-"
    if code == 2 or (code != 0 and NOT_IMPLEMENTED.search(r["stderr"])):
        return "pending", "declined"
    if code in (0, 1) and parse_only:
        got = "parsed" if code == 0 else "malformed"
        return ("pass" if code == 0 or expected == "reject" else "fail"), got
    if code in (0, 1):
        got = "accept" if code == 0 else "reject"
        return ("pass" if got == expected else "fail"), got
    return "crash", f"exit {code}" if code > 0 else f"signal {-code}"


def first_line(text: str) -> str:
    for line in text.splitlines():
        if line.strip():
            return line.strip()[:160]
    return ""


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--leanqk", default=None, help="leanqk binary (default: target/release/leanqk)")
    p.add_argument("--corpus", type=Path, default=ROOT / "corpus" / "exports")
    p.add_argument("--expected", type=Path, default=ROOT / "corpus" / "expected-leanqk.tsv")
    p.add_argument("--jobs", "-j", type=int, default=1,
                   help="tests to run at once (default 1, for stable times)")
    p.add_argument("--timeout", type=float, default=120,
                   help="seconds per test without an Arena timeout (default 120)")
    p.add_argument("--timeout-scale", type=float, default=1.0,
                   help="multiply every timeout by this (e.g. for slow machines)")
    p.add_argument("--filter", default=None, help="only tests whose id matches this regex")
    p.add_argument("--results", type=Path, help="also write the results as TSV here")
    p.add_argument("--strict", action="store_true", help="pending tests fail the run")
    p.add_argument("--parse-only", action="store_true",
                   help="only check that leanqk reads every export (leanqk check --parse-only)")
    p.add_argument("--quiet", "-q", action="store_true", help="table rows only for tests that did not pass")
    args = p.parse_args()

    leanqk = args.leanqk or str(ROOT / "target" / "release" / "leanqk")
    if not (os.path.isfile(leanqk) or shutil.which(leanqk)):
        print(f"run-corpus: {leanqk} not found (cargo build --release)", file=sys.stderr)
        return 2
    tests = read_tsv(args.expected)
    if args.filter:
        tests = [t for t in tests if re.search(args.filter, t["test_id"])]
    timeouts = {}
    manifest = args.corpus / "manifest.tsv"
    if manifest.exists():
        timeouts = {r["id"]: float(r["timeout"]) for r in read_tsv(manifest) if r["timeout"]}
    elif tests:
        print(f"run-corpus: no {manifest}; run scripts/fetch-corpus.sh first", file=sys.stderr)

    time_bin = gnu_time()
    if not time_bin:
        print("run-corpus: no GNU time; peak memory includes the runner's own", file=sys.stderr)

    def run(t):
        export = args.corpus / f"{t['test_id']}.ndjson"
        timeout = timeouts.get(t["test_id"], args.timeout) * args.timeout_scale
        if not export.exists():
            return t, "missing", "-", {"time": 0.0, "rss": 0, "stderr": "", "code": None}, timeout
        r = run_one(leanqk, export, timeout, time_bin, args.parse_only)
        status, got = classify(t["verdict"], r, args.parse_only)
        return t, status, got, r, timeout

    wall = time.monotonic()
    width = max([len(t["test_id"]) for t in tests] + [4])
    print(f"{'status':8} {'test':{width}} {'expect':7} {'got':9} {'time s':>8} {'peak MiB':>9}  note")
    results = []
    with concurrent.futures.ThreadPoolExecutor(max(1, args.jobs)) as pool:
        for t, status, got, r, timeout in pool.map(run, tests):
            note = ""
            if status == "timeout":
                note = f"killed after {timeout:g} s"
            elif status not in ("pass",):
                note = first_line(r["stderr"])
            results.append((t, status, got, r, note))
            if not (args.quiet and status == "pass"):
                print(f"{status:8} {t['test_id']:{width}} {t['verdict']:7} {got:9} "
                      f"{r['time']:8.2f} {r['rss'] / 2**20:9.1f}  {note}", flush=True)
    wall = time.monotonic() - wall

    counts = {s: 0 for s in STATUSES}
    for _, status, *_ in results:
        counts[status] += 1
    total_time = sum(r["time"] for _, _, _, r, _ in results)
    peak = max([r["rss"] for _, _, _, r, _ in results] + [0])
    summary = ", ".join(f"{counts[s]} {s}" for s in STATUSES if counts[s] or s in ("pass", "fail", "timeout", "pending"))
    print()
    print(f"run-corpus: {len(results)} tests: {summary}")
    print(f"run-corpus: {total_time:.1f} s in leanqk ({wall:.1f} s wall), peak {peak / 2**20:.1f} MiB")
    bad = [s for s in FAILING if counts[s]] + (["pending"] if args.strict and counts["pending"] else [])

    if args.results:
        with open(args.results, "w") as f:
            f.write("test_id\texpected\tstatus\tgot\ttime_s\tpeak_kib\tnote\n")
            for t, status, got, r, note in results:
                f.write(f"{t['test_id']}\t{t['verdict']}\t{status}\t{got}\t{r['time']:.3f}\t"
                        f"{r['rss'] // 1024}\t{note.replace(chr(9), ' ')}\n")
    step_summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if step_summary:
        with open(step_summary, "a") as f:
            f.write(f"## Corpus{' (parse only)' if args.parse_only else ''}\n\n| status | tests |\n|---|---:|\n")
            for s in STATUSES:
                f.write(f"| {s} | {counts[s]} |\n")
            f.write(f"\n{total_time:.1f} s in leanqk, peak {peak / 2**20:.1f} MiB\n\n")
            unexpected = [x for x in results if x[1] in FAILING]
            if unexpected:
                f.write("| test | expected | status | got | note |\n|---|---|---|---|---|\n")
                for t, status, got, r, note in unexpected[:200]:
                    f.write(f"| `{t['test_id']}` | {t['verdict']} | {status} | {got} | {note.replace('|', '/')} |\n")
    if bad:
        print(f"run-corpus: FAILED ({', '.join(bad)})")
        return 1
    print("run-corpus: OK" + (f" ({counts['pending']} pending)" if counts["pending"] else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
