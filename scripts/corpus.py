#!/usr/bin/env python3
"""Helpers for scripts/fetch-corpus.sh and scripts/lean-verdicts.sh.

Standard library only; run with `python3 -I`.

  corpus.py collect-arena BUILD_DIR OUT
      Copy the exports `lka.py build-test` left in BUILD_DIR to OUT/arena/ and
      print their manifest lines.
  corpus.py collect-cases CASES_DIR OUT SOURCE
      Copy the exports a file using the Arena's tutorial machinery wrote to
      CASES_DIR/{good,bad}/ to OUT/SOURCE/ and print their manifest lines.
  corpus.py checksums OUT [--check FILE] [--allow-extra]
      Print the SHA-256 of every export in OUT, or check them against FILE.
  corpus.py lean-verdicts OUT TSV [--jobs N]
      Run Lean's leanchecker on every export in OUT/manifest.tsv and write
      corpus/expected-lean-*.tsv.
  corpus.py expected-nitrolean LEAN_TSV DIVERGENCES_MD OUT_TSV [--check]
      Derive nitrolean's intended verdicts from Lean's and the divergence list.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

DEFAULT_TIMEOUT = 120


def tsv_field(s: str) -> str:
    return " ".join(str(s).split())


def manifest_line(test_id: str, source: str, expected: str, timeout, origin: str) -> str:
    return "\t".join([test_id, source, expected, str(timeout or ""), tsv_field(origin)])


def collect_arena(build_dir: Path, out: Path) -> None:
    lines = []
    for stats_file in sorted(build_dir.rglob("*.stats.json")):
        if "work" in stats_file.relative_to(build_dir).parts[:1]:
            continue
        stats = json.loads(stats_file.read_text())
        export = stats_file.with_name(stats_file.name[: -len(".stats.json")] + ".ndjson")
        name = stats["name"]
        dest = out / "arena" / f"{name}.ndjson"
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(export.resolve(), dest)
        origin = stats.get("yaml_file", "")
        lines.append(manifest_line(f"arena/{name}", "arena", stats["outcome"],
                                   stats.get("timeout"), origin))
    if not lines:
        sys.exit(f"corpus.py: no exports found in {build_dir}")
    print("\n".join(lines))


def collect_cases(cases_dir: Path, out: Path, source: str) -> None:
    lines = []
    for verdict, sub in (("accept", "good"), ("reject", "bad")):
        for export in sorted((cases_dir / sub).glob("*.ndjson")):
            if export.stat().st_size == 0:
                sys.exit(f"corpus.py: empty export {export}")
            dest = out / source / export.name
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(export, dest)
            lines.append(manifest_line(f"{source}/{export.stem}", source, verdict, None,
                                       f"corpus/lean ({export.stem})"))
    if not lines:
        sys.exit(f"corpus.py: no exports found in {cases_dir}")
    print("\n".join(sorted(lines)))


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def checksums(out: Path, check: Path | None, allow_extra: bool) -> None:
    files = sorted(p.relative_to(out).as_posix() for p in out.rglob("*.ndjson"))
    got = {f: sha256_file(out / f) for f in files}
    if check is None:
        for f in files:
            print(f"{got[f]}  {f}")
        return
    want = {}
    for line in check.read_text().splitlines():
        digest, name = line.split(None, 1)
        want[name.strip()] = digest
    bad = [f for f in want if f in got and got[f] != want[f]]
    missing = [f for f in want if f not in got]
    extra = [f for f in got if f not in want]
    for f in bad:
        print(f"checksum mismatch: {f}", file=sys.stderr)
    for f in missing:
        print(f"missing export: {f}", file=sys.stderr)
    for f in extra:
        print(f"{'unchecked' if allow_extra else 'unexpected'} export: {f}", file=sys.stderr)
    if bad or missing or (extra and not allow_extra):
        sys.exit(f"corpus.py: {len(bad)} mismatched, {len(missing)} missing, "
                 f"{len(extra)} extra exports (against {check})")
    print(f"corpus.py: {len(want)} exports match {check.name}", file=sys.stderr)


def read_tsv(path: Path) -> list[dict]:
    lines = path.read_text().splitlines()
    header = lines[0].split("\t")
    return [dict(zip(header, line.split("\t"))) for line in lines[1:] if line]


def lean_verdict(export: Path, toolchain: str, timeout: int) -> tuple[str, str]:
    try:
        r = subprocess.run(["elan", "run", toolchain, "leanchecker", "--from-export", str(export)],
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "timeout", f"no verdict within {timeout} s"
    text = (r.stdout + r.stderr).strip()
    first = text.splitlines()[0] if text else ""
    if r.returncode == 0 and "accepts the solution" in text:
        return "accept", ""
    if "rejects the solution" in text:
        # The first line names the declaration, the second the kernel's complaint.
        rest = [l.strip() for l in text.splitlines()[1:3]]
        reason = first.split("rejects the solution:", 1)[-1].strip()
        return "reject", tsv_field(" ".join([reason] + rest))[:200]
    if r.returncode == 1 and "uncaught exception" in text:
        # leanchecker refuses the export before it gets to the kernel, e.g. on
        # a duplicate declaration: a rejection all the same.
        return "reject", tsv_field(first)[:200]
    return "error", tsv_field(f"exit {r.returncode}: {first}")[:200]


def lean_verdicts(out: Path, tsv: Path, jobs: int, toolchain: str) -> None:
    rows = read_tsv(out / "manifest.tsv")

    def run(row):
        timeout = max(int(row["timeout"] or DEFAULT_TIMEOUT) * 3, DEFAULT_TIMEOUT)
        return lean_verdict(out / f"{row['id']}.ndjson", toolchain, timeout)

    with concurrent.futures.ThreadPoolExecutor(jobs) as pool:
        verdicts = list(pool.map(run, rows))
    lines = ["test_id\tsource\texpected\tlean\tnote"]
    for row, (verdict, note) in zip(rows, verdicts):
        expected = row["expected"]
        if verdict in ("accept", "reject") and expected in ("accept", "reject") and verdict != expected:
            note = f"Lean {verdict}s, upstream expects {expected}" + (f"; {note}" if note else "")
        lines.append("\t".join([row["id"], row["source"], expected, verdict, tsv_field(note)]))
    tsv.write_text("\n".join(lines) + "\n")
    counts = {}
    for v, _ in verdicts:
        counts[v] = counts.get(v, 0) + 1
    print(f"corpus.py: wrote {tsv} ({len(rows)} tests: {counts})", file=sys.stderr)


DIVERGENCE_ROW = re.compile(r"^\|\s*`([^`]+)`\s*\|\s*(accept|reject)\s*\|")


def expected_nitrolean(lean_tsv: Path, divergences: Path, out_tsv: Path, check: bool) -> None:
    rows = read_tsv(lean_tsv)
    ids = {r["test_id"] for r in rows}
    overrides = {}
    for line in divergences.read_text().splitlines():
        m = DIVERGENCE_ROW.match(line)
        if m:
            overrides[m.group(1)] = m.group(2)
    unknown = sorted(set(overrides) - ids)
    if unknown:
        sys.exit(f"corpus.py: divergences for unknown tests: {', '.join(unknown)}")
    lines = ["test_id\tverdict\tbasis"]
    for r in rows:
        tid = r["test_id"]
        if tid in overrides:
            verdict, basis = overrides[tid], "divergence (corpus/divergences.md)"
            if verdict == r["lean"]:
                sys.exit(f"corpus.py: {tid} is listed as a divergence but Lean agrees")
        elif r["lean"] in ("accept", "reject"):
            verdict, basis = r["lean"], "Lean v4.36.0"
        else:
            sys.exit(f"corpus.py: {tid}: no Lean verdict ({r['lean']}) and no divergence entry")
        lines.append("\t".join([tid, verdict, basis]))
    text = "\n".join(lines) + "\n"
    if check:
        if not out_tsv.exists() or out_tsv.read_text() != text:
            sys.exit(f"corpus.py: {out_tsv} is out of date; run scripts/lean-verdicts.sh")
        print(f"corpus.py: {out_tsv.name} is up to date", file=sys.stderr)
    else:
        out_tsv.write_text(text)
        print(f"corpus.py: wrote {out_tsv} ({len(overrides)} divergences)", file=sys.stderr)


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    a = sub.add_parser("collect-arena")
    a.add_argument("build_dir", type=Path)
    a.add_argument("out", type=Path)
    c = sub.add_parser("collect-cases")
    c.add_argument("cases_dir", type=Path)
    c.add_argument("out", type=Path)
    c.add_argument("source")
    s = sub.add_parser("checksums")
    s.add_argument("out", type=Path)
    s.add_argument("--check", type=Path)
    s.add_argument("--allow-extra", action="store_true")
    v = sub.add_parser("lean-verdicts")
    v.add_argument("out", type=Path)
    v.add_argument("tsv", type=Path)
    v.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    v.add_argument("--toolchain", default="leanprover/lean4:v4.36.0")
    e = sub.add_parser("expected-nitrolean")
    e.add_argument("lean_tsv", type=Path)
    e.add_argument("divergences", type=Path)
    e.add_argument("out_tsv", type=Path)
    e.add_argument("--check", action="store_true")
    args = p.parse_args()
    if args.cmd == "collect-arena":
        collect_arena(args.build_dir, args.out)
    elif args.cmd == "collect-cases":
        collect_cases(args.cases_dir, args.out, args.source)
    elif args.cmd == "checksums":
        checksums(args.out, args.check, args.allow_extra)
    elif args.cmd == "lean-verdicts":
        lean_verdicts(args.out, args.tsv, args.jobs, args.toolchain)
    elif args.cmd == "expected-nitrolean":
        expected_nitrolean(args.lean_tsv, args.divergences, args.out_tsv, args.check)


if __name__ == "__main__":
    main()
