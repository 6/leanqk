#!/usr/bin/env python3
"""Pins and checksums for the Lean Kernel Arena test set (stdlib only).

  pin.py pin RESULTS_JSON         rewrite tests.tsv and published.tsv from the
                                  arena's results.json
  pin.py collect BUILD_DIR OUT    move the exports that `lka.py build-test`
                                  wrote under BUILD_DIR into OUT/<test>.ndjson
  pin.py verify OUT               check every export in OUT against the arena's
                                  SHA-256 in tests.tsv and write OUT/SHA256SUMS

tests.tsv holds, per test, what the arena published for the export it checked
(size, lines, SHA-256, Lean version), so a rebuilt export can be compared byte
for byte with the arena's. published.tsv holds the arena's own measurements of
the checkers we compare against, on its 8-core amd64 runner.
"""

import argparse
import hashlib
import json
import shutil
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
TESTS_TSV = HERE / "tests.tsv"
PUBLISHED_TSV = HERE / "published.tsv"

TEST_COLUMNS = ["test", "group", "expected", "timeout", "compare_perf", "skip_on_ci",
                "lean_version", "export_format", "lines", "bytes", "sha256", "yaml"]
PUBLISHED_CHECKERS = ["official", "gruszka", "nano-lean"]
PUBLISHED_COLUMNS = ["checker", "version", "test", "status", "correctness", "wall_s", "cpu_s",
                     "max_rss_bytes", "ginstructions", "date"]


def group_of(name: str) -> str:
    return name.split("/", 1)[0] if "/" in name else "real-world"


def write_tsv(path: Path, columns: list[str], rows: list[dict]) -> None:
    with open(path, "w", encoding="utf-8") as f:
        f.write("\t".join(columns) + "\n")
        for r in rows:
            f.write("\t".join(" ".join(str(r.get(c, "")).split()) for c in columns) + "\n")


def read_tsv(path: Path) -> list[dict]:
    lines = path.read_text(encoding="utf-8").splitlines()
    head = lines[0].split("\t")
    return [dict(zip(head, line.split("\t"))) for line in lines[1:] if line]


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while chunk := f.read(1 << 22):
            h.update(chunk)
    return h.hexdigest()


def cmd_pin(results_json: Path) -> None:
    data = json.loads(results_json.read_text(encoding="utf-8"))
    print(f"results.json of arena commit {data['meta']['git_revision']}, "
          f"sha256 {sha256_file(results_json)}", file=sys.stderr)
    tests = []
    for t in sorted(data["tests"], key=lambda t: t["name"]):
        tests.append({
            "test": t["name"], "group": group_of(t["name"]), "expected": t["outcome"],
            "timeout": t.get("timeout", ""),
            "compare_perf": "yes" if t.get("compare-perf") else "",
            "skip_on_ci": "yes" if t.get("skip-on-ci") else "",
            "lean_version": t.get("lean_version", ""),
            "export_format": t.get("lean4export_version", ""),
            "lines": t["lines"], "bytes": t["size"], "sha256": t["sha256"],
            "yaml": t.get("yaml_file", ""),
        })
    write_tsv(TESTS_TSV, TEST_COLUMNS, tests)
    versions = {c["name"]: c.get("version") or (c.get("rev") or "")[:12] for c in data["checkers"]}
    published = []
    for r in sorted(data["results"], key=lambda r: (r["checker"], r["test"])):
        if r["checker"] not in PUBLISHED_CHECKERS:
            continue
        published.append({
            "checker": r["checker"], "version": versions.get(r["checker"], ""), "test": r["test"],
            "status": r["status"], "correctness": r["correctness"],
            "wall_s": f"{r['wall_time']:.3f}", "cpu_s": f"{r['cpu_time']:.3f}",
            "max_rss_bytes": int(r["max_rss"]), "ginstructions": f"{(r.get('instructions') or 0) / 1e9:.3f}", "date": r.get("date", ""),
        })
    write_tsv(PUBLISHED_TSV, PUBLISHED_COLUMNS, published)
    print(f"wrote {len(tests)} tests and {len(published)} published results", file=sys.stderr)


def cmd_collect(build_dir: Path, out: Path) -> None:
    """Move every export with a .stats.json next to it (as lka.py writes them,
    including the generated tutorial tests) to OUT/<test name>.ndjson."""
    n = 0
    for stats_file in sorted(build_dir.rglob("*.stats.json")):
        if stats_file.relative_to(build_dir).parts[0] == "work":
            continue
        stats = json.loads(stats_file.read_text(encoding="utf-8"))
        export = stats_file.with_name(stats_file.name[: -len(".stats.json")] + ".ndjson")
        if not export.exists():
            continue
        dest = out / f"{stats['name']}.ndjson"
        dest.parent.mkdir(parents=True, exist_ok=True)
        if dest.exists():
            dest.unlink()
        shutil.move(str(export), dest)
        n += 1
    print(f"collected {n} exports into {out}", file=sys.stderr)


def cmd_verify(out: Path) -> None:
    pinned = {t["test"]: t for t in read_tsv(TESTS_TSV)}
    bad = 0
    sums = []
    for export in sorted(out.rglob("*.ndjson")):
        name = export.relative_to(out).as_posix()[: -len(".ndjson")]
        digest = sha256_file(export)
        sums.append(f"{digest}  {name}.ndjson")
        t = pinned.get(name)
        if t is None:
            print(f"verify: {name}: not an arena test", file=sys.stderr)
            bad += 1
        elif digest != t["sha256"]:
            print(f"verify: {name}: sha256 {digest}, the arena's is {t['sha256']}", file=sys.stderr)
            bad += 1
    (out / "SHA256SUMS").write_text("\n".join(sums) + "\n", encoding="utf-8")
    missing = sorted(set(pinned) - {s.split("  ", 1)[1][: -len(".ndjson")] for s in sums})
    print(f"verify: {len(sums) - bad} of {len(sums)} exports identical to the arena's; "
          f"{len(missing)} arena tests not built here", file=sys.stderr)
    if bad:
        sys.exit(1)


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    sub.add_parser("pin").add_argument("results_json", type=Path)
    c = sub.add_parser("collect")
    c.add_argument("build_dir", type=Path)
    c.add_argument("out", type=Path)
    sub.add_parser("verify").add_argument("out", type=Path)
    a = p.parse_args()
    if a.cmd == "pin":
        cmd_pin(a.results_json)
    elif a.cmd == "collect":
        cmd_collect(a.build_dir, a.out)
    else:
        cmd_verify(a.out)


if __name__ == "__main__":
    main()
