#!/usr/bin/env python3
"""Generate the kernel test cases under tests/kernel.

Each case starts from a valid export written by Lean's `leanexport` (Lean is
pinned in ./lean-toolchain) and applies one targeted mutation, or builds a
small export from scratch.  Cases are defined in cases.py.

  mise exec -- python -I gen.py              # write out/cases/*.ndjson
  mise exec -- python -I gen.py --lean       # also run `leanchecker --from-export`
  mise exec -- python -I gen.py --update     # refresh cases.tsv and committed small exports
  mise exec -- python -I gen.py --check      # fail if cases.tsv or committed exports are stale

Run it from any directory; paths are relative to this file.
"""

import argparse
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import cases  # noqa: E402
from exportlib import Export  # noqa: E402

OUT = os.path.join(HERE, "out")
BUILD = os.path.join(OUT, "build")
COMMITTED = os.path.join(HERE, "exports")
TSV = os.path.join(HERE, "cases.tsv")
SMALL = 16 * 1024  # exports up to this size are committed
LEAN_TIMEOUT = 600


def lean_bin():
    out = subprocess.run(["elan", "which", "lean"], cwd=HERE, check=True,
                         capture_output=True, text=True).stdout.strip()
    return os.path.dirname(out)


class Toolchain:
    def __init__(self):
        self.bin = lean_bin()
        self.env = dict(os.environ)
        self.env["LEAN_PATH"] = os.pathsep.join(
            [os.path.join(self.bin, "..", "lib", "lean"), BUILD])
        self.cache = {}

    def build(self):
        os.makedirs(BUILD, exist_ok=True)
        src = os.path.join(HERE, "lean", "KCases.lean")
        olean = os.path.join(BUILD, "KCases.olean")
        if not os.path.exists(olean) or os.path.getmtime(olean) < os.path.getmtime(src):
            subprocess.run([os.path.join(self.bin, "lean"), "-o", olean, src],
                           check=True, env=self.env, stdout=subprocess.DEVNULL)

    def export(self, consts, unsafe=False):
        key = (tuple(consts), unsafe)
        if key not in self.cache:
            cmd = [os.path.join(self.bin, "leanexport")]
            if unsafe:
                cmd.append("--export-unsafe")
            cmd += ["KCases", "--"] + list(consts)
            self.cache[key] = subprocess.run(cmd, check=True, env=self.env,
                                             capture_output=True, text=True).stdout
        return Export(self.cache[key])

    def check(self, path):
        cmd = [os.path.join(self.bin, "leanchecker"), "--from-export", path]
        try:
            p = subprocess.run(cmd, env=self.env, capture_output=True, text=True,
                               timeout=LEAN_TIMEOUT)
        except subprocess.TimeoutExpired:
            return "timeout", ""
        msg = (p.stdout + p.stderr).strip().replace("\n", " ").replace("\t", " ")
        if p.returncode == 0:
            return "accept", msg
        if "rejects" in msg or "uncaught exception" in msg:
            return "reject", msg
        return "error(%d)" % p.returncode, msg


def tsv_rows(results):
    rows = ["id\trule\texpected\tlean\twhy"]
    for c in cases.CASES:
        rows.append("\t".join([c.id, c.rule, c.expected, results.get(c.id, "?"), c.why]))
    return "\n".join(rows) + "\n"


def read_tsv():
    if not os.path.exists(TSV):
        return {}
    out = {}
    with open(TSV, encoding="utf-8") as f:
        next(f)
        for ln in f:
            parts = ln.rstrip("\n").split("\t")
            out[parts[0]] = parts[3]
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--lean", action="store_true", help="run leanchecker on every case")
    ap.add_argument("--update", action="store_true", help="rewrite cases.tsv and exports/")
    ap.add_argument("--check", action="store_true", help="check cases.tsv and exports/ are current")
    ap.add_argument("--only", help="comma-separated case ids")
    args = ap.parse_args()

    tc = Toolchain()
    tc.build()
    outdir = os.path.join(OUT, "cases")
    os.makedirs(outdir, exist_ok=True)
    only = set(args.only.split(",")) if args.only else None
    ids = [c.id for c in cases.CASES]
    dup = {i for i in ids if ids.count(i) > 1}
    if dup:
        sys.exit("duplicate case ids: %s" % sorted(dup))

    texts = {}
    for c in cases.CASES:
        if only and c.id not in only:
            continue
        texts[c.id] = c.build(tc)
        with open(os.path.join(outdir, c.id + ".ndjson"), "w", encoding="utf-8") as f:
            f.write(texts[c.id])

    results = read_tsv()
    if args.lean:
        for c in cases.CASES:
            if c.id not in texts:
                continue
            verdict, msg = tc.check(os.path.join(outdir, c.id + ".ndjson"))
            results[c.id] = verdict
            flag = "" if cases.agrees(c.expected, verdict) else "   <-- differs from expected"
            print("%-36s expected %-7s lean %-7s%s" % (c.id, c.expected, verdict, flag))
            if flag and msg:
                print("    " + msg[:300])

    small = {i: t for i, t in texts.items() if len(t.encode()) <= SMALL}
    if args.update:
        with open(TSV, "w", encoding="utf-8") as f:
            f.write(tsv_rows(results))
        if not only:
            shutil.rmtree(COMMITTED, ignore_errors=True)
        os.makedirs(COMMITTED, exist_ok=True)
        for i, t in small.items():
            with open(os.path.join(COMMITTED, i + ".ndjson"), "w", encoding="utf-8") as f:
                f.write(t)
    if args.check:
        bad = []
        with open(TSV, encoding="utf-8") as f:
            if f.read() != tsv_rows(results):
                bad.append("cases.tsv")
        want = set(i + ".ndjson" for i in small)
        have = set(os.listdir(COMMITTED)) if os.path.isdir(COMMITTED) else set()
        bad += sorted(want ^ have)
        for fn in sorted(want & have):
            with open(os.path.join(COMMITTED, fn), encoding="utf-8") as f:
                if f.read() != small[fn[:-len(".ndjson")]]:
                    bad.append(fn)
        if bad:
            sys.exit("stale: " + ", ".join(bad))
    print("%d cases, %d small enough to commit" % (len(texts), len(small)))


if __name__ == "__main__":
    main()
