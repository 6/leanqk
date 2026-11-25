"""Reduce a declaration on which Lean's checker and nitrolean disagree to a small export.

usage: python3 -I bench/oracle/reduce.py EXPORT.ndjson DECLARATION [--out FILE]
           [--leanchecker BIN | --toolchain TC] [--nitrolean BIN] [--timeout S] [--max-tests N]

Starts from the closure of DECLARATION in EXPORT (the declaration and every declaration it
uses, transitively), checks that the two checkers still disagree on it, then shrinks it:
it turns the definitions and theorems of the closure into axioms of the same type, as many
as it can while the disagreement stays (a delta-debugging search: all at once, then halves,
quarters, ... down to one at a time), and drops what the remaining values no longer use.

"Disagree" means the same as for run.py: one checker accepts DECLARATION and the other
rejects it, or both reject it with different error kinds; a run that rejects another
declaration of the reduced export first does not count. The result is written to --out
(default reduced/<declaration>.ndjson) with a line for tests/kernel/cases.tsv on stdout:
id, rule, expected (Lean's verdict), lean, why.
"""
import argparse
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "tools"))
import export as ex  # noqa: E402
import run  # noqa: E402


def verdict(cmd, parse, path, target, timeout):
    """'accept', 'reject:<kind>', or None (another declaration rejected, or no verdict)."""
    with tempfile.NamedTemporaryFile("r", suffix=".log") as log:
        st = run.run_limited(cmd + [path], log.name, timeout, 64 * 1024)
        text = run.read_log(log.name)
    if st["status"] != "exited":
        return None
    ok, decl, msg = parse(text)
    if ok and st["exit"] == "0":
        return "accept"
    if decl and ex.norm_name(decl) == target:
        return "reject:" + run.kind_of(msg)
    return None


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("export")
    ap.add_argument("decl")
    ap.add_argument("--out")
    ap.add_argument("--leanchecker")
    ap.add_argument("--toolchain", default="leanprover/lean4:v4.36.0")
    ap.add_argument("--nitrolean", default=os.path.join(run.ROOT, "target", "release", "nitrolean"))
    ap.add_argument("--timeout", type=float, default=600)
    ap.add_argument("--max-tests", type=int, default=300)
    args = ap.parse_args()
    lc = args.leanchecker or os.path.join(run.toolchain_bin(args.toolchain), "leanchecker")
    target = ex.norm_name(args.decl)
    out = args.out or os.path.join("reduced", re.sub(r"[^\w.-]", "_", target) + ".ndjson")
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)

    print(f"reading {args.export}", file=sys.stderr)
    g = ex.Graph(args.export)
    nid = g.name_id(target)
    if nid is None:
        sys.exit(f"reduce: {args.decl} is not declared in {args.export}")
    start = g.decl_of[nid]
    tests = [0]
    tmp = out + ".try.ndjson"

    def both(value_free):
        tests[0] += 1
        lines = g.closure([start], value_free)
        g.write(tmp, lines, value_free)
        lv = verdict([lc, "--from-export"], run.parse_lean, tmp, target, args.timeout)
        nv = verdict([args.nitrolean, "check"], run.parse_nitrolean, tmp, target, args.timeout)
        return lv, nv, len(lines)

    lv0, nv0, n0 = both(set())
    print(f"closure: {n0} records; Lean {lv0}, nitrolean {nv0}", file=sys.stderr)
    if lv0 is None or nv0 is None or lv0 == nv0:
        os.remove(tmp)
        sys.exit("reduce: the closure does not show the disagreement (Lean "
                 f"{lv0}, nitrolean {nv0}); the mismatch needs more than the closure")

    def interesting(vf):
        if tests[0] >= args.max_tests:
            return False
        lv, nv, _ = both(vf)
        return lv == lv0 and nv == nv0

    # Delta debugging over the records whose value can be dropped.
    cands = sorted(no for no in g.closure([start]) if no != start
                   and g.decl_roots[no][0] in ("def", "thm", "opaque"))
    fixed = set()   # records made axioms so far
    if cands and interesting(set(cands)):
        fixed = set(cands)
        cands = []
    chunk = max(1, len(cands) // 2)
    while cands and tests[0] < args.max_tests:
        kept = []
        for i in range(0, len(cands), chunk):
            part = set(cands[i:i + chunk])
            if interesting(fixed | part):
                fixed |= part
            else:
                kept.extend(sorted(part))
        live = g.closure([start], fixed)
        cands = [c for c in kept if c in live]
        if chunk == 1:
            break
        chunk = max(1, chunk // 2)
    lines = g.closure([start], fixed)
    g.write(out, lines, fixed)
    os.remove(tmp)
    lv, nv = lv0, nv0  # every kept step reproduced these
    print(f"reduced: {len(lines)} records ({len(fixed)} made axioms), {tests[0]} test runs; "
          f"Lean {lv}, nitrolean {nv}; wrote {out}", file=sys.stderr)
    expected = lv.split(":")[0]
    cid = "oracle-" + re.sub(r"[^\w-]", "-", target).lower()
    print(f"{cid}\toracle\t{expected}\t{expected}\tcorpus oracle: {target}: Lean {lv}, "
          f"nitrolean {nv}")


if __name__ == "__main__":
    main()
