"""Choose the Mathlib declarations whose proofs are dominated by kernel computation.

usage: python3 -I select_decide.py RANK.tsv [COUNT] > names.txt

RANK.tsv is the output of lean/RankDecide.lean: per theorem whose proof term uses
`of_decide_eq_true`, the time the kernel takes to check it and the number of distinct objects
of its proof term. A proof that is small but slow to check is spending its time computing, so
the theorems are ranked by nanoseconds per object, among those that take at least 1 ms, and
the COUNT (default 150) highest are written, sorted by name.
"""
import sys


def main():
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 150
    rows = []
    for line in open(sys.argv[1]):
        name, ns, _mod, ok, objs = line.rstrip("\n").split("\t")
        if ok == "true" and int(ns) >= 1_000_000 and int(objs) > 0:
            rows.append((int(ns) / int(objs), name))
    rows.sort(key=lambda r: (-r[0], r[1]))
    for name in sorted(n for _, n in rows[:count]):
        print(name)


main()
