"""Trim a text-format LRAT proof: keep only the lemmas the final empty clause depends on, drop
deletion lines, and number the remaining lemmas consecutively after the clauses of the formula
(the LRAT checker of the standard library requires consecutive ids). The result is a valid LRAT
proof of the same formula.

usage: python3 -I lrat_trim.py IN.lrat OUT.lrat
"""
import sys


def main():
    lines = []  # (id, hint ids, raw line) of the addition lines, in file order
    with open(sys.argv[1]) as f:
        for raw in f:
            tok = raw.split()
            if len(tok) < 3 or tok[1] == "d":
                continue
            z = tok.index("0")
            lines.append((int(tok[0]), [abs(int(h)) for h in tok[z + 1:-1]], raw))
    if not lines or lines[-1][0] == 0 or len(lines[-1][2].split()) < 2 or lines[-1][2].split()[1] != "0":
        sys.exit("lrat_trim: the proof does not end with the empty clause")
    needed = {lines[-1][0]}
    keep = []  # (id, hint ids, raw line), in reverse file order
    for cid, hints, raw in reversed(lines):
        if cid in needed:
            needed.update(hints)
            keep.append((cid, hints, raw))
    keep.reverse()
    first = lines[0][0]  # the formula's clauses are 1 .. first - 1
    new = {cid: first + i for i, (cid, _, _) in enumerate(keep)}
    with open(sys.argv[2], "w") as out:
        for cid, hints, raw in keep:
            tok = raw.split()
            z = tok.index("0")
            lits = tok[1:z + 1]
            hs = [str((1 if int(h) > 0 else -1) * new.get(abs(int(h)), abs(int(h)))) for h in tok[z + 1:-1]]
            out.write(" ".join([str(new[cid])] + lits + hs + ["0"]) + "\n")


main()
