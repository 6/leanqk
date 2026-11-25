"""Summarize measure.sh's TSV.

usage: python3 -I summarize.py MEASUREMENTS.tsv [LRAT-MANIFEST.tsv]

Prints, per export, each checker's verdict, wall time and peak resident memory, and, for the
LRAT series (when its manifest is given), the largest LRAT each checker accepts within the
60 s and 4 GiB limits of the rows with limit_s 60.
"""
import csv
import sys


def main():
    rows = list(csv.DictReader(open(sys.argv[1]), delimiter="\t"))
    checkers = []
    for r in rows:
        if r["checker"] not in checkers:
            checkers.append(r["checker"])
    by = {}
    for r in rows:
        by.setdefault((r["export"], r["limit_s"]), {})[r["checker"]] = r
    manifest = {}
    if len(sys.argv) > 2:
        for r in csv.DictReader(open(sys.argv[2]), delimiter="\t"):
            manifest[r["label"]] = r
    print("export (LRAT bytes) @limit | " + " | ".join(checkers))
    for (export, limit), per in sorted(by.items(), key=lambda kv: (kv[0][0], int(kv[0][1]))):
        size = manifest.get(export, {}).get("lrat_bytes", "")
        cells = []
        for c in checkers:
            r = per.get(c)
            if r is None:
                cells.append("-")
            elif r["verdict"] in ("accepted", "rejected", "error"):
                cells.append(f'{r["verdict"]} {float(r["wall_s"]):.1f}s {r["peak_rss_mib"]}MiB')
            else:
                cells.append(r["verdict"])
        print(f"{export} ({size}) @{limit}s | " + " | ".join(cells))
    if manifest:
        print()
        for c in checkers:
            best = None
            for (export, limit), per in by.items():
                r = per.get(c)
                if limit == "60" and r and r["verdict"] == "accepted" and export in manifest and export != "base":
                    n = int(manifest[export]["lrat_bytes"])
                    best = max(best or (0, ""), (n, export))
            print(f"largest LRAT {c} accepts within 60 s and 4 GiB: " + (f"{best[0]} bytes ({best[1]})" if best else "none"))


main()
