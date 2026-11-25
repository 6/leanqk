#!/usr/bin/env bash
# Export Mathlib declarations whose proofs are dominated by kernel computation.
#
#   ./fetch-mathlib-decide.sh [--out DIR] [--cache DIR] [--rerank]
#
# The 150 declarations are listed in data/mathlib-decide-names.txt. They are theorems of the
# Mathlib revision the published planar-graph result pins (so run fetch-zenodo.sh first: this
# reuses its build), whose proof terms use `of_decide_eq_true` (`by decide`, `decide := true`
# and `simp` closing goals by `decide`, found by looking at the proof terms, not the source) and
# are slow to check for their size: mostly matrix and finite-group computations, for example
# CartanMatrix.E₇_det, ZMod.not_isCyclic_units_eight, Nat-valued character computations.
# None depends on an axiom beyond propext, Classical.choice and Quot.sound (no native_decide).
#
# Writes, in OUT/mathlib:
#   mathlib-decide.ndjson        the closure of the 150 declarations (Lean v4.34.0)
#   mathlib-decide-deps.ndjson   the closure of the constants they use directly, without them
#   mathlib-decide.names.txt     the 150 names
#
#   --rerank   instead, time the kernel on every Mathlib theorem whose proof uses
#              `of_decide_eq_true` (about 780; a few minutes, timings vary by machine) and print
#              the selection tools/select_decide.py makes from that to OUT/mathlib/rerank.names.txt;
#              data/mathlib-decide-names.txt is the selection from the run the baselines use.
# The export is about 800 MB. Needs what fetch-zenodo.sh needs.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/common.sh"

RERANK=0
while [[ $# -gt 0 ]]; do
  case $1 in
    --out) OUT=$2; shift ;;
    --cache) CACHE=$2; shift ;;
    --rerank) RERANK=1 ;;
    -h|--help) sed -n '2,25p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "fetch-mathlib-decide: unknown argument $1" >&2; exit 2 ;;
  esac
  shift
done
need elan python3
mkdir -p "$OUT/mathlib"; OUT=$(cd "$OUT" && pwd); CACHE=$(cd "$CACHE" 2>/dev/null && pwd || echo "$CACHE")
LEAN=$CACHE/zenodo/project/lean
[[ -d $LEAN/.lake/build ]] || die "run fetch-zenodo.sh first (it builds the Mathlib this uses)"
EXP434=$(build_exporter 434 "$LEAN4EXPORT_434" "$TC_MAIN")

if [[ $RERANK == 1 ]]; then
  log "timing the kernel on the candidates"
  (ulimit -s unlimited; cd "$LEAN" && lake env lean --run "$HERE/lean/RankDecide.lean" "$OUT/mathlib/rank.tsv" Mathlib Mathlib)
  python3 -I "$HERE/tools/select_decide.py" "$OUT/mathlib/rank.tsv" >"$OUT/mathlib/rerank.names.txt"
  log "wrote $OUT/mathlib/rerank.names.txt"
  exit 0
fi

cp "$HERE/data/mathlib-decide-names.txt" "$OUT/mathlib/mathlib-decide.names.txt"
(ulimit -s unlimited; cd "$LEAN"
 log "dependencies of the declarations (and their axioms)"
 lake env lean --run "$HERE/lean/ListDepsOfNames.lean" "$OUT/mathlib/mathlib-decide.names.txt" Mathlib >"$CACHE/mathlib-decide.deps-names.txt"
 log "export"
 lake env "$EXP434" Mathlib -- $(tr '\n' ' ' <"$OUT/mathlib/mathlib-decide.names.txt") >"$OUT/mathlib/mathlib-decide.ndjson"
 lake env "$EXP434" Mathlib -- $(tr '\n' ' ' <"$CACHE/mathlib-decide.deps-names.txt") >"$OUT/mathlib/mathlib-decide-deps.ndjson")
ls -l "$OUT/mathlib" >&2
log "wrote $OUT/mathlib"
