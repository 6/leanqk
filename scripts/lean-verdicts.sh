#!/usr/bin/env bash
# Record Lean's own verdict on every export of the corpus, and derive leanqk's.
#
#   scripts/lean-verdicts.sh [--out DIR] [--jobs N]
#
# Runs `leanchecker --from-export` of the pinned Lean on every export in DIR
# (default: corpus/exports, made by scripts/fetch-corpus.sh) and writes
# corpus/expected-lean-v4.36.0.tsv, then corpus/expected-leanqk.tsv from it and
# corpus/divergences.md.
set -euo pipefail
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
OUT=$ROOT/corpus/exports
JOBS=$(nproc 2>/dev/null || echo 2)
while [[ $# -gt 0 ]]; do
  case $1 in
    --out) OUT=$2; shift ;;
    --jobs) JOBS=$2; shift ;;
    *) echo "lean-verdicts: unknown argument $1" >&2; exit 2 ;;
  esac
  shift
done
python3 -I "$ROOT/scripts/corpus.py" lean-verdicts "$OUT" "$ROOT/corpus/expected-lean-v4.36.0.tsv" \
  --jobs "$JOBS" --toolchain leanprover/lean4:v4.36.0
python3 -I "$ROOT/scripts/corpus.py" expected-leanqk "$ROOT/corpus/expected-lean-v4.36.0.tsv" \
  "$ROOT/corpus/divergences.md" "$ROOT/corpus/expected-leanqk.tsv"
