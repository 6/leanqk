#!/usr/bin/env bash
# Build nitrolean, build and export the projects of a tier, and run the oracle on them.
#
#   bench/oracle/oracle.sh [--tier N] [--only ID,...] [run.py options...]
#
# The same as `cargo build --release`, `build.sh --tier N` and `run.py --tier N`; options
# other than --tier and --only go to run.py. Writes bench/oracle/RESULTS.md. Exit status 1
# if a project disagrees or a variant differs.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/common.sh"
TIER=1; ONLY=; REST=()
while [[ $# -gt 0 ]]; do
  case $1 in
    --tier) TIER=$2; shift ;;
    --only) ONLY=$2; shift ;;
    -h|--help) sed -n '2,8p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) REST+=("$1") ;;
  esac
  shift
done
need cargo python3
(cd "$HERE/../.." && cargo build --release --locked --bin nitrolean) >&2
sel=(--tier "$TIER"); [[ -n $ONLY ]] && sel=(--only "$ONLY")
"$HERE/build.sh" "${sel[@]}"
exec python3 -I "$HERE/run.py" "${sel[@]}" "${REST[@]}"
