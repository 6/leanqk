#!/usr/bin/env bash
# Build the published planar-graph result and export its declarations' closure.
#
#   ./fetch-zenodo.sh [--out DIR] [--cache DIR] [--update-pins]
#
# The result is doi:10.5281/zenodo.24467489, taken from its released file
# steinberg-c4-c9-v9.zip (SHA-256 pinned below) and nothing else: a Lean v4.34.0 + Mathlib
# project (the Mathlib revision is in its lake-manifest.json; the Mathlib .olean files come
# from `lake exe cache get`) and its `lean/catcher` subproject on Lean v4.30.0. Both are built
# unchanged, then exported with the lean4export commit that matches each toolchain.
#
# Writes, in OUT/zenodo:
#   steinberg-main.ndjson          closure of the project's own declarations (Lean v4.34.0)
#   steinberg-main-deps.ndjson     the same without the own declarations: closure of the
#                                  constants they use directly. Subtract the checking time
#                                  of this from that of the full export to time the own ones.
#   steinberg-main.own-names.txt   the own declarations (modules LocalRup, Steinberg, Check,
#                                  PublishedInput, Challenge; names without `_` components)
#   steinberg-catcher*.ndjson, steinberg-catcher.own-names.txt   the same for lean/catcher
#                                  (Lean v4.30.0; modules PublishedCatcher, RupPieces, PublishedInput)
# Needs curl, unzip, sha256sum, git, elan. Takes a few minutes; downloads about 6 GB of Mathlib build.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/common.sh"

while [[ $# -gt 0 ]]; do
  case $1 in
    --out) OUT=$2; shift ;;
    --cache) CACHE=$2; shift ;;
    --update-pins) export KC_UPDATE_PINS=1 ;;
    -h|--help) sed -n '2,22p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "fetch-zenodo: unknown argument $1" >&2; exit 2 ;;
  esac
  shift
done
need curl unzip sha256sum git elan
mkdir -p "$OUT/zenodo" "$CACHE"; OUT=$(cd "$OUT" && pwd); CACHE=$(cd "$CACHE" && pwd)

ZIP_URL=https://zenodo.org/records/24467489/files/steinberg-c4-c9-v9.zip
ZIP_SHA256=e5f60791343376f3974642d836e7c0daf5a143a232584662e3a221d481c7df73

fetch_url "$ZIP_URL" "$ZIP_SHA256" "$CACHE/zenodo/steinberg-c4-c9-v9.zip"
if [[ ! -d $CACHE/zenodo/project ]]; then
  log "unpacking"
  rm -rf "$CACHE/zenodo/unpack"; mkdir -p "$CACHE/zenodo/unpack"
  unzip -q "$CACHE/zenodo/steinberg-c4-c9-v9.zip" -d "$CACHE/zenodo/unpack"
  mv "$CACHE/zenodo/unpack/steinberg-c4-c9-v9/results/steinberg-c4-c9" "$CACHE/zenodo/project"
  rm -rf "$CACHE/zenodo/unpack"
fi
LEAN=$CACHE/zenodo/project/lean
[[ $(cat "$LEAN/lean-toolchain") == "$TC_MAIN" ]] || die "unexpected toolchain $(cat "$LEAN/lean-toolchain")"
[[ $(cat "$LEAN/catcher/lean-toolchain") == "$TC_CATCHER" ]] || die "unexpected catcher toolchain"

log "main project: lake exe cache get, lake build ($TC_MAIN)"
elan toolchain install "$TC_MAIN" "$TC_CATCHER" >/dev/null 2>&1 || true
(cd "$LEAN" && lake exe cache get && lake build) >"$CACHE/zenodo/build-main.log" 2>&1 ||
  { tail -30 "$CACHE/zenodo/build-main.log" >&2; die "building the main project failed"; }
log "catcher subproject ($TC_CATCHER)"
(cd "$LEAN/catcher" && lake build) >"$CACHE/zenodo/build-catcher.log" 2>&1 ||
  { tail -30 "$CACHE/zenodo/build-catcher.log" >&2; die "building lean/catcher failed"; }

EXP434=$(build_exporter 434 "$LEAN4EXPORT_434" "$TC_MAIN")
EXP430=$(build_exporter 430 "$LEAN4EXPORT_430" "$TC_CATCHER")

# export_set DIR EXPORTER NAME ROOTS PREFIXES: own names, full export, deps-only export.
export_set() {
  local dir=$1 exporter=$2 name=$3 roots=$4 prefixes=$5
  (ulimit -s unlimited; cd "$dir"
   log "$name: own declarations"
   lake env lean --run "$HERE/lean/ListOwn.lean" $roots -- $prefixes >"$OUT/zenodo/$name.own-names.txt"
   log "$name: export"
   lake env "$exporter" $roots -- $(tr '\n' ' ' <"$OUT/zenodo/$name.own-names.txt") >"$OUT/zenodo/$name.ndjson"
   lake env lean --run "$HERE/lean/ListDeps.lean" $roots -- $prefixes >"$CACHE/zenodo/$name.deps-names.txt"
   lake env "$exporter" $roots -- $(tr '\n' ' ' <"$CACHE/zenodo/$name.deps-names.txt") >"$OUT/zenodo/$name-deps.ndjson")
}
export_set "$LEAN" "$EXP434" steinberg-main "Challenge Check PublishedInput" "LocalRup Steinberg Check PublishedInput Challenge"
export_set "$LEAN/catcher" "$EXP430" steinberg-catcher "PublishedCatcher RupPieces PublishedInput" "PublishedCatcher RupPieces PublishedInput"

( cd "$OUT/zenodo" && wc -lc ./*.own-names.txt ./*.ndjson | sed 's/^/  /' ) >&2
log "wrote $OUT/zenodo"
