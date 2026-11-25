#!/usr/bin/env bash
# Kernel-only LRAT proofs of growing size, as exports.
#
#   ./fetch-lrat.sh [--out DIR] [--cache DIR] [--only LABEL,...] [--update-pins]
#
# For each instance of data/lrat-instances.tsv (public SAT Competition instances, fetched by
# their hash from benchmark-database.de, content checked against a pinned SHA-256): solve it
# with the pinned CaDiCaL (`--lrat --no-binary`), trim the proof (tools/lrat_trim.py), state
# it as a theorem with the `+kernel` mode of LRAT-Catcher (checker `LRATCatcher.checkKernel`,
# run by the kernel through `of_decide_eq_true (Eq.refl true)`), and export the theorem's
# closure with the lean4export that matches the toolchain (Lean v4.30.0).
#
# The theorem is added to the environment with `debug.skipKernelTC true`, which leaves out
# the kernel's check of the proof; checking it is what the exports are for (Lean's own check
# of the larger ones would take longer than a day). The term is built by BenchLrat.Cmd's
# `kernel_lrat`, which writes the same term as `lrat_reflect +kernel` without going through
# the elaborator. `base` is the same theorem for LRAT-Catcher's own 4-clause example, the
# export every other one contains.
#
# Then the same for the pigeonhole formulas of data/php-instances.tsv (PHP(n+1, n), made by
# LRAT-Catcher's examples/gen_php.py, refuted by the CaDiCaL of the v4.30.0 toolchain).
#
# Writes OUT/lrat/NAME.ndjson and OUT/lrat/manifest.tsv (label, GBD hash, CNF bytes, LRAT
# bytes, export bytes, LRAT SHA-256). Needs git, curl, xz, sha256sum, make, a C++ compiler,
# elan, python3.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/common.sh"

ONLY=""
while [[ $# -gt 0 ]]; do
  case $1 in
    --out) OUT=$2; shift ;;
    --cache) CACHE=$2; shift ;;
    --only) ONLY=$2; shift ;;
    --update-pins) export KC_UPDATE_PINS=1 ;;
    -h|--help) sed -n '2,25p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "fetch-lrat: unknown argument $1" >&2; exit 2 ;;
  esac
  shift
done
need git curl xz sha256sum make c++ elan python3
mkdir -p "$OUT/lrat" "$CACHE"; OUT=$(cd "$OUT" && pwd); CACHE=$(cd "$CACHE" && pwd)

CADICAL_COMMIT=4198d817d0dcde5b1240eefbff70b555b7df2af9   # rel-2.2.1 (no factoring)
CADICAL_SHA256=6f9781faa6a03049e0448761a50a5f327ecaae6b74336b66a6e073abb6af01a5
GBD=https://benchmark-database.de/file
export LC_ALL=C

log "cadical $CADICAL_COMMIT"
fetch_git cadical https://github.com/arminbiere/cadical "$CADICAL_COMMIT" "$CADICAL_SHA256"
CADICAL=$CACHE/src/cadical/build/cadical
[[ -x $CADICAL ]] || (cd "$CACHE/src/cadical" && ./configure >/dev/null && make -j"$(nproc)" >/dev/null 2>&1)

log "BenchLrat (LRAT-Catcher + kernel_lrat) on $TC_CATCHER"
tcdir=$(tc_bin "$TC_CATCHER")
PROJ=$CACHE/lrat-kernel
rm -rf "$PROJ"; mkdir -p "$PROJ"
cp -r "$HERE"/lean/lrat-kernel/. "$PROJ"/
(cd "$PROJ" && PATH=$tcdir:$PATH lake build) >"$CACHE/lrat-kernel-build.log" 2>&1 ||
  { tail -30 "$CACHE/lrat-kernel-build.log" >&2; die "building lean/lrat-kernel failed"; }
EXPORTER=$(build_exporter 430 "$LEAN4EXPORT_430" "$TC_CATCHER")
LEANPATH=$(cd "$PROJ" && PATH=$tcdir:$PATH lake env printenv LEAN_PATH)

WORK=$CACHE/lrat-work; mkdir -p "$WORK"
ROWS=$OUT/lrat/.rows; mkdir -p "$ROWS"   # one manifest row per label, so --only keeps the others

# export_one LABEL CNF LRAT: states and exports the theorem for the pair.
export_one() {
  local label=$1 cnf=$2 lrat=$3 d=$WORK/$1
  mkdir -p "$d"
  cat >"$d/Bench_$label.lean" <<EOF
import BenchLrat
set_option debug.skipKernelTC true
kernel_lrat bench_$label "$cnf" "$lrat"
EOF
  (ulimit -s unlimited
   cd "$PROJ" && PATH=$tcdir:$PATH lake env lean -R "$d" -o "$d/Bench_$label.olean" "$d/Bench_$label.lean")
  (ulimit -s unlimited
   cd "$PROJ" && LEAN_PATH=$d:$LEANPATH PATH=$tcdir:$PATH "$EXPORTER" "Bench_$label" -- "bench_$label") \
     >"$OUT/lrat/$label.ndjson"
}

log "base"
cp "$PROJ"/.lake/packages/LRATCatcher/LRATCatcher/Tests/tiny.{cnf,lrat} "$WORK/"
export_one base "$WORK/tiny.cnf" "$WORK/tiny.lrat"
printf 'base\t-\t%s\t%s\t%s\t%s\n' "$(stat -c %s "$WORK/tiny.cnf")" "$(stat -c %s "$WORK/tiny.lrat")" \
  "$(stat -c %s "$OUT/lrat/base.ndjson")" "$(sha256sum "$WORK/tiny.lrat" | cut -c1-64)" >"$ROWS/base"

tail -n +2 "$HERE/data/lrat-instances.tsv" | while IFS=$'\t' read -r label hash cnf_sha lrat_sha; do
  [[ -z $ONLY || ,$ONLY, == *,$label,* ]] || continue
  d=$WORK/$label; mkdir -p "$d"
  log "$label: instance $hash"
  curl -fsSL --retry 3 -o "$d/f.xz" "$GBD/$hash"
  xz -dc "$d/f.xz" >"$d/f.cnf"
  got=$(sha256sum "$d/f.cnf" | cut -c1-64)
  [[ $got == "$cnf_sha" || ${KC_UPDATE_PINS:-0} == 1 ]] || die "$label: CNF SHA-256 is $got, expected $cnf_sha"
  "$CADICAL" -q --lrat --no-binary "$d/f.cnf" "$d/f.lrat" >"$d/cadical.out" || [[ $? == 20 ]]
  grep -q '^s UNSATISFIABLE' "$d/cadical.out" || die "$label: not unsatisfiable"
  python3 -I "$HERE/tools/lrat_trim.py" "$d/f.lrat" "$d/f.trim.lrat"
  got=$(sha256sum "$d/f.trim.lrat" | cut -c1-64)
  [[ $got == "$lrat_sha" || ${KC_UPDATE_PINS:-0} == 1 ]] || die "$label: LRAT SHA-256 is $got, expected $lrat_sha"
  export_one "$label" "$d/f.cnf" "$d/f.trim.lrat"
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$label" "$hash" "$(stat -c %s "$d/f.cnf")" "$(stat -c %s "$d/f.trim.lrat")" \
    "$(stat -c %s "$OUT/lrat/$label.ndjson")" "$got" >"$ROWS/$label"
  rm -f "$d/f.xz" "$d/f.lrat"   # large; regenerated deterministically
done
# The pigeonhole formulas PHP(n+1, n), from LRAT-Catcher's generator, refuted by the CaDiCaL
# of the v4.30.0 toolchain (2.1.2): a second series, with one proof family growing ~9x a step.
tail -n +2 "$HERE/data/php-instances.tsv" | while IFS=$'\t' read -r label holes cnf_sha lrat_sha; do
  [[ -z $ONLY || ,$ONLY, == *,$label,* ]] || continue
  d=$WORK/$label; mkdir -p "$d"
  log "$label: PHP($((holes + 1)), $holes)"
  python3 -I "$PROJ/.lake/packages/LRATCatcher/examples/gen_php.py" $((holes + 1)) "$holes" >"$d/f.cnf"
  "$tcdir/cadical" -q --lrat --no-binary "$d/f.cnf" "$d/f.lrat" >"$d/cadical.out" || [[ $? == 20 ]]
  for x in cnf:$cnf_sha lrat:$lrat_sha; do
    got=$(sha256sum "$d/f.${x%%:*}" | cut -c1-64)
    [[ $got == "${x#*:}" || ${KC_UPDATE_PINS:-0} == 1 ]] || die "$label: ${x%%:*} SHA-256 is $got, expected ${x#*:}"
  done
  export_one "$label" "$d/f.cnf" "$d/f.lrat"
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$label" "-" "$(stat -c %s "$d/f.cnf")" "$(stat -c %s "$d/f.lrat")" \
    "$(stat -c %s "$OUT/lrat/$label.ndjson")" "$(sha256sum "$d/f.lrat" | cut -c1-64)" >"$ROWS/$label"
  rm -f "$d/f.lrat"
done
{ printf 'label	gbd_hash	cnf_bytes	lrat_bytes	export_bytes	lrat_sha256
'
  cat "$ROWS"/* | sort -t "$(printf "\t")" -k4,4n; } >"$OUT/lrat/manifest.tsv"
log "wrote $OUT/lrat"
