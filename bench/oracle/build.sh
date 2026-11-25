#!/usr/bin/env bash
# Build the pinned projects and export each one.
#
#   bench/oracle/build.sh [--tier N] [--only ID,...] [--out DIR] [--cache DIR] [--update-pins]
#
#   --tier N     the projects of projects.tsv with tier <= N (default 1)
#   --only IDS   these projects instead, whatever their tier
#   --out DIR    where the exports go (default bench/oracle/out, or $ORACLE_OUT)
#   --cache DIR  sources and build trees (default bench/oracle/cache, or $ORACLE_CACHE)
#   --update-pins  record export SHA-256s that differ from exports.sha256 instead of stopping
#
# For each project: a checkout at the pinned commit (its lean-toolchain must be the pinned
# one), `lake exe cache get` if the project asks for it, `lake build` of its roots, then the
# list of the non-internal constants declared in its own modules and the export of their
# closure with the exporter of that toolchain. Writes, in OUT/<id>/:
#   export.ndjson     the export (not committed)
#   own-names.txt     the constants it is the closure of
#   build.env         toolchain, project directory and roots, for run.py
# and checks the export's SHA-256 against exports.sha256 (an id not listed there is added).
# Needs git, elan, sha256sum. A project already built is not rebuilt.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/common.sh"

TIER=1; ONLY=; UPDATE=0
while [[ $# -gt 0 ]]; do
  case $1 in
    --tier) TIER=$2; shift ;;
    --only) ONLY=$2; shift ;;
    --out) OUT=$2; shift ;;
    --cache) CACHE=$2; shift ;;
    --update-pins) UPDATE=1 ;;
    -h|--help) sed -n '2,21p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "build: unknown argument $1" >&2; exit 2 ;;
  esac
  shift
done
need git elan sha256sum
mkdir -p "$OUT" "$CACHE/src"; OUT=$(cd "$OUT" && pwd); CACHE=$(cd "$CACHE" && pwd)
SUMS=$HERE/exports.sha256
touch "$SUMS"

build_one() {
  local id=$1 tc=$2 url=$3 commit=$4 subdir=$5 roots=$6 prefixes=$7 cache=$8
  local src=$CACHE/src/$id dir out=$OUT/$id bin exp
  dir=$src/$subdir
  mkdir -p "$out"
  if [[ ! -d $src/.git ]]; then
    git init -q "$src"; git -C "$src" remote add origin "$url"
  fi
  if ! git -C "$src" cat-file -e "$commit^{commit}" 2>/dev/null; then
    log "$id: fetching $commit"
    git -C "$src" fetch -q --depth 1 origin "$commit"
  fi
  git -C "$src" -c advice.detachedHead=false checkout -q --force "$commit"
  [[ $(git -C "$src" rev-parse HEAD) == "$commit" ]] || die "$id: not at $commit"
  [[ $(tr -d '[:space:]' <"$dir/lean-toolchain") == "$tc" ]] ||
    die "$id: lean-toolchain is $(cat "$dir/lean-toolchain"), pinned $tc"
  bin=$(tc_bin "$tc")
  exp=$(exporter "$tc")
  local r=${roots//,/ } p=${prefixes//,/ }
  (
    export PATH=$bin:$PATH
    cd "$dir"
    if [[ $cache == yes ]]; then log "$id: lake exe cache get"; lake exe cache get >&2; fi
    log "$id: lake build $r ($tc)"
    # shellcheck disable=SC2086
    lake build $r >"$out/build.log" 2>&1 || { tail -30 "$out/build.log" >&2; exit 1; }
    ulimit -s unlimited  # the name list is passed on the command line
    log "$id: own declarations"
    # shellcheck disable=SC2086
    lake env lean --run "$HERE/../kernel-compute/lean/ListOwn.lean" $r -- $p >"$out/own-names.txt"
    log "$id: export ($(wc -l <"$out/own-names.txt") names)"
    # shellcheck disable=SC2086,SC2046
    lake env "$exp" $r -- $(tr '\n' ' ' <"$out/own-names.txt") >"$out/export.ndjson.part"
  ) || die "$id: build or export failed"
  mv "$out/export.ndjson.part" "$out/export.ndjson"
  {
    printf 'toolchain=%s\n' "$tc"
    printf 'project_dir=%s\n' "$dir"
    printf 'roots=%s\n' "$roots"
    printf 'commit=%s\n' "$commit"
  } >"$out/build.env"
  local got want
  got=$(sha256sum "$out/export.ndjson" | cut -c1-64)
  want=$(awk -v f="$id.ndjson" '$2 == f { print $1 }' "$SUMS")
  if [[ -z $want ]]; then
    printf '%s  %s\n' "$got" "$id.ndjson" >>"$SUMS"; sort -k2 -o "$SUMS" "$SUMS"
    log "$id: recorded SHA-256 $got"
  elif [[ $got != "$want" ]]; then
    if [[ $UPDATE == 1 ]]; then
      awk -v f="$id.ndjson" -v h="$got" '$2 == f { $1 = h; print $1 "  " $2; next } { print }' "$SUMS" >"$SUMS.new"
      mv "$SUMS.new" "$SUMS"; log "$id: SHA-256 now $got (was $want)"
    else die "$id: export SHA-256 is $got, pinned $want (--update-pins to accept it)"; fi
  fi
  log "$id: $(wc -l <"$out/export.ndjson") lines, $(du -h "$out/export.ndjson" | cut -f1)"
}

n=0
while IFS=$'\t' read -r id _tier tc url commit subdir roots prefixes cache; do
  if [[ -f $OUT/$id/export.ndjson && -f $OUT/$id/build.env ]] &&
     grep -qx "commit=$commit" "$OUT/$id/build.env"; then
    log "$id: already built"; n=$((n + 1)); continue
  fi
  build_one "$id" "$tc" "$url" "$commit" "$subdir" "$roots" "$prefixes" "$cache"
  n=$((n + 1))
done < <(projects "$TIER" "$ONLY")
((n > 0)) || die "no project selected"
log "built $n project(s) in $OUT"
