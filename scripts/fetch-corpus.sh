#!/usr/bin/env bash
# Fetch the kernel-checker test corpus and export it as NDJSON.
#
#   scripts/fetch-corpus.sh [--full] [--out DIR] [--cache DIR] [--update-checksums]
#
# Every source is fetched at a pinned commit and its content is checked against a
# pinned SHA-256; the exports are made with the `leanexport` of the pinned Lean
# toolchain and checked against corpus/exports.sha256, so that every run produces
# the same files byte for byte. See corpus/SOURCES.md for the sources.
#
#   --full              also build the large real-world exports (Init, Std, Mathlib,
#                       ...) that the Arena marks `skip-on-ci`; these take hours and
#                       tens of GB, and are not in corpus/exports.sha256
#   --out DIR           where to put the exports (default: corpus/exports)
#   --cache DIR         where to keep sources and build directories
#                       (default: corpus/.cache)
#   --update-checksums  rewrite corpus/exports.sha256 instead of checking it
#
# Needs git, curl, sha256sum, elan and uv (see mise.corpus.toml).
set -euo pipefail

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
OUT=$ROOT/corpus/exports
CACHE=$ROOT/corpus/.cache
FULL=0
UPDATE=0
while [[ $# -gt 0 ]]; do
  case $1 in
    --full) FULL=1 ;;
    --out) OUT=$2; shift ;;
    --cache) CACHE=$2; shift ;;
    --update-checksums) UPDATE=1 ;;
    -h|--help) sed -n '2,20p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "fetch-corpus: unknown argument $1" >&2; exit 2 ;;
  esac
  shift
done
mkdir -p "$OUT" "$CACHE"
OUT=$(cd "$OUT" && pwd)
CACHE=$(cd "$CACHE" && pwd)

# ---------------------------------------------------------------------------
# Pins

LEAN_TOOLCHAIN=leanprover/lean4:v4.36.0
LEAN_GITHASH=611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9

# name url commit paths-used content-sha256
SOURCES=(
  "arena https://github.com/leanprover/lean-kernel-arena 8a7d0dceea76dfe6fd7bd7f3a6ea216f6347c6aa lka.py,schemas,tests,tutorial bca8d90d563dccae56111676d051f36e5bba3701d5445b9b56611ad96eae1262"
  "lean4 https://github.com/leanprover/lean4 $LEAN_GITHASH tests/pkg/leanchecker e6e4b5d31e95dcf8cc4aefcf899eb943cd2d325ebba43f087941a7142276a126"
  "nanoda https://github.com/ammkrn/nanoda_lib 0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929 test_resources 4221408183f2a6a4c518f5dbe9aa9460e18e1463e532aa7238860c27ef739f6e"
)

# The Python packages lka.py needs are resolved as of this date.
export UV_EXCLUDE_NEWER=2026-11-24T00:00:00Z
export UV_PYTHON=3.12

# ---------------------------------------------------------------------------

log() { printf '%s fetch-corpus: %s\n' "$(date -u +%H:%M:%S)" "$*" >&2; }
die() { printf 'fetch-corpus: error: %s\n' "$*" >&2; exit 1; }
trap 'printf "fetch-corpus: error: command failed at line %s\n" "$LINENO" >&2' ERR

for tool in git curl sha256sum elan uv python3; do
  command -v "$tool" >/dev/null || die "$tool not found (see mise.corpus.toml)"
done
PY=(python3 -I "$ROOT/scripts/corpus.py")

# SHA-256 over the contents of the given paths: the sorted list of the SHA-256s
# of their files, with their paths, hashed again. Independent of git.
content_sha256() {
  local dir=$1; shift
  (cd "$dir" && find "$@" -type f -print0 | LC_ALL=C sort -z | xargs -0 sha256sum) |
    sha256sum | cut -c1-64
}

# fetch_source NAME URL COMMIT PATHS SHA256: check out PATHS of the repository at
# COMMIT into $CACHE/src/NAME and check their contents.
fetch_source() {
  local name=$1 url=$2 commit=$3 paths=$4 want=$5
  local dir=$CACHE/src/$name
  IFS=, read -r -a plist <<<"$paths"
  if [[ ! -d $dir/.git ]]; then
    rm -rf "$dir"
    git init -q "$dir"
    git -C "$dir" remote add origin "$url"
  fi
  if ! git -C "$dir" cat-file -e "$commit^{commit}" 2>/dev/null; then
    log "fetching $name at $commit"
    git -C "$dir" fetch -q --depth 1 --filter=blob:none origin "$commit"
  fi
  git -C "$dir" sparse-checkout set --no-cone "${plist[@]}" 2>/dev/null
  git -C "$dir" -c advice.detachedHead=false checkout -q --force "$commit"
  git -C "$dir" clean -qfdx
  [[ $(git -C "$dir" rev-parse HEAD) == "$commit" ]] || die "$name: not at $commit"
  local got
  got=$(content_sha256 "$dir" "${plist[@]}")
  if [[ $got != "$want" ]]; then
    if [[ $UPDATE == 1 ]]; then
      log "$name: content SHA-256 is $got (pinned: $want)"
    else
      die "$name: content SHA-256 is $got, expected $want"
    fi
  fi
}

# A fresh copy of a fetched source, without its .git directory.
work_copy() {
  local from=$1 to=$2
  rm -rf "$to"
  mkdir -p "$to"
  (cd "$from" && tar --exclude=.git -cf - .) | (cd "$to" && tar -xf -)
}

# ---------------------------------------------------------------------------
# Lean

log "installing $LEAN_TOOLCHAIN"
elan toolchain install "$LEAN_TOOLCHAIN" >/dev/null 2>&1 || elan toolchain install "$LEAN_TOOLCHAIN"
lean_version=$(elan run "$LEAN_TOOLCHAIN" lean --version)
[[ $lean_version == *"commit $LEAN_GITHASH"* ]] || die "unexpected Lean: $lean_version"

for s in "${SOURCES[@]}"; do
  # shellcheck disable=SC2086
  fetch_source $s
done

# The output directory holds nothing but generated files: start afresh.
if [[ -n $(ls -A "$OUT") && ! -f $OUT/manifest.tsv ]]; then
  die "$OUT is not empty and has no manifest.tsv; refusing to clear it"
fi
find "$OUT" -mindepth 1 -delete
MANIFEST=$OUT/manifest.tsv
: >"$MANIFEST.tmp"

WORK=$CACHE/work
mkdir -p "$WORK"

# ---------------------------------------------------------------------------
# Lean Kernel Arena: every test, built by the Arena's own tool.

log "arena: building the tests"
work_copy "$CACHE/src/arena" "$WORK/arena"
arena_args=(build-test)
[[ $FULL == 1 ]] || arena_args+=(--skip-ci)
(cd "$WORK/arena" && uv run --quiet lka.py "${arena_args[@]}") >"$WORK/arena.log" 2>&1 ||
  { tail -40 "$WORK/arena.log" >&2; die "arena: build-test failed (log: $WORK/arena.log)"; }
"${PY[@]}" collect-arena "$WORK/arena/_build/tests" "$OUT" >>"$MANIFEST.tmp"

# Our own test files, written with the Arena's tutorial machinery
# (`good_decl`, `bad_decl`, ...): each test case becomes one export.
log "arena tutorial machinery: building"
(cd "$WORK/arena/tutorial" && lake build -q Tutorial.Meta) >"$WORK/tutorial-meta.log" 2>&1 ||
  { tail -40 "$WORK/tutorial-meta.log" >&2; die "building Tutorial.Meta failed"; }
for pair in lean4lean:Lean4LeanTests historical:HistoricalBugs; do
  source=${pair%%:*}
  file=$ROOT/corpus/lean/${pair#*:}.lean
  log "$source: exporting $(basename "$file")"
  rm -rf "$WORK/$source"
  (cd "$WORK/arena/tutorial" && OUT=$WORK/$source LEAN_ABORT_ON_PANIC=1 lake env lean "$file") \
    >"$WORK/$source.log" 2>&1 ||
    { tail -40 "$WORK/$source.log" >&2; die "$source: exporting $file failed"; }
  "${PY[@]}" collect-cases "$WORK/$source" "$OUT" "$source" >>"$MANIFEST.tmp"
done

# ---------------------------------------------------------------------------
# Lean's leanchecker tests (tests/pkg/leanchecker): the modules that have an
# `.export` file, exported as its run_test.sh does.

log "leanchecker: building the test package"
work_copy "$CACHE/src/lean4/tests/pkg/leanchecker" "$WORK/leanchecker"
echo "$LEAN_TOOLCHAIN" >"$WORK/leanchecker/lean-toolchain"
(cd "$WORK/leanchecker" && lake build -q) >"$WORK/leanchecker.log" 2>&1 ||
  { tail -40 "$WORK/leanchecker.log" >&2; die "leanchecker: lake build failed"; }
mkdir -p "$OUT/leanchecker"
for spec in "$WORK"/leanchecker/LeanCheckerTests/*.lean.export; do
  base=$(basename "$spec" .lean.export)
  module=LeanCheckerTests.$base
  mapfile -t decls <"$spec"
  (cd "$WORK/leanchecker" && lake env leanexport "$module" -- "${decls[@]}") \
    >"$OUT/leanchecker/$base.ndjson" 2>"$WORK/leanchecker-$base.err"
  [[ ! -s $WORK/leanchecker-$base.err ]] ||
    { cat "$WORK/leanchecker-$base.err" >&2; die "leanchecker: leanexport $module failed"; }
  if grep -q "accepts the solution" "$spec.out.expected"; then expected=accept; else expected=reject; fi
  printf 'leanchecker/%s\tleanchecker\t%s\t\t%s\n' "$base" "$expected" \
    "tests/pkg/leanchecker/LeanCheckerTests/$base.lean" >>"$MANIFEST.tmp"
done

# ---------------------------------------------------------------------------
# nanoda_lib's test exports, as they are.

mkdir -p "$OUT/nanoda"
for pair in Empty:accept ProjFromProp:reject; do
  base=${pair%%:*}
  cp "$CACHE/src/nanoda/test_resources/$base/export" "$OUT/nanoda/$base.ndjson"
  printf 'nanoda/%s\tnanoda\t%s\t\t%s\n' "$base" "${pair#*:}" \
    "test_resources/$base/export" >>"$MANIFEST.tmp"
done

# ---------------------------------------------------------------------------

{
  printf 'id\tsource\texpected\ttimeout\torigin\n'
  LC_ALL=C sort "$MANIFEST.tmp"
} >"$MANIFEST"
rm "$MANIFEST.tmp"

SUMS=$ROOT/corpus/exports.sha256
if [[ $UPDATE == 1 ]]; then
  "${PY[@]}" checksums "$OUT" >"$SUMS"
  log "wrote $SUMS"
else
  "${PY[@]}" checksums "$OUT" --check "$SUMS" $([[ $FULL == 1 ]] && echo --allow-extra)
fi
log "$(($(wc -l <"$MANIFEST") - 1)) exports in $OUT"
