#!/usr/bin/env bash
# Build the Lean Kernel Arena's test set at the arena's pinned versions.
#
#   bench/arena/fetch.sh [--out DIR] [--cache DIR] [--small | --large | --all]
#                        [--keep-work] [TEST-GLOB...]
#
# Fetches the arena at the commit pinned below, checks the SHA-256 of its
# sources, installs the Lean toolchain the arena exports with, and builds the
# exports with the arena's own `lka.py build-test`, exactly as the arena does.
# Every export is then checked against the SHA-256 the arena published for it
# (bench/arena/tests.tsv), and the SHA-256s of everything built are written to
# OUT/SHA256SUMS. A test whose export differs from the arena's is an error.
#
#   --small       the tests the arena builds on CI (no `skip-on-ci`); default
#   --large       only the large real-world tests (`skip-on-ci`): init, std,
#                 cedar, con-leche, cslib, mathlib, navier-stokes-euler,
#                 reachability, perf/gf3-matrix-product. Mathlib alone needs
#                 ~25 GB of disk and ~16 GB of RAM to export
#   --all         every test
#   TEST-GLOB     only tests whose name matches (lka.py's own patterns, e.g.
#                 'perf/*' or std); combined with --small/--large as a filter
#   --out DIR     where the exports go (default: bench/arena/data/exports)
#   --cache DIR   sources, build directories and lka.py's export cache
#                 (default: bench/arena/data/cache)
#   --keep-work   keep the projects lka.py built (by default they are
#                 removed after their exports are collected, to save disk)
#   --export-cache DIR
#                 let lka.py keep a copy of each export of a pinned project in
#                 DIR and reuse it next time (costs as much disk again)
#
# Needs git, curl, sha256sum, elan, uv and python3.
set -euo pipefail

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
OUT=$HERE/data/exports
CACHE=$HERE/data/cache
SELECT=small
KEEP_WORK=0
EXPORT_CACHE=
PATTERNS=()
while [[ $# -gt 0 ]]; do
  case $1 in
    --out) OUT=$2; shift ;;
    --cache) CACHE=$2; shift ;;
    --small) SELECT=small ;;
    --large) SELECT=large ;;
    --all) SELECT=all ;;
    --keep-work) KEEP_WORK=1 ;;
    --export-cache) EXPORT_CACHE=$2; shift ;;
    -h | --help) sed -n '2,31p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    -*) echo "fetch: unknown option $1" >&2; exit 2 ;;
    *) PATTERNS+=("$1") ;;
  esac
  shift
done

# ---------------------------------------------------------------------------
# Pins

ARENA_URL=https://github.com/leanprover/lean-kernel-arena
ARENA_COMMIT=8a7d0dceea76dfe6fd7bd7f3a6ea216f6347c6aa
# SHA-256 over lka.py, schemas/, tests/ and tutorial/ at ARENA_COMMIT (see
# content_sha256 below).
ARENA_PATHS=lka.py,schemas,tests,tutorial
ARENA_SHA256=bca8d90d563dccae56111676d051f36e5bba3701d5445b9b56611ad96eae1262
# The toolchain of the arena's tests/lean-toolchain; its bundled `leanexport`
# writes the exports.
LEAN_TOOLCHAIN=leanprover/lean4:v4.36.0
LEAN_GITHASH=611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9
# The Python packages lka.py needs, as resolved on this date.
export UV_EXCLUDE_NEWER=2026-11-24T00:00:00Z
export UV_PYTHON=3.12

# ---------------------------------------------------------------------------

log() { printf '%s fetch: %s\n' "$(date -u +%H:%M:%S)" "$*" >&2; }
die() { printf 'fetch: error: %s\n' "$*" >&2; exit 1; }

for tool in git curl sha256sum elan uv python3; do
  command -v "$tool" >/dev/null || die "$tool not found"
done
mkdir -p "$OUT" "$CACHE"
OUT=$(cd "$OUT" && pwd)
CACHE=$(cd "$CACHE" && pwd)
PIN=(python3 -I "$HERE/pin.py")

# SHA-256 over the contents of the given paths: the sorted list of the SHA-256s
# of their files, with their paths, hashed again. Independent of git.
content_sha256() {
  local dir=$1; shift
  (cd "$dir" && find "$@" -type f -print0 | LC_ALL=C sort -z | xargs -0 sha256sum) |
    sha256sum | cut -c1-64
}

# The arena at its pinned commit.
SRC=$CACHE/arena-src
if [[ ! -d $SRC/.git ]]; then
  rm -rf "$SRC"
  git init -q "$SRC"
  git -C "$SRC" remote add origin "$ARENA_URL"
fi
if ! git -C "$SRC" cat-file -e "$ARENA_COMMIT^{commit}" 2>/dev/null; then
  log "fetching the arena at $ARENA_COMMIT"
  git -C "$SRC" fetch -q --depth 1 origin "$ARENA_COMMIT"
fi
git -C "$SRC" -c advice.detachedHead=false checkout -q --force "$ARENA_COMMIT"
git -C "$SRC" clean -qfdx
IFS=, read -r -a arena_paths <<<"$ARENA_PATHS"
got=$(content_sha256 "$SRC" "${arena_paths[@]}")
[[ $got == "$ARENA_SHA256" ]] || die "arena sources: SHA-256 $got, expected $ARENA_SHA256"

# Lean.
log "installing $LEAN_TOOLCHAIN"
elan toolchain install "$LEAN_TOOLCHAIN" >/dev/null 2>&1 || elan toolchain install "$LEAN_TOOLCHAIN"
lean_version=$(elan run "$LEAN_TOOLCHAIN" lean --version)
[[ $lean_version == *"commit $LEAN_GITHASH"* ]] || die "unexpected Lean: $lean_version"

# A working copy of the arena: lka.py writes its exports to _build/tests.
WORK=$CACHE/arena
rm -rf "$WORK/_build/tests"
mkdir -p "$WORK"
(cd "$SRC" && tar --exclude=.git -cf - .) | (cd "$WORK" && tar -xf -)

args=(build-test)
[[ -z $EXPORT_CACHE ]] || args+=(--cache "$EXPORT_CACHE")
case $SELECT in
  small) args+=(--skip-ci) ;;
  large)
    mapfile -t large < <(awk -F'\t' 'NR > 1 && $6 == "yes" { print $1 }' "$HERE/tests.tsv")
    if [[ ${#PATTERNS[@]} -gt 0 ]]; then
      sel=()
      for t in "${large[@]}"; do
        for p in "${PATTERNS[@]}"; do
          # shellcheck disable=SC2053 # patterns are globs
          [[ $t == $p ]] && { sel+=("$t"); break; }
        done
      done
      PATTERNS=("${sel[@]}")
      [[ ${#PATTERNS[@]} -gt 0 ]] || die "no large test matches"
    else
      PATTERNS=("${large[@]}")
    fi
    ;;
esac
args+=("${PATTERNS[@]}")

# lka.py runs each test's pre-build with /bin/sh; the arena's is bash (in its
# nix shell), and cedar's pre-build uses `shopt`. Elsewhere it fails.
if [[ $SELECT != small ]] && ! /bin/sh -c 'shopt -s dotglob' 2>/dev/null; then
  log "warning: /bin/sh is not bash; cedar's pre-build will fail (see README)"
fi

log "building: lka.py ${args[*]}"
LOG=$CACHE/build-test.log
(cd "$WORK" && uv run --quiet lka.py "${args[@]}") >"$LOG" 2>&1 ||
  { tail -40 "$LOG" >&2; die "lka.py build-test failed (log: $LOG)"; }

"${PIN[@]}" collect "$WORK/_build/tests" "$OUT"
[[ $KEEP_WORK == 1 ]] || rm -rf "$WORK/_build/tests/work"
"${PIN[@]}" verify "$OUT"
log "exports in $OUT, their SHA-256s in $OUT/SHA256SUMS"
