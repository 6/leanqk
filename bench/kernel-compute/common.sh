# Shared helpers and pins for the scripts in this directory. Sourced, not run.
# shellcheck shell=bash

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
CACHE=${KC_CACHE:-$HERE/cache}      # sources, build trees, checker binaries (gitignored)
OUT=${KC_OUT:-$HERE/out}            # generated exports and tables (gitignored)

log() { printf '%s %s: %s\n' "$(date -u +%H:%M:%S)" "$(basename "$0" .sh)" "$*" >&2; }
die() { printf '%s: error: %s\n' "$(basename "$0" .sh)" "$*" >&2; exit 1; }
trap 'printf "%s: error: command failed at line %s\n" "$(basename "$0" .sh)" "$LINENO" >&2' ERR

need() { for t in "$@"; do command -v "$t" >/dev/null || die "$t not found (see README.md)"; done; }

# Toolchains (installed with elan) and the lean4export commit that matches each.
TC_MAIN=leanprover/lean4:v4.34.0     # the published project and Mathlib
TC_CATCHER=leanprover/lean4:v4.30.0  # its lean/catcher subproject, and LRAT-Catcher
TC_CHECK=leanprover/lean4:v4.36.0    # leanchecker, the toolchain nitrolean targets
LEAN4EXPORT_URL=https://github.com/leanprover/lean4export
LEAN4EXPORT_434=076e8e57707e813375e8f9da8bf989799ace9680   # "bump toolchain to v4.34.0"
LEAN4EXPORT_430=a3e35a584f59b390667db7269cd37fca8575e4bf   # "bump toolchain to v4.30.0"

tc_bin() { # tc_bin TOOLCHAIN -> directory with lean, lake, leanchecker
  local tc=$1
  elan toolchain install "$tc" >/dev/null 2>&1 || elan toolchain install "$tc" >&2
  echo "$(elan run "$tc" lean --print-prefix)/bin"
}

# fetch_git NAME URL COMMIT CONTENT_SHA256: a checkout of URL at COMMIT in
# $CACHE/src/NAME (no .git history beyond that commit), checked against the pinned
# content hash. With KC_UPDATE_PINS=1 a mismatch is only reported.
fetch_git() {
  local name=$1 url=$2 commit=$3 want=$4 dir=$CACHE/src/$1
  if [[ ! -d $dir/.git ]]; then
    rm -rf "$dir"; mkdir -p "$dir"
    git init -q "$dir"; git -C "$dir" remote add origin "$url"
  fi
  if ! git -C "$dir" cat-file -e "$commit^{commit}" 2>/dev/null; then
    log "fetching $name at $commit"
    git -C "$dir" fetch -q --depth 1 origin "$commit"
  fi
  git -C "$dir" -c advice.detachedHead=false checkout -q --force "$commit"
  git -C "$dir" clean -qfdx
  [[ $(git -C "$dir" rev-parse HEAD) == "$commit" ]] || die "$name: not at $commit"
  local got
  got=$( (cd "$dir" && find . -path ./.git -prune -o -type f -print0 | LC_ALL=C sort -z | xargs -0 sha256sum) | sha256sum | cut -c1-64)
  if [[ $got != "$want" ]]; then
    if [[ ${KC_UPDATE_PINS:-0} == 1 ]]; then log "$name: content SHA-256 is $got (pinned: $want)"
    else die "$name: content SHA-256 is $got, expected $want"; fi
  fi
}

# fetch_url URL SHA256 FILE: download URL to FILE unless FILE already has that hash.
fetch_url() {
  local url=$1 want=$2 file=$3
  if [[ -f $file ]] && [[ $(sha256sum "$file" | cut -c1-64) == "$want" ]]; then return; fi
  mkdir -p "$(dirname "$file")"
  curl -fsSL --retry 3 -o "$file.part" "$url"
  [[ $(sha256sum "$file.part" | cut -c1-64) == "$want" ]] || die "$url: SHA-256 mismatch"
  mv "$file.part" "$file"
}

# lean4export built with the matching toolchain: build_exporter NAME COMMIT TOOLCHAIN
# leaves $CACHE/lean4export-NAME/.lake/build/bin/lean4export.
build_exporter() {
  local name=$1 commit=$2 tc=$3 dir=$CACHE/lean4export-$1
  if [[ ! -x $dir/.lake/build/bin/lean4export ]]; then
    rm -rf "$dir"; mkdir -p "$dir"
    git -C "$dir" init -q; git -C "$dir" remote add origin "$LEAN4EXPORT_URL"
    git -C "$dir" fetch -q --depth 1 origin "$commit"
    git -C "$dir" -c advice.detachedHead=false checkout -q "$commit"
    [[ $(cat "$dir/lean-toolchain") == "$tc" ]] || die "lean4export $commit is for $(cat "$dir/lean-toolchain"), not $tc"
    (cd "$dir" && elan run "$tc" lake build) >&2
  fi
  echo "$dir/.lake/build/bin/lean4export"
}
