# Shared helpers and pins for the scripts in this directory. Sourced, not run.
# shellcheck shell=bash

HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
CACHE=${ORACLE_CACHE:-$HERE/cache}   # sources and build trees (gitignored)
OUT=${ORACLE_OUT:-$HERE/out}         # exports, logs, results (gitignored)
PROJECTS=$HERE/projects.tsv

log() { printf '%s %s: %s\n' "$(date -u +%H:%M:%S)" "$(basename "$0" .sh)" "$*" >&2; }
die() { printf '%s: error: %s\n' "$(basename "$0" .sh)" "$*" >&2; exit 1; }
need() { for t in "$@"; do command -v "$t" >/dev/null || die "$t not found (see README.md)"; done; }

# The toolchain whose `leanchecker --from-export` gives Lean's verdict. Older toolchains'
# leanchecker has no --from-export (it came with v4.35.0), so their exports are checked by
# v4.36.0, the version nitrolean targets; the export format (3.1) is the same.
check_toolchain() {
  case $1 in
    leanprover/lean4:v4.2[89].* | leanprover/lean4:v4.3[0-4].*) echo leanprover/lean4:v4.36.0 ;;
    *) echo "$1" ;;
  esac
}

# The exporter: from v4.35.0 on, `leanexport` ships with the toolchain; before, it is
# github.com/leanprover/lean4export at the commit that bumps it to that toolchain.
LEAN4EXPORT_URL=https://github.com/leanprover/lean4export
lean4export_commit() {
  case $1 in
    leanprover/lean4:v4.28.0) echo ca36c44858e2d7ba40996203d2f08a69113d1211 ;;
    leanprover/lean4:v4.29.0) echo caccfbebbc99077962b3321125b2375bb3fa22db ;;
    leanprover/lean4:v4.30.0) echo a3e35a584f59b390667db7269cd37fca8575e4bf ;;
    leanprover/lean4:v4.31.0) echo 8554815c2dc6b7abe99ec1f08849c9759ba77947 ;;
    leanprover/lean4:v4.32.0) echo 4e7915201d3f9f04470d9eae002fa695f7cdc589 ;;
    leanprover/lean4:v4.33.0) echo 15f6055e299ad5b89345e533cc2192f4cc00f659 ;;
    leanprover/lean4:v4.34.0) echo 076e8e57707e813375e8f9da8bf989799ace9680 ;;
    *) return 1 ;;
  esac
}

tc_bin() { # tc_bin TOOLCHAIN -> directory with lean, lake, leanchecker
  local tc=$1
  elan toolchain install "$tc" >/dev/null 2>&1 || elan toolchain install "$tc" >&2
  echo "$(elan run "$tc" lean --print-prefix)/bin"
}

exporter() { # exporter TOOLCHAIN -> path of the exporter for it
  local tc=$1 bin commit dir
  bin=$(tc_bin "$tc")
  if [[ -x $bin/leanexport ]]; then echo "$bin/leanexport"; return; fi
  commit=$(lean4export_commit "$tc") || die "no exporter pinned for $tc"
  dir=$CACHE/lean4export-${commit:0:12}
  if [[ ! -x $dir/.lake/build/bin/lean4export ]]; then
    rm -rf "$dir"; mkdir -p "$dir"
    git -C "$dir" init -q; git -C "$dir" remote add origin "$LEAN4EXPORT_URL"
    git -C "$dir" fetch -q --depth 1 origin "$commit"
    git -C "$dir" -c advice.detachedHead=false checkout -q "$commit"
    [[ $(cat "$dir/lean-toolchain") == "$tc" ]] || die "lean4export $commit is for $(cat "$dir/lean-toolchain"), not $tc"
    (cd "$dir" && PATH=$bin:$PATH lake build) >&2
  fi
  echo "$dir/.lake/build/bin/lean4export"
}

# projects TIER ONLY: the lines of projects.tsv with tier <= TIER (or whose id is in the
# comma list ONLY, when it is not empty), without comments.
projects() {
  local tier=$1 only=$2
  grep -v '^#' "$PROJECTS" | grep -v '^[[:space:]]*$' | while IFS=$'\t' read -r id t rest; do
    if [[ -n $only ]]; then [[ ,$only, == *,$id,* ]] || continue
    else ((t <= tier)) || continue; fi
    printf '%s\t%s\t%s\n' "$id" "$t" "$rest"
  done
}
