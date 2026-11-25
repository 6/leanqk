#!/usr/bin/env bash
# Check that nitrolean's .olean reader builds the same environment as Lean's
# NDJSON exporter: every exported declaration must be in the oleans with a
# structurally identical type, value and other fields.
#
# Usage: scripts/olean-equivalence.sh MODULE [WORKDIR]
#
# MODULE is Init, Std, Lean or Mathlib. WORKDIR (default: a new temporary
# directory) holds the export and, for Mathlib, a Mathlib checkout with its
# cached build. Needs elan, git and curl; the Mathlib export takes about
# 15 GB of memory and 10 GB of disk.
set -euo pipefail

mod=${1:?usage: $0 MODULE [WORKDIR]}
work=${2:-$(mktemp -d)}
toolchain=leanprover/lean4:v4.36.0
mathlib_tag=v4.36.0
mathlib_commit=fc4f59e577feb1a4956671bc04ac18aaaf8cd842
repo=$(cd "$(dirname "$0")/.." && pwd)
mkdir -p "$work"
work=$(cd "$work" && pwd)

elan toolchain install "$toolchain" >/dev/null
lean_prefix=$(elan run "$toolchain" lean --print-prefix)
export PATH="$lean_prefix/bin:$PATH"

(cd "$repo" && cargo build --release --quiet)
nitrolean="$repo/target/release/nitrolean"
timefmt='%e s, peak RSS %M KB'

case "$mod" in
  Mathlib)
    if [ ! -d "$work/mathlib4" ]; then
      git -c advice.detachedHead=false clone --quiet --depth 1 --branch "$mathlib_tag" \
        https://github.com/leanprover-community/mathlib4 "$work/mathlib4"
    fi
    got=$(git -C "$work/mathlib4" rev-parse HEAD)
    if [ "$got" != "$mathlib_commit" ]; then
      echo "mathlib4 $mathlib_tag is at $got, expected $mathlib_commit" >&2
      exit 2
    fi
    (cd "$work/mathlib4" && lake exe cache get >/dev/null)
    export_cmd=(lake env leanexport Mathlib)
    target="$work/mathlib4"
    run_dir="$work/mathlib4"
    ;;
  Init | Std | Lean)
    export_cmd=(leanexport "$mod")
    target="$mod"
    run_dir="$work"
    ;;
  *)
    echo "unknown module $mod (Init, Std, Lean or Mathlib)" >&2
    exit 2
    ;;
esac

out="$work/$mod.ndjson"
if [ ! -s "$out" ]; then
  echo "exporting $mod"
  (cd "$run_dir" && /usr/bin/time -f "export: $timefmt" "${export_cmd[@]}" >"$out.tmp")
  mv "$out.tmp" "$out"
fi
ls -l "$out"
echo "comparing"
(cd "$run_dir" && /usr/bin/time -f "compare: $timefmt" "$nitrolean" compare "$out" "$target")
