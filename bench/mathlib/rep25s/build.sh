#!/usr/bin/env bash
# Builds rep25s, a dependency-closed slice of Mathlib v4.36.0 (README.md):
#
#   build.sh MATHLIB_CHECKOUT OUT.ndjson
#
# Clones Mathlib at v4.36.0 into MATHLIB_CHECKOUT unless it is there, fetches
# its prebuilt .olean files (lake exe cache get), exports the declarations
# listed in rep25s.roots.jsonl.zst with everything they depend on, and checks
# the result's line count, size and SHA-256. Needs elan with
# leanprover/lean4:v4.36.0, git and zstd.
set -euo pipefail
if [[ $# != 2 ]]; then
    echo "usage: $0 MATHLIB_CHECKOUT OUT.ndjson" >&2
    exit 2
fi
recipe=$(cd "$(dirname "$0")" && pwd)
checkout=$(realpath -m "$1")
output=$(realpath -m "$2")
mathlib_rev=fc4f59e577feb1a4956671bc04ac18aaaf8cd842
toolchain=leanprover/lean4:v4.36.0
roots="$recipe/rep25s.roots.jsonl.zst"

printf '%s  %s\n' aa8beb3c2e868cdfcdf51f4f32c6e9d9536ebb3116fbe525ad9f4ff89022a606 "$roots" |
    sha256sum --check --strict --quiet
if [[ ! -e "$checkout" ]]; then
    mkdir -p "$(dirname "$checkout")"
    git clone -q --depth 1 --branch v4.36.0 https://github.com/leanprover-community/mathlib4.git "$checkout"
fi
test "$(git -C "$checkout" rev-parse HEAD)" = "$mathlib_rev"
test "$(cat "$checkout/lean-toolchain")" = "$toolchain"

mkdir -p "$(dirname "$output")"
tmp=$(mktemp -d "$(dirname "$output")/.rep25s.XXXXXXXX")
trap 'rm -rf -- "$tmp"' EXIT
zstd -q -d -c "$roots" > "$tmp/roots.jsonl"
(
    cd "$checkout"
    export ELAN_TOOLCHAIN="$toolchain"
    lake exe cache get
    lake env lean --run "$recipe/OrderedExport.lean" "$tmp/roots.jsonl" > "$tmp/rep25s.ndjson"
)
test "$(wc -l < "$tmp/rep25s.ndjson")" -eq 6881298
test "$(wc -c < "$tmp/rep25s.ndjson")" -eq 367621205
printf '%s  %s\n' e8aff3c872ae2b052b49646047f1e6ce331f29e14c394eb4f845a3b01e47b768 "$tmp/rep25s.ndjson" |
    sha256sum --check --strict
mv -f "$tmp/rep25s.ndjson" "$output"
