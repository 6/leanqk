#!/usr/bin/env bash
# Build the four checkers that measure.sh compares, each at a pinned commit.
#
#   ./build-checkers.sh [--cache DIR] [--nitrolean DIR] [--update-pins]
#
#   nitrolean   built from the checkout this directory is in (or --nitrolean DIR);
#               its commit is recorded, it is not pinned here
#   gruszka     github.com/jasisz/gruszka, with `susz` (crates.io, pinned version),
#               which converts an export to the binary form gruszka reads
#   nano-lean   github.com/sdiehl/nano-lean, the `nl-fast` binary
#   leanchecker the one of the Lean toolchain nitrolean targets (v4.36.0); not built, installed with elan
#
# Writes $CACHE/bin/{nitrolean,gruszka,susz,nl-fast,leanchecker} and $CACHE/bin/versions.tsv.
# Needs git, curl, sha256sum, elan and a Rust toolchain (rustup); a checker that
# fails to build is reported and skipped, the others are still built.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/common.sh"

NITROLEAN=$(cd "$HERE/../.." && pwd)
UPDATE=0
while [[ $# -gt 0 ]]; do
  case $1 in
    --cache) CACHE=$2; shift ;;
    --nitrolean) NITROLEAN=$2; shift ;;
    --update-pins) UPDATE=1 ;;
    -h|--help) sed -n '2,16p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "build-checkers: unknown argument $1" >&2; exit 2 ;;
  esac
  shift
done
[[ $UPDATE == 1 ]] && export KC_UPDATE_PINS=1
need git curl sha256sum elan cargo
mkdir -p "$CACHE/bin"; CACHE=$(cd "$CACHE" && pwd)

GRUSZKA_COMMIT=43d2d1277e6dfa72572caa871c67ef15f78193e9
GRUSZKA_SHA256=23e8d6fda27cdf09d495bf9f20196feb9140b334c40bf321599a4634f8d38e3a
NANO_COMMIT=b5602a4ba169f6d4aef34fcdc3011fc41cd777e8
NANO_SHA256=fff9b5e9c34246b14f6e54bd781e213c4ced8b161fd73578d216cee1034f5f2c
SUSZ_VERSION=0.4.0

: >"$CACHE/bin/versions.tsv"
ver() { printf '%s\t%s\n' "$1" "$2" >>"$CACHE/bin/versions.tsv"; }

try() { # try NAME COMMAND...: run, report a failure instead of stopping
  # (not as an `if` condition, which would turn off `set -e` inside it)
  local name=$1 rc; shift
  set +e; ( set -e; "$@" ) >"$CACHE/build-$name.log" 2>&1; rc=$?; set -e
  if [[ $rc == 0 ]]; then log "$name: built"
  else log "$name: BUILD FAILED (log: $CACHE/build-$name.log)"; ver "$name" "build failed"; fi
}

build_nitrolean() {
  (cd "$NITROLEAN" && CARGO_TARGET_DIR=$CACHE/target/nitrolean cargo build --release --locked)
  cp "$CACHE/target/nitrolean/release/nitrolean" "$CACHE/bin/nitrolean"
  ver nitrolean "$(git -C "$NITROLEAN" rev-parse HEAD 2>/dev/null || echo unknown)"
}
build_gruszka() {
  fetch_git gruszka https://github.com/jasisz/gruszka "$GRUSZKA_COMMIT" "$GRUSZKA_SHA256"
  (cd "$CACHE/src/gruszka" && CARGO_TARGET_DIR=$CACHE/target/gruszka cargo build --release --locked)
  cp "$CACHE/target/gruszka/release/gruszka" "$CACHE/bin/gruszka"
  ver gruszka "$GRUSZKA_COMMIT"
  CARGO_TARGET_DIR=$CACHE/target/susz cargo install susz --version "$SUSZ_VERSION" --locked --root "$CACHE/susz"
  cp "$CACHE/susz/bin/susz" "$CACHE/bin/susz"
  ver susz "$SUSZ_VERSION"
}
build_nano() {
  fetch_git nano-lean https://github.com/sdiehl/nano-lean "$NANO_COMMIT" "$NANO_SHA256"
  (cd "$CACHE/src/nano-lean" && CARGO_TARGET_DIR=$CACHE/target/nano cargo build --release --locked --bin nl-fast)
  cp "$CACHE/target/nano/release/nl-fast" "$CACHE/bin/nl-fast"
  ver nano-lean "$NANO_COMMIT"
}
leanchecker_link() {
  local d; d=$(tc_bin "$TC_CHECK")
  ln -sf "$d/leanchecker" "$CACHE/bin/leanchecker"
  ver leanchecker "$("$d/lean" --version)"
}

try leanchecker leanchecker_link
try nitrolean build_nitrolean
try gruszka build_gruszka
try nano-lean build_nano
cat "$CACHE/bin/versions.tsv"
