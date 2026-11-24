#!/usr/bin/env bash
# Tests scripts/public-check.sh: in a temporary git repository, a clean tree
# passes, and one planted violation of each kind is caught. The planted names
# are split with '' so that this file passes the check itself.
set -euo pipefail
SRC=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
repo=$tmp/repo
failures=0

g() { git -C "$repo" -c user.name=test -c user.email=test@example.com -c commit.gpgsign=false "$@"; }

git init -q "$repo"
mkdir "$repo/scripts"
cp "$SRC/public-check.sh" "$repo/scripts/"
printf '# test allowlist\nallowed.bin\nbig-allowed.txt  # trailing comment\n' >"$repo/scripts/public-check.allow"
echo "Lean quick kernel - work in progress" >"$repo/README.md"
echo "documentation address 192.0.2.17, version 4.36.0" >"$repo/notes.txt"
g add -A
g commit -qm "Initial commit"
g tag base

run() { (cd "$repo" && bash scripts/public-check.sh "$@") >"$tmp/out" 2>&1; }
reset() { g reset -q --hard base && g clean -qfdx; }

# expect_fail LABEL MESSAGE: the check fails and reports MESSAGE.
expect_fail() {
  if run base..HEAD; then
    echo "FAIL: $1: not caught"; failures=$((failures + 1))
  elif ! grep -qF -- "$2" "$tmp/out"; then
    echo "FAIL: $1: no '$2' in:"; sed 's/^/  /' "$tmp/out"; failures=$((failures + 1))
  else
    echo "ok: $1"
  fi
  reset
}
expect_pass() {
  if run base..HEAD; then echo "ok: $1"; else
    echo "FAIL: $1: flagged:"; sed 's/^/  /' "$tmp/out"; failures=$((failures + 1))
  fi
  reset
}
plant() { printf '%b\n' "$2" >"$repo/$1" && g add -f "$1"; }
commit() { g commit -q --allow-empty -m "$1"; }

expect_pass "clean tree"

printf 'Lean quick kernel - work in progress\nmore\n' >"$repo/README.md"
expect_fail "README with two lines" "README.md must be exactly"

plant a.txt "written by Cla""ude"
expect_fail "model name" "AI model or assistant name: a.txt:1"

plant a.txt "run it under agent""ctl"
expect_fail "tool name" "tool or platform name: a.txt:1"

plant a.txt "see /ho""me/alice/x"
expect_fail "home path" "home or scratch path: a.txt:1"

plant a.txt "see /Us""ers/alice/x"
expect_fail "macOS home path" "home or scratch path: a.txt:1"

plant a.txt "in scra""tch/1a2b3c4d"
expect_fail "scratch path" "home or scratch path: a.txt:1"

plant a.txt "server at 10.1.2"".3"
expect_fail "IPv4 address" "IPv4 address: a.txt:1: 10.1.2"".3"

plant a.txt "host box.example.ts"".net"
expect_fail "tailnet hostname" "private hostname: a.txt:1"

plant a.txt "host db.corp.inter""nal"
expect_fail "internal hostname" "private hostname: a.txt:1"

printf 'by Cla''ude\n' >"$repo/b.txt"
expect_fail "untracked file" "AI model or assistant name: b.txt:1"

commit "Fix it with Op""us"
expect_fail "model name in a commit message" "AI model or assistant name: Fix it with"

commit "Fix it

Generated ""with a tool"
expect_fail "assistance phrase in a commit message" "AI-assistance phrase"

commit "Fix it

Co-Authored""-By: Someone <someone@example.com>"
expect_fail "co-author trailer" "co-author trailer"

commit "Fix it (#9)

Co-Authored""-By: 6[bot] <129682364+6[bot]@users.noreply.github.com>"
expect_pass "squash trailer"

plant Foo.olean "x"
expect_fail ".olean file" "build artifact: Foo.olean"

plant lib.a "x"
expect_fail ".a file" "build artifact: lib.a"

mkdir -p "$repo/.lake/build" && plant .lake/build/x.txt "x"
expect_fail ".lake directory" "build directory: .lake/build/x.txt"

mkdir -p "$repo/target/debug" && plant target/debug/x.txt "x"
expect_fail "target directory" "build directory: target/debug/x.txt"

printf 'a\0b' >"$repo/blob.bin" && g add blob.bin
expect_fail "binary file" "binary file: blob.bin"

printf 'a\0b' >"$repo/allowed.bin" && g add allowed.bin
expect_pass "allowlisted binary file"

head -c 1048577 /dev/zero | tr '\0' a >"$repo/big.txt" && g add big.txt
expect_fail "file over 1 MB" "file over 1 MB: big.txt"

head -c 1048577 /dev/zero | tr '\0' a >"$repo/big-allowed.txt" && g add big-allowed.txt
expect_pass "allowlisted file over 1 MB"

if ((failures)); then echo "public-check-test: $failures failure(s)"; exit 1; fi
echo "public-check-test: OK"
