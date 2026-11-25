#!/usr/bin/env bash
# Checks that the repository holds nothing that shouldn't be public.
#
#   scripts/public-check.sh [RANGE]     check the tree and the messages of the
#                                       commits in RANGE (default origin/main..HEAD)
#   scripts/public-check.sh --tree-only check the tree only
#
# The tree is every tracked file plus every untracked file that isn't ignored,
# so that it can run before a commit. Exits nonzero after reporting every
# violation. Binary files and files over 1 MB are refused unless their path
# (or a glob matching it) is listed in scripts/public-check.allow.
set -uo pipefail
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$ROOT" || exit 2

range=origin/main..HEAD
check_commits=1
case ${1-} in
  --tree-only) check_commits=0 ;;
  -h | --help) sed -n '2,11p' "${BASH_SOURCE[0]}"; exit 0 ;;
  ?*) range=$1 ;;
esac

errors=0
violation() { echo "public-check: $*" >&2; errors=$((errors + 1)); }

paths='/(home|Users)/[A-Za-z0-9_]'
ipv4='\b([0-9]{1,3}\.){3}[0-9]{1,3}\b'
coauthor='^[[:space:]]*co-authored-by:'
bot_trailer='Co-Authored-By: 6[bot] <129682364+6[bot]@users.noreply.github.com>'

# Prints matches of an extended regex in the tree as path:line:text.
tree_grep() { git grep --untracked -nIE "$@" -- . 2>/dev/null; }

# 1. README.md is exactly one line, ending in a newline.
readme_line='`nitrolean` - work in progress'
if [[ ! -f README.md ]]; then
  violation "README.md is missing"
elif [[ $(cat README.md) != "$readme_line" || $(wc -l <README.md) != 1 ]]; then
  violation "README.md must be exactly the one line '$readme_line'"
fi

# 2. Home directory paths.
while IFS= read -r m; do violation "home directory path: $m"; done < <(tree_grep "$paths")

# IPv4 addresses outside the documentation ranges of RFC 5737.
while IFS= read -r m; do
  ip=${m##*:}
  IFS=. read -r a b c d <<<"$ip"
  ((10#$a <= 255 && 10#$b <= 255 && 10#$c <= 255 && 10#$d <= 255)) || continue
  case $a.$b.$c in 192.0.2 | 198.51.100 | 203.0.113) continue ;; esac
  violation "IPv4 address: ${m%:*}: $ip"
done < <(git grep --untracked -nIoE "$ipv4" -- . 2>/dev/null)

# 3. Build artifacts, binaries and large files.
allow=()
if [[ -f scripts/public-check.allow ]]; then
  while IFS= read -r line; do
    line=${line%%#*}
    line=${line%"${line##*[![:space:]]}"}
    [[ -n $line ]] && allow+=("$line")
  done <scripts/public-check.allow
fi
allowed() {
  local p
  for p in "${allow[@]}"; do
    # shellcheck disable=SC2053 # the allowlist holds globs
    [[ $1 == $p ]] && return 0
  done
  return 1
}

declare -A text=()
while IFS= read -r -d '' f; do text[$f]=1; done < <(git grep --untracked -IlzE '' -- . 2>/dev/null)

while IFS= read -r -d '' f; do
  [[ -f $f && ! -L $f ]] || continue
  case /$f in
    */.lake/* | */target/*) violation "build directory: $f"; continue ;;
  esac
  case $f in
    *.olean | *.ilean | *.ir | *.o | *.so | *.dylib | *.a) violation "build artifact: $f"; continue ;;
  esac
  size=$(stat -c %s -- "$f")
  if ((size > 0)) && [[ -z ${text[$f]-} ]] && ! allowed "$f"; then
    violation "binary file: $f (list it in scripts/public-check.allow if it belongs here)"
  fi
  if ((size > 1048576)) && ! allowed "$f"; then
    violation "file over 1 MB: $f ($size bytes; list it in scripts/public-check.allow if it belongs here)"
  fi
done < <(git ls-files -z --cached --others --exclude-standard)

# 4. Commit messages.
if ((check_commits)); then
  if ! commits=$(git rev-list "$range" 2>/dev/null); then
    violation "cannot list the commits in '$range' (fetch the base, or pass --tree-only)"
  else
    for c in $commits; do
      msg=$(git log -1 --format=%B "$c")
      short=${c:0:12}
      while IFS= read -r m; do
        [[ $m == "$bot_trailer" ]] || violation "commit $short: co-author trailer: $m"
      done < <(grep -iE "$coauthor" <<<"$msg")
    done
  fi
fi

if ((errors)); then
  echo "public-check: $errors violation(s)" >&2
  exit 1
fi
if ((check_commits)); then
  echo "public-check: OK (tree and $(grep -c . <<<"$commits") commit(s) in $range)"
else
  echo "public-check: OK (tree)"
fi
