#!/usr/bin/env bash
# Consistency checks of the correctness harness that need neither Lean nor the
# corpus: the scripts parse, the verdict tables agree with each other and with
# corpus/divergences.md, and the runner classifies results correctly.
set -euo pipefail
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$ROOT"
fail() { echo "selfcheck: $*" >&2; exit 1; }

# Nothing private in the public tree, and (when origin/main is known) in the
# messages of the commits on top of it.
if git rev-parse -q --verify origin/main >/dev/null; then
  scripts/public-check.sh || fail "public-check failed"
else
  scripts/public-check.sh --tree-only || fail "public-check failed"
fi

for f in scripts/*.sh; do bash -n "$f"; done
for f in scripts/*.py; do python3 -I -c 'import ast, sys; ast.parse(open(sys.argv[1]).read())' "$f"; done

# Every test has an export checksum, a Lean verdict and a leanqk verdict.
lean_tsv=corpus/expected-lean-v4.36.0.tsv
ids_sums=$(sed -E 's/^[0-9a-f]{64}  (.*)\.ndjson$/\1/' corpus/exports.sha256 | LC_ALL=C sort)
ids_lean=$(tail -n +2 "$lean_tsv" | cut -f1 | LC_ALL=C sort)
ids_leanqk=$(tail -n +2 corpus/expected-leanqk.tsv | cut -f1 | LC_ALL=C sort)
[[ $ids_sums == "$ids_lean" ]] || fail "$lean_tsv and corpus/exports.sha256 list different tests"
[[ $ids_lean == "$ids_leanqk" ]] || fail "the two expected-*.tsv list different tests"
[[ -z $(uniq -d <<<"$ids_lean") ]] || fail "duplicate test ids"
awk -F'\t' 'NR > 1 && (NF != 5 || $3 !~ /^(accept|reject|either)$/ || $4 !~ /^(accept|reject|timeout|error)$/) {
  print "selfcheck: bad row in '"$lean_tsv"': " $0; bad = 1 } END { exit bad }' "$lean_tsv"
python3 -I scripts/corpus.py expected-leanqk "$lean_tsv" corpus/divergences.md corpus/expected-leanqk.tsv --check

# Every source in the tables is described in corpus/SOURCES.md.
for s in $(tail -n +2 "$lean_tsv" | cut -f2 | sort -u); do
  grep -q "^## .*(\`$s\`)" corpus/SOURCES.md || fail "source $s is not described in corpus/SOURCES.md"
done

# The runner, on a fake checker.
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/c/t"
printf 'id\tsource\texpected\ttimeout\torigin\nt/slow\tt\taccept\t1\t-\n' >"$tmp/c/manifest.tsv"
printf 'test_id\tverdict\tbasis\n' >"$tmp/e.tsv"
for t in good:accept bad:reject wrong:accept todo:accept todo2:reject declined:accept boom:reject slow:accept malformed:reject; do
  echo "${t%%:*}" >"$tmp/c/t/${t%%:*}.ndjson"
  printf 't/%s\t%s\tx\n' "${t%%:*}" "${t#*:}" >>"$tmp/e.tsv"
done
printf 't/absent\taccept\tx\n' >>"$tmp/e.tsv"
cat >"$tmp/leanqk" <<'EOF'
#!/bin/sh
[ "$2" = --parse-only ] && { case $(cat "$3") in malformed|wrong) exit 1 ;; *) exit 0 ;; esac; }
case $(cat "$2") in
  good) exit 0 ;; bad) exit 1 ;; wrong) exit 1 ;;
  todo|todo2) echo "leanqk: check: not implemented yet" >&2; exit 1 ;;
  declined) echo "leanqk: declined" >&2; exit 2 ;;
  malformed) echo "leanqk: malformed input" >&2; exit 1 ;;
  boom) kill -SEGV $$ ;;
  slow) sleep 30 ;;
esac
EOF
chmod +x "$tmp/leanqk"
set +e
python3 -I scripts/run-corpus.py --leanqk "$tmp/leanqk" --corpus "$tmp/c" --expected "$tmp/e.tsv" \
  --results "$tmp/r.tsv" -j 4 >"$tmp/out" 2>&1
code=$?
set -e
got=$(tail -n +2 "$tmp/r.tsv" | cut -f1,3 | LC_ALL=C sort | tr '\t\n' ': ')
want="t/absent:missing t/bad:pass t/boom:crash t/declined:pending t/good:pass t/malformed:pass t/slow:timeout t/todo:pending t/todo2:pending t/wrong:fail "
[[ $got == "$want" && $code == 1 ]] || { cat "$tmp/out"; fail "runner self-test: got '$got' (exit $code)"; }
grep -q "10 tests: 3 pass, 3 pending, 1 fail, 1 crash, 1 timeout, 1 missing" "$tmp/out" ||
  { cat "$tmp/out"; fail "runner self-test: unexpected summary"; }
python3 -I scripts/run-corpus.py --leanqk "$tmp/leanqk" --corpus "$tmp/c" --expected "$tmp/e.tsv" \
  --filter 'good|bad|todo' >/dev/null || fail "runner self-test: pending must not fail the run"
if python3 -I scripts/run-corpus.py --leanqk "$tmp/leanqk" --corpus "$tmp/c" --expected "$tmp/e.tsv" \
  --filter todo --strict >/dev/null; then fail "runner self-test: --strict must fail on pending"; fi

python3 -I scripts/run-corpus.py --leanqk "$tmp/leanqk" --corpus "$tmp/c" --expected "$tmp/e.tsv" \
  --parse-only --filter 'good|bad|malformed|wrong' --results "$tmp/p.tsv" >/dev/null && fail "runner self-test: parse-only must fail on t/wrong"
got=$(tail -n +2 "$tmp/p.tsv" | cut -f1,3,4 | LC_ALL=C sort | tr '\t\n' ': ')
[[ $got == "t/bad:pass:parsed t/good:pass:parsed t/malformed:pass:malformed t/wrong:fail:malformed " ]] ||
  fail "runner self-test: parse-only got '$got'"

echo "selfcheck: OK ($(wc -l <<<"$ids_lean") tests)"
