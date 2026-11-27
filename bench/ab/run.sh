#!/bin/bash
# Runs base (A) and candidate (B) of nitrolean in interleaved A/B/B/A or
# B/A/A/B quadruples on this machine and appends one row per run to OUT.tsv:
#
#   run.sh OUT.tsv
#
# From the environment:
#   A_BIN, B_BIN     the two binaries
#   A_FLAGS, B_FLAGS extra `nitrolean check` flags for each (may be empty)
#   SLICES           export names, space-separated; each is $EXPORTS/NAME.ndjson
#   THREADS          thread counts, space-separated (passed as -j)
#   REPS             quadruples per slice and thread count
#   ORDER            ABBA (the default) or BAAB: the order of each quadruple
#   META             the file bench/ab/probe.sh wrote (CPU, EVENTS, ...)
#   JOB              this job's index, for the rows
#
# Each run is `nitrolean check -j T FLAGS EXPORT` under GNU time (wall,
# user and system CPU time, peak RSS) and, where the machine has counters,
# under `perf stat -e EVENTS` (instructions:u and instructions: all threads,
# user space only and user plus kernel). The export is read through once
# before every run so that each starts with it in the page cache. A run's
# output is its exit status, standard output and standard error; the row
# holds its SHA-256, which must be the same for A and B.
set -uo pipefail
ORDER=${ORDER:-ABBA}
case $ORDER in
  ABBA) sides="A B B A" ;;
  BAAB) sides="B A A B" ;;
  *) echo "ORDER must be ABBA or BAAB, not $ORDER" >&2; exit 1 ;;
esac
out=${1:?usage: run.sh OUT.tsv}
# shellcheck disable=SC1090
. "$META"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

[ -s "$out" ] || printf 'job\tarch\tcpu\tcounters\tslice\tthreads\trep\tpos\tside\tstatus\twall_s\tuser_s\tsys_s\tcpu_s\trss_kib\tinstr_u\tinstr_all\tcounted_pct\tout_sha\torder\n' >"$out"

one() { # SIDE BIN FLAGS EXPORT THREADS -> one row
  local side=$1 bin=$2 flags=$3 in=$4 t=$5
  local cmd=("$bin" check -j "$t")
  # shellcheck disable=SC2206
  [ -n "$flags" ] && cmd+=($flags)
  cmd+=("$in")
  local timed=(/usr/bin/time -f '%e %U %S %M' -o "$tmp/time" -- "${cmd[@]}")
  rm -f "$tmp/time" "$tmp/perf"
  cat "$in" >/dev/null
  if [ -n "$EVENTS" ]; then
    perf stat -x, -e "$EVENTS" -o "$tmp/perf" -- "${timed[@]}" >"$tmp/stdout" 2>"$tmp/stderr"
  else
    "${timed[@]}" >"$tmp/stdout" 2>"$tmp/stderr"
  fi
  local status=$?
  # perf stat that cannot count exits before the command runs: time it
  # again without perf, with no counts.
  if ! grep -qE '^[0-9.]+ [0-9.]+ [0-9.]+ [0-9]+$' "$tmp/time" 2>/dev/null; then
    echo "perf stat did not run the command ($(head -c 200 "$tmp/stderr" | tr '\n' ' ')); timing it without perf" >&2
    rm -f "$tmp/perf"
    "${timed[@]}" >"$tmp/stdout" 2>"$tmp/stderr"
    status=$?
  fi
  # GNU time reports a command killed by a signal on stderr: keep it out of
  # the output's hash, which is the command's own.
  sed -i '/^Command \(exited with non-zero status\|terminated by signal\)/d' "$tmp/stderr"
  local wall user sys rss
  read -r wall user sys rss < <(grep -E '^[0-9.]+ [0-9.]+ [0-9.]+ [0-9]+$' "$tmp/time" | tail -1)
  local iu= ia= pct=
  if [ -s "$tmp/perf" ]; then
    iu=$(awk -F, '$3 == "instructions:u" && $1 ~ /^[0-9]+$/ {print $1}' "$tmp/perf")
    ia=$(awk -F, '$3 == "instructions" && $1 ~ /^[0-9]+$/ {print $1}' "$tmp/perf")
    # The share of the run each counter was counting (below 100 if perf
    # had to multiplex them).
    pct=$(awk -F, '$3 ~ /^instructions/ && $5 != "" {if (m == "" || $5 < m) m = $5} END {print m}' "$tmp/perf")
  fi
  local sha
  sha=$({ echo "status $status"; echo "-- stdout"; cat "$tmp/stdout"; echo "-- stderr"; cat "$tmp/stderr"; } | sha256sum | cut -c1-16)
  local cpu_s
  cpu_s=$(awk -v u="$user" -v s="$sys" 'BEGIN {printf "%.2f", u + s}')
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$JOB" "$ARCH" "$CPU" "$COUNTERS" "$slice" "$t" "$rep" "$pos" "$side" "$status" \
    "$wall" "$user" "$sys" "$cpu_s" "$rss" "$iu" "$ia" "$pct" "$sha" "$ORDER" >>"$out"
  echo "$slice -j$t rep $rep #$pos $side: status $status, wall ${wall}s, CPU ${cpu_s}s, RSS $((rss / 1024)) MiB, instructions:u ${iu:--}, output $sha$([ "$status" = 0 ] || echo " ($(tail -1 "$tmp/stderr" | cut -c1-200))")"
}

for slice in $SLICES; do
  in=$EXPORTS/$slice.ndjson
  [ -f "$in" ] || { echo "no export $in" >&2; exit 1; }
  for t in $THREADS; do
    for rep in $(seq "$REPS"); do
      pos=0
      for side in $sides; do
        pos=$((pos + 1))
        if [ "$side" = A ]; then one A "$A_BIN" "${A_FLAGS:-}" "$in" "$t"; else one B "$B_BIN" "${B_FLAGS:-}" "$in" "$t"; fi
      done
    done
  done
done
