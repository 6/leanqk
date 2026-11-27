#!/bin/bash
# Where the cycles go, for nitrolean and gruszka alike: hardware counters
# per run, then per-symbol profiles on cycles and instructions.
#
#   profile.sh OUT.md RAW_DIR
#
# Environment: IN (the export), W (the work directory, holding in.susz and
# gruszka/), NL (the nitrolean binary). Needs perf with hardware counters.
#
# 1. perf stat, once per command (nitrolean -j1 and -j4; gruszka with its
#    packer at 1 and 4 workers; gruszka alone at 1 worker), with every event of the list below this machine's perf can
#    count (each one tried first on a small command). Counters beyond the
#    PMU's are multiplexed and scaled; perf prints the share of time each
#    was counted. Beside each run, the most memory in transparent huge
#    pages (AnonHugePages, summed over the checker's processes), sampled
#    every 2 seconds.
# 2. perf record -e cycles:u -e instructions:u, one sample every 1000003
#    events, for nitrolean -j1 and gruszka alone at 1 worker; by symbol,
#    with each symbol's cycles, instructions and their ratio (IPC), and by
#    shared object.
#
# OUT.md gets the tables; RAW_DIR the perf stat output and the reports.
set -uo pipefail
out=${1:?usage: profile.sh OUT.md RAW_DIR} raw=${2:?usage: profile.sh OUT.md RAW_DIR}
mkdir -p "$raw"
gdir=$W/gruszka
period=1000003

# Generic events, then Intel ones (perf's names for this CPU's events, where
# it knows them), then the top-down group. Kept if they count on `true`.
candidates=(
  cycles:u instructions:u cycles:k instructions:k branches:u branch-misses:u
  L1-dcache-loads:u L1-dcache-load-misses:u LLC-loads:u LLC-load-misses:u
  cache-references:u cache-misses:u dTLB-loads:u dTLB-load-misses:u
  iTLB-load-misses:u
  l2_rqsts.references:u l2_rqsts.miss:u mem_load_retired.l1_miss:u
  mem_load_retired.l2_miss:u mem_load_retired.l3_miss:u
  dtlb_load_misses.walk_completed:u dtlb_load_misses.walk_active:u
  dtlb_load_misses.stlb_hit:u cycle_activity.stalls_total:u
  cycle_activity.stalls_l1d_miss:u cycle_activity.stalls_l2_miss:u
  cycle_activity.stalls_l3_miss:u exe_activity.bound_on_loads:u
  machine_clears.count:u int_misc.recovery_cycles:u
  '{slots,topdown-retiring,topdown-bad-spec,topdown-fe-bound,topdown-be-bound}'
  page-faults task-clock context-switches cpu-migrations
)
evs=()
for e in "${candidates[@]}"; do
  if perf stat -x, -e "$e" -o /tmp/profile-probe -- true >/dev/null 2>&1 &&
    ! grep -qE '<not (supported|counted)>' /tmp/profile-probe; then
    evs+=("$e")
  fi
done
events=$(IFS=,; echo "${evs[*]}")

# The most AnonHugePages (KiB) of the processes named $1, until $2 exits.
thp_watch() {
  local name=$1 pid=$2 max=0 n
  while kill -0 "$pid" 2>/dev/null; do
    n=$(for p in $(pgrep -x "$name"); do
          awk '/^AnonHugePages:/ {print $2}' "/proc/$p/smaps_rollup" 2>/dev/null
        done | awk '{s += $1} END {print s + 0}')
    [ "$n" -gt "$max" ] && max=$n
    sleep 2
  done
  echo "$max"
}

# count_run NAME PROCESS DIR CMD: one run under perf stat, from DIR.
count_run() {
  local name=$1 proc=$2 dir=$3 cmd=$4 f
  f=$raw/stat-$(echo "$name" | tr -c 'a-z0-9\n' '-').csv
  cat "$IN" "$W/in.susz" > /dev/null
  (cd "$dir" && TMPDIR=$W exec perf stat -x, -e "$events" -o "$f" -- sh -c "$cmd" > /dev/null 2>&1) &
  local pid=$!
  local thp; thp=$(thp_watch "$proc" "$pid")
  wait "$pid"; local status=$?
  echo "$name	$status	$thp	$f" >> "$raw/stat-index.tsv"
}

: > "$raw/stat-index.tsv"
count_run "nitrolean -j1" nitrolean "$W" "'$NL' check -j 1 '$IN'"
count_run "gruszka (susz pack + 1 worker)" gruszka "$gdir" "scripts/arena-run '$IN' 1"
count_run "gruszka alone (1 worker)" gruszka "$gdir" "'$gdir/target/release/gruszka' '$W/in.susz' 1"
count_run "nitrolean -j4" nitrolean "$W" "'$NL' check -j 4 '$IN'"
count_run "gruszka (susz pack + 4 workers)" gruszka "$gdir" "scripts/arena-run '$IN' 4"

# record NAME DIR CMD: per-symbol cycles and instructions.
record() {
  local name=$1 dir=$2 cmd=$3 tag d
  tag=$(echo "$name" | tr -c 'a-z0-9\n' '-')
  d=$W/perf-$tag.data
  cat "$IN" "$W/in.susz" > /dev/null
  if ! (cd "$dir" && perf record -q -e cycles:u -e instructions:u -c "$period" -o "$d" -- sh -c "$cmd" > /dev/null 2>&1); then
    echo "$name: perf record failed" >> "$raw/record-notes.txt"
    return
  fi
  # To files first: a pipe cut short would fail the step (pipefail).
  perf report -i "$d" --stdio --no-children -n --sort symbol 2>/dev/null > "$raw/report-$tag.txt"
  perf report -i "$d" --stdio --no-children -n --sort dso 2>/dev/null > "$raw/report-dso-$tag.txt"
  rm -f "$d"
}
record "nitrolean -j1" "$W" "'$NL' check -j 1 '$IN'"
record "gruszka alone (1 worker)" "$gdir" "'$gdir/target/release/gruszka' '$W/in.susz' 1"

# Each symbol's samples of both events (perf report gives one section per
# event, "# Samples: N of event 'E'", then lines "pct samples [.] symbol").
by_symbol() {
  awk -v period="$period" '
    /^# Samples: .* of event / { ev = ($0 ~ /instructions/) ? "i" : "c"; next }
    /^#/ || NF < 3 { next }
    { k = ($3 ~ /^\[.\]$/) ? 4 : 3; s = $k; for (j = k + 1; j <= NF; j++) s = s " " $j
      n[ev, s] += $2; tot[ev] += $2; if (ev == "c") syms[s] = 1 }
    END {
      for (s in syms) printf "%d\t%d\t%s\n", n["c", s], n["i", s], s
    }' "$1" | sort -t$'\t' -k1,1nr | head -"${2:-60}" | awk -F'\t' -v p="$period" '
      { c = $1 * p / 1e9; i = $2 * p / 1e9
        printf "| %s | %.2f | %.2f | %s |\n", $3, c, i, (c > 0 ? sprintf("%.2f", i / c) : "-") }'
}

{
  echo "### Hardware counters"
  echo
  echo "One run each under \`perf stat\`. Events this machine's perf counts: \`$events\`."
  echo "THP: \`$(cat /sys/kernel/mm/transparent_hugepage/enabled 2>/dev/null)\`, defrag \`$(cat /sys/kernel/mm/transparent_hugepage/defrag 2>/dev/null)\`."
  echo
  while IFS=$'\t' read -r name status thp f; do
    echo "#### $name (exit $status, at most $((thp / 1024)) MiB in huge pages)"
    echo
    echo "| event | count | counted % |"
    echo "|---|--:|--:|"
    awk -F, '$1 ~ /^[0-9.]+$/ { printf "| %s | %s | %s |\n", $3, $1, $5 }' "$f"
    awk -F, '$1 ~ /^[0-9.]+$/ { v[$3] = $1 }
      END {
        if (v["cycles:u"] > 0) {
          printf "\nIPC (user) %.3f", v["instructions:u"] / v["cycles:u"]
          if (v["instructions:u"] > 0) {
            if ("branch-misses:u" in v) printf "; branch misses per 1000 instructions %.2f", 1000 * v["branch-misses:u"] / v["instructions:u"]
            if ("LLC-load-misses:u" in v) printf "; LLC load misses per 1000 %.3f", 1000 * v["LLC-load-misses:u"] / v["instructions:u"]
            if ("l2_rqsts.miss:u" in v) printf "; L2 misses per 1000 %.2f", 1000 * v["l2_rqsts.miss:u"] / v["instructions:u"]
            if ("dTLB-load-misses:u" in v) printf "; dTLB load misses per 1000 %.3f", 1000 * v["dTLB-load-misses:u"] / v["instructions:u"]
          }
          if ("dtlb_load_misses.walk_active:u" in v) printf "; page-walk cycles %.1f%%", 100 * v["dtlb_load_misses.walk_active:u"] / v["cycles:u"]
          if ("cycle_activity.stalls_l3_miss:u" in v) printf "; L3-miss stall cycles %.1f%%", 100 * v["cycle_activity.stalls_l3_miss:u"] / v["cycles:u"]
          if ("cycle_activity.stalls_total:u" in v) printf "; all stall cycles %.1f%%", 100 * v["cycle_activity.stalls_total:u"] / v["cycles:u"]
          if (v["cycles:k"] > 0) printf "; kernel cycles %.1f%% of user", 100 * v["cycles:k"] / v["cycles:u"]
          print ""
        }
      }' "$f"
    echo
  done < "$raw/stat-index.tsv"
  for name in "nitrolean -j1" "gruszka alone (1 worker)"; do
    tag=$(echo "$name" | tr -c 'a-z0-9\n' '-')
    [ -s "$raw/report-$tag.txt" ] || continue
    echo "### $name by symbol (top 60 by user cycles)"
    echo
    echo "| symbol | G cycles | G instructions | IPC |"
    echo "|---|--:|--:|--:|"
    by_symbol "$raw/report-$tag.txt" 60
    echo
    echo "By shared object (samples of each event):"
    echo
    echo '```'
    awk '/^# Samples/ { print; n = 0; next } !/^#/ && NF >= 3 && n++ < 8' "$raw/report-dso-$tag.txt"
    echo '```'
    echo
  done
  [ -f "$raw/record-notes.txt" ] && cat "$raw/record-notes.txt"
} > "$out"
