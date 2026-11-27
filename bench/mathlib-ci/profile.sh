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
# 3. perf record on loads that missed L2, branch misses and completed page
#    walks (those this machine counts), one sample every 20011, for
#    nitrolean -j1 and -j4 and gruszka alone at 1 worker, by symbol.
# 4. The same loads and mispredicted branches sampled precisely, by source
#    line, for nitrolean -j1 and gruszka alone at 1 worker.
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
# For nitrolean, also each mapping's Rss and AnonHugePages (KiB) when its
# total Rss was highest, into $3 (address range, size, Rss, AnonHugePages,
# name; the 25 largest by Rss).
thp_watch() {
  local name=$1 pid=$2 maps=${3:-} max=0 top=0 n p r
  while kill -0 "$pid" 2>/dev/null; do
    n=$(for p in $(pgrep -x "$name"); do
          awk '/^AnonHugePages:/ {print $2}' "/proc/$p/smaps_rollup" 2>/dev/null
        done | awk '{s += $1} END {print s + 0}')
    [ "$n" -gt "$max" ] && max=$n
    if [ -n "$maps" ]; then
      for p in $(pgrep -x "$name"); do
        r=$(awk '/^Rss:/ {print $2}' "/proc/$p/smaps_rollup" 2>/dev/null)
        if [ -n "$r" ] && [ "$r" -gt "$top" ]; then
          top=$r
          awk -v total="$r" '
            /^[0-9a-f]+-[0-9a-f]+ / { if (range != "") print range "\t" size "\t" rss "\t" thp "\t" what
              range = $1; what = (NF >= 6) ? $6 : "[anon]"; size = rss = thp = 0; next }
            /^Size:/ { size = $2 } /^Rss:/ { rss = $2 } /^AnonHugePages:/ { thp = $2 }
            END { if (range != "") print range "\t" size "\t" rss "\t" thp "\t" what }' "/proc/$p/smaps" 2>/dev/null |
            sort -t$'\t' -k3,3nr | head -n 25 > "$maps.tmp" && mv "$maps.tmp" "$maps"
        fi
      done
    fi
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
  local maps=
  [ "$proc" = nitrolean ] && maps=${f%.csv}.maps.tsv
  local thp; thp=$(thp_watch "$proc" "$pid" "$maps")
  wait "$pid"; local status=$?
  echo "$name	$status	$thp	$f" >> "$raw/stat-index.tsv"
}

: > "$raw/stat-index.tsv"
count_run "nitrolean -j1" nitrolean "$W" "'$NL' check -j 1 '$IN'"
count_run "gruszka (susz pack + 1 worker)" gruszka "$gdir" "scripts/arena-run '$IN' 1"
count_run "gruszka alone (1 worker)" gruszka "$gdir" "'$gdir/target/release/gruszka' '$W/in.susz' 1"
count_run "nitrolean -j4" nitrolean "$W" "'$NL' check -j 4 '$IN'"
count_run "gruszka (susz pack + 4 workers)" gruszka "$gdir" "scripts/arena-run '$IN' 4"

# record NAME DIR EVENTS CMD: per-symbol samples of EVENTS (comma-separated),
# one sample every $period (or $3's own period) events.
record() {
  local name=$1 dir=$2 evlist=$3 per=$4 cmd=$5 tag d e args=()
  tag=$(echo "$name" | tr -c 'a-z0-9\n' '-')
  d=$W/perf-$tag.data
  for e in ${evlist//,/ }; do args+=(-e "$e"); done
  cat "$IN" "$W/in.susz" > /dev/null
  if ! (cd "$dir" && perf record -q "${args[@]}" -c "$per" -o "$d" -- sh -c "$cmd" > /dev/null 2>&1); then
    echo "$name: perf record failed" >> "$raw/record-notes.txt"
    return
  fi
  # To files first: a pipe cut short would fail the step (pipefail).
  perf report -i "$d" --stdio --no-children -n --sort symbol 2>/dev/null > "$raw/report-$tag.txt"
  perf report -i "$d" --stdio --no-children -n --sort dso 2>/dev/null > "$raw/report-dso-$tag.txt"
  rm -f "$d"
}
record "nitrolean -j1" "$W" cycles:u,instructions:u "$period" "'$NL' check -j 1 '$IN'"
record "gruszka alone (1 worker)" "$gdir" cycles:u,instructions:u "$period" "'$gdir/target/release/gruszka' '$W/in.susz' 1"

# Where the misses are: loads that missed L2, branch misses and completed
# page walks, by symbol, where this machine counts all three.
mperiod=20011
mevents=
for e in mem_load_retired.l2_miss:u branch-misses:u dtlb_load_misses.walk_completed:u; do
  case ",$events," in *",$e,"*) mevents=${mevents:+$mevents,}$e ;; esac
done
if [ -n "$mevents" ]; then
  record "misses nitrolean -j1" "$W" "$mevents" "$mperiod" "'$NL' check -j 1 '$IN'"
  record "misses nitrolean -j4" "$W" "$mevents" "$mperiod" "'$NL' check -j 4 '$IN'"
  record "misses gruszka alone (1 worker)" "$gdir" "$mevents" "$mperiod" "'$gdir/target/release/gruszka' '$W/in.susz' 1"
fi

# Loads that missed L2 and mispredicted branches at their own instructions
# (precise sampling, :pp), by source line: nitrolean is built with line
# tables when profiling (CARGO_PROFILE_RELEASE_DEBUG), gruszka's release
# profile has them. The data and the binaries go into RAW_DIR as well, for
# a closer look (perf annotate).
pevents=mem_load_retired.l2_miss:upp,br_misp_retired.all_branches:upp
by_line() {
  local name=$1 dir=$2 bin=$3 cmd=$4 tag d e args=()
  tag=$(echo "$name" | tr -c 'a-z0-9\n' '-')
  d=$raw/perf-$tag.data
  for e in ${pevents//,/ }; do args+=(-e "$e"); done
  cat "$IN" "$W/in.susz" > /dev/null
  if ! (cd "$dir" && perf record -q "${args[@]}" -c "$mperiod" -o "$d" -- sh -c "$cmd" > /dev/null 2>&1); then
    echo "$name: perf record of $pevents failed" >> "$raw/record-notes.txt"
    rm -f "$d"
    return
  fi
  timeout 2400 perf report -i "$d" --stdio --no-children -n --sort srcline 2>/dev/null > "$raw/report-$tag.txt" ||
    echo "$name: perf report by source line did not finish" >> "$raw/record-notes.txt"
  timeout 1200 perf report -i "$d" --stdio --no-children -n --sort symbol,srcline --percent-limit 0.05 2>/dev/null > "$raw/report-sym-$tag.txt" || true
  cp "$bin" "$raw/bin-$tag"
}
by_line "lines nitrolean -j1" "$W" "$NL" "'$NL' check -j 1 '$IN'"
by_line "lines gruszka alone (1 worker)" "$gdir" "$gdir/target/release/gruszka" "'$gdir/target/release/gruszka' '$W/in.susz' 1"

# The symbols of a report, by the samples of each of its events (perf
# report gives one section per event, "# Samples: N of event 'E'", then
# lines "pct samples [.] symbol"): a table of the top $2 by the first
# event, in billions of events (the sample period $3), with the ratio of
# the second to the first if $4 is set.
by_symbol() {
  local f=$1 top=$2 per=$3 ratio=${4:-} tmp
  tmp=$(mktemp)
  awk '
    /^# Samples: .* of event / { ev = $0; sub(/.* of event /, "", ev); gsub(/\047/, "", ev)
      if (!(ev in seen)) { seen[ev] = 1; order[++ne] = ev }; next }
    /^#/ || NF < 3 { next }
    { k = ($3 ~ /^\[.\]$/) ? 4 : 3; s = $k; for (j = k + 1; j <= NF; j++) s = s " " $j
      sub(/( +-)+$/, "", s)
      n[ev, s] += $2; if (ev == order[1]) syms[s] = 1 }
    END {
      for (s in syms) { line = ""; for (i = 1; i <= ne; i++) line = line n[order[i], s] "\t"; print line s }
    }' "$f" | sort -t$'\t' -k1,1nr > "$tmp"
  head -n "$top" "$tmp" | awk -F'\t' -v p="$per" -v r="$ratio" '
    { out = "| " $NF; for (i = 1; i < NF; i++) out = out sprintf(" | %.3f", $i * p / 1e9)
      if (r != "") out = out " | " ($1 > 0 ? sprintf("%.2f", $2 / $1) : "-")
      print out " |" }'
  rm -f "$tmp"
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
    if [ -s "${f%.csv}.maps.tsv" ]; then
      echo "Largest mappings at the highest Rss (MiB): range, size, Rss, AnonHugePages, name:"
      echo
      echo '```'
      awk -F'\t' '{ printf "%s %9.1f %8.1f %8.1f %s\n", $1, $2 / 1024, $3 / 1024, $4 / 1024, $5 }' "${f%.csv}.maps.tsv"
      echo '```'
      echo
    fi
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
    by_symbol "$raw/report-$tag.txt" 60 "$period" ipc
    echo
    echo "By shared object (samples of each event):"
    echo
    echo '```'
    awk '/^# Samples/ { print; n = 0; next } !/^#/ && NF >= 3 && n++ < 8' "$raw/report-dso-$tag.txt"
    echo '```'
    echo
  done
  for name in "misses nitrolean -j1" "misses nitrolean -j4" "misses gruszka alone (1 worker)"; do
    tag=$(echo "$name" | tr -c 'a-z0-9\n' '-')
    [ -s "$raw/report-$tag.txt" ] || continue
    echo "### $name by symbol (top 40 by the first event; billions of: $mevents)"
    echo
    echo "| symbol | ${mevents//,/ | } |"
    echo "|---|$(echo "$mevents" | sed 's/[^,]*/--:/g; s/,/|/g')|"
    by_symbol "$raw/report-$tag.txt" 40 "$mperiod"
    echo
  done
  for name in "lines nitrolean -j1" "lines gruszka alone (1 worker)"; do
    tag=$(echo "$name" | tr -c 'a-z0-9\n' '-')
    [ -s "$raw/report-$tag.txt" ] || continue
    echo "### $name by source line (top 50 by the first event; billions of: $pevents)"
    echo
    echo "| source line | ${pevents//,/ | } |"
    echo "|---|--:|--:|"
    by_symbol "$raw/report-$tag.txt" 50 "$mperiod"
    echo
  done
  if [ -f "$raw/record-notes.txt" ]; then cat "$raw/record-notes.txt"; fi
} > "$out"
