#!/bin/bash
# Measures one checker run the way the Lean Kernel Arena does: instructions
# (all threads and children), wall time, user and system CPU time, and peak
# RSS (GNU time's %M).
#
#   measure.sh NAME OUT.tsv CMD
#
# CMD runs as `sh -c CMD`. COUNTER picks how instructions are counted:
#   perf        perf stat -e instructions, around the timed run (as the arena)
#   perf-u      perf stat -e instructions:u (user space only)
#   cachegrind  a second, untimed run under valgrind's cachegrind (Ir, all
#               threads and children); times and RSS come from the plain run.
#               Some 30 to 70 times slower than the plain run.
#   none        no count
# Appends one tab-separated row to OUT.tsv (header written if new):
# name, round ($ROUND, default 1), exit status, verdict, wall s, user s,
# sys s, CPU s, peak RSS MiB, billions of instructions, counter, last line
# of output.
set -uo pipefail
name=$1 out=$2 cmd=$3
counter=${COUNTER:-none}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

timed=(/usr/bin/time -f '%e %U %S %M' -o "$tmp/time" -- sh -c "$cmd")
case $counter in
  perf)   perf stat -x, -e instructions -o "$tmp/perf" -- "${timed[@]}" >"$tmp/log" 2>&1 ;;
  perf-u) perf stat -x, -e instructions:u -o "$tmp/perf" -- "${timed[@]}" >"$tmp/log" 2>&1 ;;
  *)      "${timed[@]}" >"$tmp/log" 2>&1 ;;
esac
status=$?
read -r wall user sys rss_kib < <(grep -E '^[0-9.]+ [0-9.]+ [0-9.]+ [0-9]+$' "$tmp/time" | tail -1)

ginstr=
case $counter in
  perf|perf-u)
    n=$(awk -F, '$3 ~ /^instructions/ && $1 ~ /^[0-9]+$/ {print $1}' "$tmp/perf")
    [ -n "$n" ] && ginstr=$(awk -v n="$n" 'BEGIN {printf "%.1f", n / 1e9}') ;;
  cachegrind)
    valgrind --tool=cachegrind --cache-sim=no --trace-children=yes \
      --cachegrind-out-file="$tmp/cg.%p" -- sh -c "$cmd" >"$tmp/cglog" 2>&1
    cgstatus=$?
    # One file per process; each has a "summary: Ir" line. No count unless
    # the run under valgrind ended as the plain one did (gruszka, for one,
    # reserves more address space than valgrind gives a program).
    if [ "$cgstatus" = "$status" ]; then
      ginstr=$(cat "$tmp"/cg.* | awk '/^summary:/ {s += $2} END {if (s) printf "%.1f", s / 1e9}')
    else
      echo "$name: status $status, under cachegrind $cgstatus: $(grep -v '^==' "$tmp/cglog" | tail -1)" >&2
    fi ;;
esac

case $status in
  0) verdict=accepted ;;
  1) verdict=rejected ;;
  2) verdict=declined ;;
  *) verdict=error ;;
esac
last=$(grep -v '^\s*$' "$tmp/log" | tail -1 | tr '\t' ' ' | cut -c1-200)
[ -s "$out" ] || printf 'run\tround\tstatus\tverdict\twall_s\tuser_s\tsys_s\tcpu_s\trss_mib\tginstructions\tcounter\tlast_line\n' >"$out"
cpu=$(awk -v u="$user" -v s="$sys" 'BEGIN {printf "%.2f", u + s}')
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$name" "${ROUND:-1}" "$status" "$verdict" \
  "$wall" "$user" "$sys" "$cpu" "$((rss_kib / 1024))" "${ginstr:--}" "$counter" "$last" >>"$out"
echo "$name (round ${ROUND:-1}): $verdict, wall ${wall}s, CPU ${cpu}s, RSS $((rss_kib / 1024)) MiB, ${ginstr:--} G instructions"
