#!/bin/bash
# Summarises the rows measure.sh wrote: per run, the median of each measure
# over the rounds, then the ratios of the medians, nitrolean / nano-lean and
# nitrolean / gruszka, for the pairs that run the same number of threads,
# then every row.
#
#   report.sh RESULTS.tsv > summary.md
#
# Exits 1 if any run did not accept.
set -euo pipefail
tsv=$1
cols=(5 6 7 8 9 10)  # wall, user, sys, CPU, RSS, instructions

# The median of column $2 of run $1 ("-" if it has no numbers).
median() {
  awk -F'\t' -v r="$1" -v c="$2" 'NR > 1 && $1 == r && $c != "-" {print $c}' "$tsv" |
    sort -g | awk '{v[NR] = $1} END {
      if (NR == 0) print "-"
      else if (NR % 2) print v[(NR + 1) / 2]
      else printf "%.2f\n", (v[NR / 2] + v[NR / 2 + 1]) / 2 }'
}
ratio() { awk -v a="$1" -v b="$2" 'BEGIN {if (a == "-" || b == "-" || b + 0 == 0) print "-"; else printf "%.2f\n", a / b}'; }

mapfile -t runs < <(awk -F'\t' 'NR > 1 && !seen[$1]++ {print $1}' "$tsv")
echo "Medians over $(awk -F'\t' 'NR > 1 {print $2}' "$tsv" | sort -u | wc -l) rounds; in each round the runs alternate between the checkers."
echo
echo "| run | verdicts | G instructions | wall s | user s | sys s | CPU s | peak RSS MiB |"
echo "|---|---|--:|--:|--:|--:|--:|--:|"
declare -A med
for r in "${runs[@]}"; do
  for c in "${cols[@]}"; do med[$r,$c]=$(median "$r" "$c"); done
  v=$(awk -F'\t' -v r="$r" 'NR > 1 && $1 == r {n[$4]++} END {for (k in n) printf "%s%s ×%d", s, k, n[k]; s = ", "}' "$tsv")
  echo "| $r | $v | ${med[$r,10]} | ${med[$r,5]} | ${med[$r,6]} | ${med[$r,7]} | ${med[$r,8]} | ${med[$r,9]} |"
done
echo
echo "Ratios of the medians, nitrolean / the other checker (below 1: nitrolean used less):"
echo
echo "| nitrolean | other | instructions | wall | CPU | peak RSS |"
echo "|---|---|--:|--:|--:|--:|"
pairs=(
  "nitrolean -j1|nano-lean -j1"
  "nitrolean -j4|nano-lean -j4"
  "nitrolean -j1|gruszka (susz pack + 1 worker)"
  "nitrolean -j4|gruszka (susz pack + 4 workers)"
  "nitrolean -j4|gruszka alone (4 workers)"
)
for p in "${pairs[@]}"; do
  a=${p%%|*} b=${p#*|}
  [ -n "${med[$a,5]:-}" ] && [ -n "${med[$b,5]:-}" ] || continue
  echo "| $a | $b | $(ratio "${med[$a,10]}" "${med[$b,10]}") | $(ratio "${med[$a,5]}" "${med[$b,5]}") | $(ratio "${med[$a,8]}" "${med[$b,8]}") | $(ratio "${med[$a,9]}" "${med[$b,9]}") |"
done
echo
echo "<details><summary>All runs</summary>"
echo
echo "| run | round | verdict | G instructions | wall s | user s | sys s | CPU s | peak RSS MiB |"
echo "|---|--:|---|--:|--:|--:|--:|--:|--:|"
awk -F'\t' 'NR > 1 {printf "| %s | %s | %s | %s | %s | %s | %s | %s | %s |\n", $1, $2, $4, $10, $5, $6, $7, $8, $9}' "$tsv"
echo
echo "</details>"
awk -F'\t' 'NR > 1 && $4 != "accepted" {bad = 1; print "not accepted: " $1 ", round " $2 " (" $12 ")" > "/dev/stderr"} END {exit bad}' "$tsv"
