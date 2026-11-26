#!/bin/bash
# Finds out how instructions can be counted on this machine: installs perf
# and valgrind, lowers perf_event_paranoid, and tries perf stat -e
# instructions, then instructions:u, then valgrind's cachegrind, on a small
# command. Prints a Markdown report on standard output and writes the first
# counter that gave a count (perf, perf-u, cachegrind or none) to the file
# named by $1.
set -uo pipefail
choice=${1:?usage: probe.sh CHOICE_FILE}
{ sudo apt-get update -q && sudo apt-get install -yq valgrind time \
    linux-tools-common "linux-tools-$(uname -r)"; } >/tmp/probe-apt.log 2>&1 \
  || { sudo apt-get install -yq linux-tools-generic >>/tmp/probe-apt.log 2>&1 || true; }
sudo sysctl -q kernel.perf_event_paranoid=-1 kernel.kptr_restrict=0 || true

work=(sh -c 'i=0; while [ $i -lt 100000 ]; do i=$((i+1)); done')
count() { # perf event -> its count, or what perf said instead
  perf stat -x, -e "$1" -o /tmp/probe-perf -- "${work[@]}" >/dev/null 2>/tmp/probe-perf-err \
    || { head -c 300 /tmp/probe-perf-err | tr '\n' ' '; return; }
  awk -F, -v e="$1" '$3 == e {print $1}' /tmp/probe-perf
}
echo "### Instruction counters on this runner"
echo
echo "- CPU: $(lscpu | sed -n 's/^Model name: *//p'), $(nproc) vCPUs, $(free -g | awk '/^Mem:/ {print $2}') GB RAM"
echo "- kernel: $(uname -r); hypervisor: $(lscpu | sed -n 's/^Hypervisor vendor: *//p')"
echo "- PMU in dmesg: \`$(sudo dmesg | grep -iE 'Performance Events|PMU' | head -3 | sed 's/^\[[^]]*\] //' | tr '\n' ';')\`"
echo "- perf: $(perf --version 2>&1 | head -1)"
echo
echo "| method | result |"
echo "|---|---|"
picked=none
for ev in instructions instructions:u cycles task-clock; do
  r=$(count "$ev")
  echo "| \`perf stat -e $ev\` | ${r:-(empty)} |"
  if [[ $r =~ ^[0-9]+$ ]] && [ "$picked" = none ]; then
    case $ev in instructions) picked=perf ;; instructions:u) picked=perf-u ;; esac
  fi
done
cg=$(valgrind --tool=cachegrind --cache-sim=no --cachegrind-out-file=/tmp/probe-cg -- "${work[@]}" 2>&1 \
  && awk '/^summary:/ {print $2}' /tmp/probe-cg)
cg=$(echo "$cg" | tail -1)
echo "| \`valgrind --tool=cachegrind\` (Ir) | ${cg:-failed} |"
if [ "$picked" = none ] && [[ $cg =~ ^[0-9]+$ ]]; then picked=cachegrind; fi
echo
echo "Counter used: **$picked**"
echo "$picked" >"$choice"
