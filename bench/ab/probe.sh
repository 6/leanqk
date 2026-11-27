#!/bin/bash
# Prepares a runner for bench/ab/run.sh and says what it is: installs perf
# and GNU time, lowers perf_event_paranoid, and tries `perf stat` with
# instructions:u and instructions on a small command. Writes shell
# assignments to the file named by $1 (CPU, ARCH, EVENTS: the events perf
# can count here, comma-separated, empty without counters; COUNTERS: yes or
# no-counters) and prints a one-line description.
set -uo pipefail
out=${1:?usage: probe.sh OUT}
{ sudo apt-get update -q && sudo apt-get install -yq time \
    linux-tools-common "linux-tools-$(uname -r)"; } >/tmp/ab-probe-apt.log 2>&1 \
  || { sudo apt-get install -yq time linux-tools-generic >>/tmp/ab-probe-apt.log 2>&1 || true; }
sudo sysctl -q kernel.perf_event_paranoid=-1 kernel.kptr_restrict=0 || true

cpu=$(lscpu | sed -n 's/^Model name: *//p' | head -1)
work=(sh -c 'i=0; while [ $i -lt 100000 ]; do i=$((i+1)); done')
events=
for ev in instructions:u instructions; do
  if perf stat -x, -e "$ev" -o /tmp/ab-probe-perf -- "${work[@]}" >/dev/null 2>&1 &&
     awk -F, -v e="$ev" '$3 == e && $1 ~ /^[0-9]+$/ {ok = 1} END {exit !ok}' /tmp/ab-probe-perf; then
    events=${events:+$events,}$ev
  fi
done
counters=yes
[[ $events == *instructions:u* ]] || counters=no-counters
{
  printf 'CPU=%q\n' "$cpu"
  printf 'ARCH=%q\n' "$(uname -m)"
  printf 'EVENTS=%q\n' "$events"
  printf 'COUNTERS=%q\n' "$counters"
  printf 'VCPUS=%q\n' "$(nproc)"
  printf 'HYPERVISOR=%q\n' "$(lscpu | sed -n 's/^Hypervisor vendor: *//p' | head -1)"
} >"$out"
echo "$(uname -m), $cpu, $(nproc) vCPUs, $(free -g | awk '/^Mem:/ {print $2}') GB RAM; perf events: ${events:-none} ($counters)"
