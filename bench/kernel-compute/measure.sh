#!/usr/bin/env bash
# Time the checkers on exports and write the results as a TSV.
#
#   ./measure.sh [--timeout SECONDS] [--mem-mib MIB] [--checkers LIST] [--out FILE]
#                [--append] [--cache DIR] EXPORT.ndjson...
#
#   --timeout   wall-clock limit per run (default 60)
#   --mem-mib   resident-memory limit per run (default 4096); a run above it is killed
#   --checkers  comma list from leanchecker,gruszka,nano-lean,nitrolean (default: all)
#   --out       the TSV (default: out/measurements.tsv); --append adds to it, else it is replaced
#   --cache     where build-checkers.sh put the binaries (default: cache)
#
# Columns: export, export_bytes, checker, limit_s, verdict, exit, wall_s, peak_rss_mib.
# verdict is accepted, rejected, timeout (over the limit), oom (over the memory limit),
# error (anything else: the checker could not read the export, crashed, ...) or
# unavailable (the checker was not built). Run the checker's output is kept in
# out/logs/. gruszka reads a binary form of the export: `susz pack` makes it once,
# outside the measured time, into cache/susz/.
# The memory limit is a limit on the resident set, sampled every 50 ms (tools/run_limited.py).
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/common.sh"

TIMEOUT=60; MEM=4096; CHECKERS=leanchecker,gruszka,nano-lean,nitrolean; TSV=$OUT/measurements.tsv; APPEND=0
FILES=()
while [[ $# -gt 0 ]]; do
  case $1 in
    --timeout) TIMEOUT=$2; shift ;;
    --mem-mib) MEM=$2; shift ;;
    --checkers) CHECKERS=$2; shift ;;
    --out) TSV=$2; shift ;;
    --append) APPEND=1 ;;
    --cache) CACHE=$2; shift ;;
    -h|--help) sed -n '2,19p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    -*) echo "measure: unknown argument $1" >&2; exit 2 ;;
    *) FILES+=("$1") ;;
  esac
  shift
done
[[ ${#FILES[@]} -gt 0 ]] || die "no exports given"
need python3
BIN=$CACHE/bin
LOGS=$OUT/logs; mkdir -p "$LOGS" "$(dirname "$TSV")" "$CACHE/susz"
[[ $APPEND == 1 && -f $TSV ]] || printf 'export\texport_bytes\tchecker\tlimit_s\tverdict\texit\twall_s\tpeak_rss_mib\n' >"$TSV"
RUN=(python3 -I "$HERE/tools/run_limited.py")

# verdict CHECKER STATUS EXIT LOGFILE
verdict() {
  local checker=$1 status=$2 code=$3 log=$4
  case $status in timeout|oom) echo "$status"; return ;; esac
  case $checker in
    leanchecker) grep -q 'accepts the solution' "$log" && echo accepted || { [[ $code == 1 ]] && echo rejected || echo error; } ;;
    nitrolean)   grep -q '^accepted' "$log" && echo accepted || { grep -q '^rejected' "$log" && echo rejected || echo error; } ;;
    gruszka)     [[ $(tail -n1 "$log") == accepted ]] && echo accepted || { grep -q -i 'rejected\|failed' "$log" && echo rejected || echo error; } ;;
    nano-lean)   [[ $code == 0 ]] && grep -q ' 0 failures' "$log" && echo accepted || { [[ $code == 1 ]] && echo rejected || echo error; } ;;
  esac
}

for f in "${FILES[@]}"; do
  [[ -f $f ]] || die "$f: no such file"
  f=$(cd "$(dirname "$f")" && pwd)/$(basename "$f")
  name=$(basename "$f" .ndjson)
  bytes=$(stat -c %s "$f")
  for c in ${CHECKERS//,/ }; do
    bin=$BIN/$c; cmd=()
    case $c in
      leanchecker) cmd=("$bin" --from-export "$f") ;;
      nitrolean)   cmd=("$bin" check "$f") ;;
      nano-lean)   bin=$BIN/nl-fast; cmd=("$bin" "$f") ;;
      gruszka)
        bin=$BIN/gruszka
        if [[ -x $BIN/susz ]]; then
          susz=$CACHE/susz/$name.susz
          [[ -f $susz ]] || "$BIN/susz" pack --no-index "$f" "$susz" >"$LOGS/$name.susz-pack.log" 2>&1 || rm -f "$susz"
          cmd=("$bin" "$susz")
        fi ;;
      *) die "unknown checker $c" ;;
    esac
    if [[ ! -x $bin || ${#cmd[@]} -eq 0 || ( $c == gruszka && ! -f $CACHE/susz/$name.susz ) ]]; then
      printf '%s\t%s\t%s\t%s\tunavailable\t\t\t\n' "$name" "$bytes" "$c" "$TIMEOUT" >>"$TSV"
      continue
    fi
    log "$name: $c (limit ${TIMEOUT}s, ${MEM} MiB)"
    logf=$LOGS/$name.$c.t$TIMEOUT.log
    IFS=$'\t' read -r status code wall rss < <("${RUN[@]}" "$TIMEOUT" "$MEM" "$logf" -- "${cmd[@]}")
    v=$(verdict "$c" "$status" "$code" "$logf")
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$name" "$bytes" "$c" "$TIMEOUT" "$v" "$code" "$wall" "$rss" >>"$TSV"
  done
done
log "wrote $TSV"
