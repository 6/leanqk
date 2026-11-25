#!/usr/bin/env bash
# Matrix certificates of growing size, as exports.
#
#   ./make-exports.sh [--out DIR] [--cache DIR] [--only LABEL,...] [--update-pins]
#
# For each row of data/certificates.tsv: make the certificate with gen.py (synthetic,
# seeded; its SHA-256 is pinned in the table), state it as a theorem with `mat_cert`
# (MatCert/Cmd.lean: `MatCert.InvertibleMod p n A` or `MatCert.Nonsingular n A`, proved
# by running the checker `MatCert.check` in the kernel), and export the theorem's closure
# with the lean4export that matches the toolchain (Lean v4.34.0).
#
# A label ending in -corrupt is the same certificate with one entry of B changed, so
# that its theorem is false: a checker has to reject that export.
#
# Certificates with n <= 16 are added with Lean's kernel check on, so Lean's kernel has
# accepted what those exports contain. The larger ones are added with
# `debug.skipKernelTC true` (Lean's kernel needs about 30 s and 8 GB for n = 64 already);
# checking them is what the exports are for.
#
# Writes OUT/certificates/LABEL.ndjson and OUT/certificates/manifest.tsv (label, kind, n,
# certificate bytes, export bytes, certificate SHA-256). OUT and CACHE default to
# ../kernel-compute/out and ../kernel-compute/cache, as for the other benchmarks.
# Needs git, sha256sum, elan, python3.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/../kernel-compute/common.sh"
CERTS=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
ONLY=""
while [[ $# -gt 0 ]]; do
  case $1 in
    --out) OUT=$2; shift ;;
    --cache) CACHE=$2; shift ;;
    --only) ONLY=$2; shift ;;
    --update-pins) export KC_UPDATE_PINS=1 ;;
    -h|--help) sed -n '2,23p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "make-exports: unknown argument $1" >&2; exit 2 ;;
  esac
  shift
done
need git sha256sum elan python3
mkdir -p "$OUT/certificates" "$CACHE"; OUT=$(cd "$OUT" && pwd); CACHE=$(cd "$CACHE" && pwd)
export LC_ALL=C

log "MatCert on $TC_MAIN"
tcdir=$(tc_bin "$TC_MAIN")
[[ $(cat "$CERTS/lean-toolchain") == "$TC_MAIN" ]] || die "lean-toolchain is not $TC_MAIN"
PROJ=$CACHE/matcert
rm -rf "$PROJ"; mkdir -p "$PROJ"
cp -r "$CERTS"/{lakefile.toml,lean-toolchain,MatCert.lean,MatCert} "$PROJ"/
(cd "$PROJ" && PATH=$tcdir:$PATH lake build) >"$CACHE/matcert-build.log" 2>&1 ||
  { tail -30 "$CACHE/matcert-build.log" >&2; die "building MatCert failed"; }
EXPORTER=$(build_exporter 434 "$LEAN4EXPORT_434" "$TC_MAIN")
LEANPATH=$(cd "$PROJ" && PATH=$tcdir:$PATH lake env printenv LEAN_PATH)
WORK=$CACHE/certificates-work; mkdir -p "$WORK"
ROWS=$OUT/certificates/.rows; mkdir -p "$ROWS"

tail -n +2 "$CERTS/data/certificates.tsv" | while IFS=$'\t' read -r label kind n param seed sha; do
  [[ -z $ONLY || ,$ONLY, == *,$label,* ]] || continue
  d=$WORK/$label; rm -rf "$d"; mkdir -p "$d"
  log "$label: $kind n=$n"
  flag=(); [[ $label == *-corrupt ]] && flag=(--corrupt)
  case $kind in
    inverse) python3 -I "$CERTS/gen.py" inverse "$param" "$n" "$seed" "$d/cert.txt" "${flag[@]}" ;;
    nonsingular) python3 -I "$CERTS/gen.py" nonsingular "$n" "$param" "$seed" "$d/cert.txt" "${flag[@]}" ;;
    *) die "$label: unknown kind $kind" ;;
  esac
  got=$(sha256sum "$d/cert.txt" | cut -c1-64)
  [[ $got == "$sha" || ${KC_UPDATE_PINS:-0} == 1 ]] || die "$label: certificate SHA-256 is $got, expected $sha"
  [[ $got == "$sha" ]] || log "$label: certificate SHA-256 is $got (pinned: $sha)"
  mod=Bench_${label//-/_}; thm=bench_${label//-/_}
  { echo "import MatCert"
    [[ $n -le 16 && $label != *-corrupt ]] || echo "set_option debug.skipKernelTC true"
    echo "mat_cert $thm \"$d/cert.txt\""; } >"$d/$mod.lean"
  (ulimit -s unlimited
   cd "$PROJ" && PATH=$tcdir:$PATH lake env lean -R "$d" -o "$d/$mod.olean" "$d/$mod.lean")
  (ulimit -s unlimited
   cd "$PROJ" && LEAN_PATH=$d:$LEANPATH PATH=$tcdir:$PATH "$EXPORTER" "$mod" -- "$thm") \
     >"$OUT/certificates/$label.ndjson"
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$label" "$kind" "$n" "$(stat -c %s "$d/cert.txt")" \
    "$(stat -c %s "$OUT/certificates/$label.ndjson")" "$got" >"$ROWS/$label"
done
{ printf 'label\tkind\tn\tcert_bytes\texport_bytes\tcert_sha256\n'
  cat "$ROWS"/* | sort -t "$(printf '\t')" -k2,2 -k3,3n; } >"$OUT/certificates/manifest.tsv"
log "wrote $OUT/certificates"
