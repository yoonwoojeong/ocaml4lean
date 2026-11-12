#!/usr/bin/env bash
# Build the reference checker ./refcheck (OCaml >= 5.1, nothing else).
set -euo pipefail
cd "$(dirname "$0")"
OUT=_obuild
rm -rf "$OUT"; mkdir -p "$OUT"
for m in rbig rjson rterm rtc rdecl rmain; do cp "$m.ml" "$OUT/"; done
cd "$OUT"
for m in rbig rjson rterm rtc rdecl rmain; do
  ocamlopt -w -a -c "$m.ml"
done
ocamlopt -o ../refcheck rbig.cmx rjson.cmx rterm.cmx rtc.cmx rdecl.cmx rmain.cmx
echo "built ref/refcheck"
