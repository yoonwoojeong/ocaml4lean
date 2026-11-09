#!/usr/bin/env bash
# Build ocaml4lean with nothing but the OCaml (>= 5.1) compiler distribution:
# no dune, no opam packages.  Produces ./ocaml4lean.
# (With dune installed, `dune build` builds the same sources.)
set -euo pipefail
cd "$(dirname "$0")"
OUT=_obuild
rm -rf "$OUT"; mkdir -p "$OUT"
FLAGS="-unsafe -inline 200"
if ocamlopt -config | grep -qE '^flambda2?: true'; then FLAGS="$FLAGS -O3"; fi
# library modules in dependency order, packed into a module Kernel
MODS="hc name level z expr vec env json fastline parse tc nbe nbh inductive check"
CMX=""
for m in $MODS; do
  cp "src/$m.ml" "$OUT/"
  ocamlopt $FLAGS -w -a -I "$OUT" -I +unix -for-pack Kernel -c "$OUT/$m.ml"
  CMX="$CMX $OUT/$m.cmx"
done
ocamlopt -pack -o "$OUT/kernel.cmx" $CMX
cp bin/main.ml "$OUT/main.ml"
ocamlopt $FLAGS -w -a -I "$OUT" -I +unix -c "$OUT/main.ml"
ocamlopt $FLAGS -I +unix unix.cmxa "$OUT/kernel.cmx" "$OUT/main.cmx" -o ocaml4lean
echo "built ./ocaml4lean"
