#!/usr/bin/env bash
# Build and run the level cross-check; exits non-zero on any mismatch.
set -euo pipefail
cd "$(dirname "$0")"
T=$(mktemp -d)
cp ../rbig.ml ../rterm.ml test_levels.ml "$T/"
(cd "$T" && ocamlopt -w -a rbig.ml rterm.ml test_levels.ml -o t && out=$(./t) && echo "$out" && ! echo "$out" | grep -q MISMATCH && echo "$out" | grep -q " 0 mismatches")
