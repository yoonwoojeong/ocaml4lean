#!/usr/bin/env bash
# Run ocaml4lean on the hand-written .ndjson cases of lean-kernel-arena and
# compare with the expected outcome.  usage: tests/arena_ndjson.sh ARENA_DIR
set -u
ROOT=$(cd "$(dirname "$0")/.." && pwd)
A=${1:?path to lean-kernel-arena}
pass=0; fail=0
for f in "$A"/tests/*/*.ndjson; do
  y=${f%.ndjson}.yaml; exp=$(grep -E '^outcome:' "$y" | awk '{print $2}')
  "$ROOT/_build/default/bin/main.exe" -q "$f" > /dev/null 2>&1; code=$?
  got=$([ $code = 0 ] && echo accept || echo reject)
  if [ "$exp" = either ] || [ "$exp" = "$got" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL $f: expected $exp, got $got"; fi
done
echo "passed $pass, failed $fail"; [ $fail = 0 ]
