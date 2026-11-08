#!/usr/bin/env bash
# Compile each tests/lean/*.lean with the official toolchain, export it with
# tools/Export.lean and check that ocaml4lean accepts it.
# usage: tests/lean_tests.sh   (LEAN_HOME defaults to /opt/lean/lean-4.35.0-linux)
set -u
ROOT=$(cd "$(dirname "$0")/.." && pwd)
LEAN_HOME=${LEAN_HOME:-/opt/lean/lean-4.35.0-linux}
export PATH=$LEAN_HOME/bin:$PATH
W=$(mktemp -d)
pass=0; fail=0
for f in "$ROOT"/tests/lean/*.lean; do
  m=$(basename "$f" .lean)
  cp "$f" "$W/"
  (cd "$W" && LEAN_PATH=$W:$LEAN_HOME/lib/lean lean -o "$m.olean" "$m.lean") || { echo "FAIL $m: compile"; fail=$((fail+1)); continue; }
  decls=$(grep -oE '^(inductive|structure) [A-Za-z0-9]+' "$f" | awk '{print $2}')
  (cd "$W" && LEAN_PATH=$W:$LEAN_HOME/lib/lean lean --run "$ROOT/tools/Export.lean" "$m" -- $decls > "$m.ndjson") || { echo "FAIL $m: export"; fail=$((fail+1)); continue; }
  if "${CHECKER:-$ROOT/ocaml4lean}" -q "$W/$m.ndjson" > "$W/$m.out" 2>&1; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL $m: $(tail -1 "$W/$m.out")"; fi
done
rm -rf "$W"
echo "passed $pass, failed $fail"; [ $fail = 0 ]
