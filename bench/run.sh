#!/usr/bin/env bash
# Reproducible benchmark: export each workload once, then time
#   * the official Lean kernel (tools/Replay.lean, same declarations), and
#   * ocaml4lean with 1, 2 and 4 checking domains,
# recording wall time, peak RSS (GNU time) and GC statistics.
#
# usage: bench/run.sh [WORKDIR] [MODULE...]      (default modules: Init Std)
# env:   LEAN_HOME (default /opt/lean/lean-4.35.0-linux), REPS (default 1)
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
WORK=${1:-$ROOT/bench/work}; shift || true
MODS=${*:-Init Std}
LEAN_HOME=${LEAN_HOME:-/opt/lean/lean-4.35.0-linux}
REPS=${REPS:-1}
export PATH=$LEAN_HOME/bin:$PATH
mkdir -p "$WORK"
CHK=${CHECKER:-$ROOT/ocaml4lean}   # built by ./build.sh
OUT=$WORK/results.tsv
echo -e "workload\tchecker\tjobs\trep\twall_s\tmax_rss_kb\tdetail" > "$OUT"
for m in $MODS; do
  f=$WORK/$m.ndjson
  [ -s "$f" ] || lean --run "$ROOT/tools/Export.lean" "$m" > "$f"
  for r in $(seq "$REPS"); do
    /usr/bin/time -f "%e %M" -o "$WORK/t" lean --run "$ROOT/tools/Replay.lean" "$m" > "$WORK/o" 2>&1
    read -r w rss < "$WORK/t"
    echo -e "$m\tofficial\t1\t$r\t$w\t$rss\t$(tr '\n' ' ' < "$WORK/o")" | tee -a "$OUT"
    for j in 1 2 4; do
      /usr/bin/time -f "%e %M" -o "$WORK/t" "$CHK" -j "$j" --stats "$f" > "$WORK/o" 2>&1 || true
      read -r w rss < "$WORK/t"
      echo -e "$m\tocaml4lean\t$j\t$r\t$w\t$rss\t$(grep -E 'accepted|rejected|parse|gc:' "$WORK/o" | tr '\n' ' ')" | tee -a "$OUT"
    done
  done
done
