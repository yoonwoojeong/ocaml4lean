#!/usr/bin/env bash
# Before/after benchmark for optimization work: check time (s), peak RSS (MB)
# and verdict on Init (1 and 4 domains), Std and the Lean package (4 domains),
# and four reduction-heavy arena perf cases (1 domain).
# usage: bench/quick.sh BINARY [WORKDIR]    (WORKDIR holds init/std/lean.ndjson and arena2/)
BIN=$1; W=${2:-/home/user/work}
run() { # label jobs file
  /usr/bin/time -f "%M" -o /tmp/quick_rss.$$ "$BIN" -j "$2" --stats "$3" > /tmp/quick_out.$$ 2>&1
  local code=$?
  local chk; chk=$(grep -oE "check [0-9.]+s" /tmp/quick_out.$$ | grep -oE "[0-9.]+")
  printf "%-26s check=%8ss  rss=%6sMB  exit=%s\n" "$1" "$chk" "$(( $(cat /tmp/quick_rss.$$) / 1024 ))" "$code"
}
run "init -j1" 1 "$W/init.ndjson"
run "init -j4" 4 "$W/init.ndjson"
run "std -j4" 4 "$W/std.ndjson"
run "lean -j4" 4 "$W/lean.ndjson"
for t in magma_list_pair_n7 grind_ring_5 app_lam beta_ladder; do run "perf/$t" 1 "$W/arena2/T_perf_$t.ndjson"; done
rm -f /tmp/quick_rss.$$ /tmp/quick_out.$$
