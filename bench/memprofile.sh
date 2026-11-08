#!/usr/bin/env bash
# Run a command, sampling its resident memory every 0.5 s from /proc (no cost to
# the measured process), and print phase markers the checker emits with
# O4L_MEMLOG=1.  Output: TSV "seconds  rss_MB" in $OUT (default memprofile.tsv),
# the command's stderr/stdout in $OUT.log, and a summary on stdout.
# usage: OUT=prefix bench/memprofile.sh CMD ARGS...
set -u
OUT=${OUT:-memprofile}
export O4L_MEMLOG=1
"$@" > "$OUT.log" 2>&1 &
pid=$!
t0=$(date +%s.%N)
: > "$OUT.tsv"
while kill -0 $pid 2>/dev/null; do
  rss=$(awk '/^VmRSS:/ {print int($2/1024)}' /proc/$pid/status 2>/dev/null)
  [ -n "$rss" ] && echo -e "$(echo "$(date +%s.%N) - $t0" | bc)\t$rss" >> "$OUT.tsv"
  sleep 0.5
done
wait $pid; code=$?
echo "exit=$code  peak_rss=$(sort -t$'\t' -k2 -n "$OUT.tsv" | tail -1 | cut -f2)MB  samples=$(wc -l < "$OUT.tsv")"
grep -E "^memlog|^accepted|^rejected|^error|internal error" "$OUT.log"
exit $code
