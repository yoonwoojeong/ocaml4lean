#!/usr/bin/env python3
"""Aggregate `perf script` call stacks (perf record --call-graph dwarf) by leaf
symbol and its nearest DEPTH callers, skipping GC/runtime trampolines, so one can
see *who* calls a hot runtime or library function.
usage: perf script -i FILE -F sym | bench/perfcallers.py [DEPTH] [MATCH]"""
import sys, collections
depth = int(sys.argv[1]) if len(sys.argv) > 1 else 2
match = sys.argv[2] if len(sys.argv) > 2 else None
skip = ("caml_call_gc", "caml_alloc", "caml_c_call", "caml_apply", "caml_do_pending", "caml_poll",
        "caml_major_collection", "major_collection", "mark", "caml_garbage", "caml_empty_minor",
        "caml_stw", "caml_try_run", "[unknown]", "caml_raise", "caml_curry", "caml_tuplify")
stacks, cur = collections.Counter(), []
def flush():
    if cur:
        leaf, rest = cur[0], []
        for f in cur[1:]:
            if f.startswith(skip) or f == leaf or (rest and rest[-1] == f):
                continue          # runtime trampolines and recursion
            rest.append(f)
        if match is None or match in leaf:
            stacks[(leaf,) + tuple(rest[:depth])] += 1
total = 0
for line in sys.stdin:
    s = line.strip()
    if not s:
        flush(); total += 1 if cur else 0; cur = []
    elif not s.endswith(":") and not s.startswith("o4l"):
        cur.append(s.split()[-1] if " " in s else s)
flush()
for k, v in stacks.most_common(40):
    print(f"{100*v/max(total,1):6.2f}%  " + "  <-  ".join(k))
