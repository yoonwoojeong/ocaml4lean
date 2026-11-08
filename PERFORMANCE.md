# Performance and validation

All numbers: 4-vCPU cloud VM (x86-64), 15 GB RAM, Lean v4.35.0, OCaml 5.2.1+flambda,
one run each (re-runs during development varied by about ±5%). Raw data is in
`bench/results/`; `bench/run.sh` and `bench/arena.py` reproduce it.

## Workloads

The same declarations go to both checkers. `tools/Export.lean` writes the module and
all its dependencies as NDJSON; `tools/Replay.lean` sends the very same constants to
Lean's C++ kernel (`Kernel.Environment.replay`, which is how the lean-kernel-arena
runs the official kernel). The official time is the kernel's own replay time, so
loading `.olean` files is not counted. For ocaml4lean, parsing is shown separately.

| workload | constants | NDJSON size |
|---|---:|---:|
| `Init` | 65 893 | 360 MB |
| `Std` (includes `Init`) | 112 719 | 587 MB |

## Results: Init and Std

| workload | checker | domains | check time | + parse | peak RSS |
|---|---|---:|---:|---:|---:|
| Init | official kernel | 1 | **55.4 s** | – | 2.0 GB |
| Init | ocaml4lean | 1 | 65.3 s | 10.0 s | 2.1 GB |
| Init | ocaml4lean | 2 | 35.0 s | 9.7 s | 2.1 GB |
| Init | ocaml4lean | 4 | **19.1 s** | 9.7 s | 2.2 GB |
| Std | official kernel | 1 | **93.1 s** | – | 2.4 GB |
| Std | ocaml4lean | 1 | 128.7 s | 16.2 s | 3.7 GB |
| Std | ocaml4lean | 2 | 72.2 s | 16.9 s | 3.8 GB |
| Std | ocaml4lean | 4 | **42.6 s** | 16.9 s | 3.8 GB |

* On one core, checking takes 1.18× (Init) to 1.38× (Std) as long as the official kernel.
* It scales well: from 1 to 4 domains it is 3.4× faster on Init and 3.0× on Std. With
  4 domains it checks Init in 0.35× and Std in 0.46× of the official kernel's time
  (including parsing: 0.52× and 0.64×).
* Allocation (Init, 1 domain): 70 GB in the minor heap, 5.4 GB promoted, 25 major
  collections. Most of the peak RSS is the hash-consed environment (6.3 M nodes).

## Results: lean-kernel-arena perf cases (1 domain, check time)

Selected cases from `bench/results/arena-perf.txt` (31 cases; all verdicts correct):

| case | ocaml4lean | official | ratio |
|---|---:|---:|---:|
| grind-ring-5 | 2.04 s | 2.08 s | 0.98 |
| magma-string-n4 | 3.01 s | 2.96 s | 1.02 |
| magma-string-pair-n9 | 12.3 s | 9.8 s | 1.26 |
| magma-list-pair-n21 | 45.6 s | 33.9 s | 1.34 |
| magma-list-deep-n36 | 83.5 s | 61.8 s | 1.35 |
| let-ladder | 1.14 s | 0.79 s | 1.43 |
| beta-ladder (Θ(n²) substitution) | 2.09 s | 1.43 s | 1.46 |
| app-lam (DAG + Θ(n²) substitution) | 10.8 s | 5.6 s | 1.92 |

The remaining cases take under 0.15 s on both checkers.

## Comparison with nanoda, con-leche and con-ron

Not measured. Building them (Rust/Lean projects from GitHub) was blocked by the
permission policy of the environment this was written in, as was building
`lean4export`. `bench/run.sh` takes any checker command line, so they can be added
where they can be built. For orientation only (other hardware, other Lean version):
the arena's published numbers report nanoda and con-ron as faster than the official
kernel on Mathlib when running with 4 threads.

## Validation

* `Init` and `Std` are accepted in full: every theorem, definition and inductive
  block, with all recursors re-derived and identical to the exported ones.
* The lean-kernel-arena cases (`bench/results/arena-correctness.txt`, 94 cases:
  31 perf, 24 bugs, 29 corner cases, 10 other):
  * all 35 expected accepts are accepted and all 31 expected rejects (forged
    recursors, orphan constructors, universe bugs, loose bound variables, forged
    quotients, …) are rejected;
  * on the 28 "either" corner cases, ocaml4lean gives the same verdict as the official
    kernel on all 22 where the official kernel gives one, and, like it, does not
    terminate on `eta-struct-major-no-whnf` and `eta-struct-major-and-no-whnf` (cases
    documented as non-terminating for the official kernel; stopped by the time limit);
    the other 4 are hand-written files the official replay cannot read.
  * In total the official kernel could be run on 68 of the cases; the verdicts agree
    on all of them.
  * The arena's `tutorial` group was not run: it needs `lean4export` as a library.

## What made it fast (and what did not)

Times are Init check times on one domain unless noted; each step was measured.

| change | effect |
|---|---|
| first working version (hash-cons everything, generic `Hashtbl`) | 243 s |
| constant table keyed by names with their own hash (no polymorphic hashing) + "global" bit (skip global lookup when a child is not global) | 243 → 117 s |
| open-addressing hash-cons tables with inline hashes | 117 → 91 s |
| allocation-free scanner for name/level/expression lines; array index tables | parse 19 → 10 s |
| **stop interning terms built during checking** (structural equality instead) | 91 → 74 s; magma-n7 8.4 → 3.9 s, beta-ladder 13.4 → 3.5 s |
| open-addressing caches (infer/whnf) and pair set for def-eq caches | beta 3.7 → 1.9, magma 3.8 → 3.4 s |
| traversal memo: short-lived table, migrating to a reusable flat table for big terms | app-lam 15.3 → 10.4 s, Init unchanged |
| flambda (`-O3`) | 72 → 64 s |

Tried and reverted, because measurement showed no gain or a loss:
* a lossy direct-mapped memo for substitution (DAG sharing lost on collisions: slower);
* always using a reusable memo for substitution (write barriers on small traversals:
  Init 74 → 81 s), and gating memoisation by term size (lost sharing: Init slower);
* keeping the scratch hash-cons table at its grown size (worse cache locality);
* GC tuning (`space_overhead`, larger minor heap): within noise or slower.

### Where the remaining gap is

Against the C++ kernel on one core, the gap is allocation and GC rather than the
algorithm, which is the same: about 20–30% of the check time is minor/major GC work.
Terms kept in the per-declaration caches survive minor collections and are promoted,
and the very large environment heap makes each major cycle expensive. The adversarial
substitution tests (`app-lam`, `beta-ladder`) suffer most because every substituted
node is allocated, cached and promoted. Ideas that would attack this, not done here:
substitution in an environment (closures) instead of eager instantiation, and keeping
per-declaration terms in an arena that is dropped without being traced.

Parallel checking scales to about 3–3.4× on 4 domains. It is limited by OCaml 5's
stop-the-world minor collections (all domains synchronise), so it improves together
with any reduction in allocation.
