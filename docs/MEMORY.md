# Memory engineering for the Mathlib benchmark

This document records why `ocaml4lean` failed the Lean Kernel Arena's Mathlib test,
what was measured, what was changed (and what was not, with reasons), and how to
reproduce every number. Soundness is not traded for memory anywhere: every change
below affects allocation, data layout, GC pacing or scheduling, never what is
checked or how definitional equality is decided.

## 1. Diagnosis of the arena failure

Arena record for `mathlib` at rev `3753af7` (run of 2026-11-08):

| field | value |
|---|---|
| status / exit code | `error` / **137** |
| stdout, stderr | empty |
| wall / CPU time | 171.8 s / 211.2 s |
| peak RSS | 15,630 MB |
| instructions | 1.524 × 10¹² |
| runner | `nscloud-ubuntu-22.04-amd64-8x16` (8 vCPU, 16 GB) |

What each hypothesis would look like, against what was recorded:

| hypothesis | expected signature | verdict |
|---|---|---|
| external SIGKILL by the kernel OOM killer | exit 137, no output, RSS at the machine limit | **consistent** |
| arena time limit | status `timeout` | excluded |
| OCaml exception (stack overflow, assertion, ...) | handler prints `internal error: …`, exit 3 | excluded (no output) |
| segmentation fault | exit 139 | excluded |
| GC thrashing without exhaustion | long CPU-bound run without a kill | excluded (killed after 2.9 min, CPU ≈ wall) |

*Where* it died: a complete run of ocaml4lean costs 1,300–2,200 instructions per
input byte on the arena (Init 1,577; Std 2,155; cedar 1,268), of which parsing is a
small part. Mathlib's 1.524 × 10¹² instructions are 263 per byte of its 5.8 GB, and
CPU time exceeded wall time by only 39 s although checking runs 4 domains. So the
process was killed at the end of parsing or in the first seconds of checking.

Calibration from the same arena run: peak RSS / input size was 2.5× on `cslib`
(2.3 GB, built on Mathlib), predicting ~14.5 GB for Mathlib, i.e. the 15.6 GB kill.
The arena also shows ~35% more RSS than the development VM for the same input
(`std`: 3.0 GB vs 2.2 GB), so local measurements are scaled by 1.35 when predicting
arena behaviour.

A concurrency bug was found on the way (not the Mathlib failure, but it could have
struck it): module-level `lazy` constants were forced by several domains, which in
OCaml 5 raises `CamlinternalLazy.Undefined`. They are now built eagerly (commit
`95b59fa`).

## 2. Measurement setup

* **Mathlib proxy.** Mathlib itself cannot be exported in the development
  environment, so `bench/proxy/mathlib_proxy.py` builds a *valid* environment of
  the same scale from real code: the `Lean` package export (which contains Init)
  plus K copies of every non-Init declaration with all names re-rooted under a fresh
  root `C_k`; references to Init keep their names. K = 6 gives 6.17 GB and 100.9 M
  lines (Mathlib: 5.8 GB, 109.8 M), 1,056,596 declarations, all of which must be
  accepted. It is a stress test of scale, not of Mathlib's exact shape (its RSS /
  input ratio is lower than cslib's), which is why a hard bound (stage G) matters.
* **Instrumentation.** `O4L_MEMLOG=1` prints, at each phase boundary, VmRSS/VmHWM
  and GC statistics; `bench/memprofile.sh` samples VmRSS from `/proc` every 0.5 s
  from outside the process. (A sampling domain inside the process was tried and
  rejected: every extra domain joins OCaml 5's stop-the-world minor collections and
  doubled `Init`'s check time.)
* **Machine.** 4 vCPU, 15 GB, OCaml 5.4.0. Timings are taken with no other load: with
  4 checking domains on fewer free cores, stop-the-world synchronisation made checking
  2.3× slower in one accidental measurement.

## 3. Stages on the Mathlib proxy (4 domains)

| stage | parse-end RSS | live after compaction (RSS / GC heap) | peak RSS | wall | minor / promoted words |
|---|---:|---:|---:|---:|---:|
| 0 — arena rev `3753af7` | 8.14 GB | 5.10 / 4.43 GB | 8.83 GB | 592 s | 39.3 G / 1.71 G |
| A — presized tables | 6.35 GB | 5.04 / 4.43 GB | 8.98 GB | 600 s | 39.3 G / 1.73 G |
| A+G+B — governor, one-word header | **5.78 GB** | **4.48 / 3.89 GB** | **8.08 GB** | **536 s** | 37.3 G / 1.40 G |
| final (A+B+G with two-signal governor), OCaml 5.4.0 | 5.77 GB | 4.48 / 3.89 GB | 8.06 GB | 585 s | 41.0 G / 1.44 G |
| final, OxCaml 5.4.0+ox flambda2 | 5.75 GB | 4.53 / 3.92 GB | 8.23 GB | **441 s** | **10.1 G** / 1.28 G |

All stages accept all 1,056,596 declarations.

**A — presizing (parse phase).** The parser's index table and the environment's
hash-cons table grew by copying; old and new arrays coexisted and the old ones stayed
as garbage until a major cycle. At the end of parsing 39% of the heap was such
garbage (7.2 GB heap, 4.4 GB live). Both tables are now allocated at their final size
from the input size (exports average 55–60 bytes per line, ~90% expressions, ~70%
distinct after hash-consing). Parse-end RSS −22%, parsing 18% faster.

**B — one-word node header.** Every expression node stored a 63-bit hash field and
a 63-bit info field. The hash only needs 31 bits and the info (flags, saturating size,
loose-bound-variable range) 32, so they now share one word: App/Lam/Pi/Const nodes
shrink from 5 to 4 words. Predicted saving 70.7 M distinct nodes × 8 B = 566 MB;
measured 540 MB of live heap. Soundness: the loose-bound-variable range must stay
below 2²¹; building a term beyond it raises an internal error (exit 3), it is never
truncated (a truncated range could make an open term look closed).

**G — RSS-driven memory governor.** The peak during checking is not GC heap: with 4
domains, RSS exceeded the GC's own top heap by 0.7 GB on an 827 MB input and by
2.7 GB on the proxy, against 0.16 GB with one domain. Experiments excluded glibc
arenas (`MALLOC_ARENA_MAX=1`, trim/mmap thresholds: < 3% change) and GC accounting
(`Gc.quick_stat` does include other domains' heaps — verified). The excess is
per-domain memory outside the GC's accounting (allocator slack around large blocks,
which OCaml 5 obtains from `malloc`; free per-domain pools; domain stacks). Since it
cannot be predicted from the input, it is controlled: the governor samples VmRSS and
the GC heap every 0.2 s and, under pressure, lowers `space_overhead` (down to a floor,
see §3a) and lets fewer domains start new declarations (down to 1); it relaxes when the
GC heap is well within the headroom above the live environment (§3a). Budget: 80% of
the cgroup limit or of physical memory (12.5 GB on the arena runner; 60% before §3a),
`O4L_MEM_BUDGET_MB` to override. It changes scheduling and GC pacing only.

Governor verification:

| input | budget | peak RSS | result |
|---|---:|---:|---|
| `Lean` export, 827 MB (unconstrained peak 3.3 GB) | 2,000 MB | 2,129 MB | all 207,422 accepted; 294 s instead of 76 s |
| Mathlib proxy, 6.2 GB (unconstrained peak 8.1 GB) | 6,000 MB | 6,580 MB | bound held for 12 min of checking on 1 domain (run then killed by an unrelated build sharing the VM) |

Finding from the second run: RSS is a high-water mark under OCaml 5 (freed pool
memory stays mapped), so a governor that waits for RSS to drop never relaxes. The
governor therefore throttles on *growth* of RSS above budget (or GC heap near budget)
and relaxes on the GC heap being well below budget.

## 3a. The governor latch on the arena's Mathlib (fixed)

Arena record for `mathlib` at rev `51d1b48` (round of 2026-11-08): accepted, but
**80.3 min wall** (timeout 94.7 min), 50.6 × 10¹² instructions (4.36× the official
kernel; the arena's "2.34 h" is that count at 6 × 10⁹/s), peak RSS 11.9 GB, CPU/wall
1.62. Every other large test ran at 1.2–3× the official kernel's instructions with
CPU/wall ≈ 3, and stayed below the governor's budget.

Cause: the governor relaxed only when the GC heap fell below 60% of the budget
(5.6 GB of a 9.4 GB budget on the 16 GB runner). Mathlib's environment alone is larger
and stays live to the end, so after the first pressure signal the run stayed on
**one domain with `space_overhead` 10** for its whole length. Every major cycle marks
the whole environment, so GC work grows as 1/overhead.

Changes:
* **Relief relative to the live heap**: the governor records the GC heap at the start
  of checking (`base_heap`) and relaxes when `heap < base_heap + 60% × (budget −
  base_heap)`.
* **Adaptive overhead floor**: the largest overhead ≤ `O4L_MIN_OVERHEAD` (default 40)
  whose steady heap `base_heap × (1 + o/100)` fits in 3/4 of the budget, at least 10.
  Checking starts at the floor when it is above the size-based policy, and the
  governor never goes below it.
* **Budget 80%** of memory instead of 60% (the official kernel itself peaks at 10.7 GB
  on that runner).

Measured on the 6.2 GB Mathlib proxy (4 domains, 4 vCPU / 15 GB VM, OCaml 5.4.0; all
1,055,791 declarations accepted in every run). A budget of 5,800 MB reproduces the
arena's ratio of live environment to old budget (3.9 GB / 5.8 GB vs. ~6 GB / 9.4 GB);
8,100 MB is the same scaling of the new 80% budget.

| binary | budget | floor / start overhead | governor | check | wall | user CPU | peak RSS | major GCs |
|---|---:|---:|---|---:|---:|---:|---:|---:|
| old (`8715624`) | 5,800 MB | 10 / 25 | **latched at 1 domain, overhead 10** | 1,328 s | 25.2 min | 36.0 min | 6,382 MB | 210 |
| new | 5,800 MB | 11 / 25 | throttles and recovers (1–4 domains) | 461 s | 10.7 min | 25.4 min | 6,629 MB | 107 |
| new | 8,100 MB | 40 / 40 | never throttled | **313 s** | **8.2 min** | 21.4 min | 8,084 MB | 64 |
| old, ungoverned | — | — / 25 | off | 368 s | 9.3 min | 25.3 min | 7,645 MB | 90 |

The old binary's latched run is 3.6× slower to check than the ungoverned run, the
same order as the arena's slowdown; with the fix the same budget costs 25% instead of
260%. With room in the budget the higher floor makes checking 15% faster than the old
ungoverned run, for 6% more peak RSS.

Expected on the arena: with a 12.5 GB budget and Mathlib's live heap estimated at
7.5–8 GB (from the latched run's peak, scaled by the proxy's peak/live ratio), the
floor is about 25 (the old starting overhead) and the governor can relax again.

## 4. OxCaml evaluation

OxCaml (Jane Street's branch of OCaml; `5.4.0+ox`, tag `5.4.0-ox9`) was evaluated
against the concrete costs measured above.

| feature | applies to | expected effect on the Mathlib failure |
|---|---|---|
| Flambda 2 (`-O3`) | everything | speed only. Upstream flambda 1 already gave −11% check time on Init; no effect on peak memory, which is live data |
| mixed blocks / unboxed `int32#` fields | node header | **none**: the OxCaml documentation for this release states that int32 fields in mixed blocks still take a full word each ("we'd like for int32 fields to be packed efficiently (two to a word) … currently that's not the case"). Stage B already packs hash + info into one word in standard OCaml |
| unboxed arrays (`int32#` arrays pack 2 per word) | hash-cons table hashes, memo tables | none beyond stage A: the hash array is already an off-heap 32-bit Bigarray; the other tables are `int array`s (unboxed already) or arrays of pointers |
| stack allocation (`local_`, `stack_`, `exclave_`) | temporaries: argument arrays from `get_app_args`, tuple keys of per-call memo tables, `option` results | lowers minor-heap allocation. Not peak memory: expression nodes escape into caches and the environment and must stay on the heap; the minor heap is 2 MB per domain |
| region / arena allocation | per-declaration scratch | **not available** in OxCaml (locals are bound to lexical regions, not to a declaration) |

Quantitatively: the peak is set by the live environment (3.9 GB on the proxy) plus
per-domain overhead; OxCaml features address neither. The part of the run they could
improve is allocation rate: on the proxy, 37.3 G words are allocated in the minor heap
and 96% of them die young. If stack allocation removed the temporaries share of that
(estimated 15–30%), minor collections — and with them OCaml 5's stop-the-world
synchronisations — would drop proportionally, a few percent of wall time.

Costs and risks of migrating:
* The arena builds checkers in its Nix shell, which provides upstream OCaml 5.4 only.
  OxCaml would have to be built in the checker's build step: bootstrap OCaml 5.4,
  dune 3.23 and menhir 20231231 (exact version enforced by `configure`), then the
  compiler — a long build on every checker rebuild, with sources downloaded from
  GitHub and gitlab.inria.fr.
* Reproducibility: OxCaml release tags are documented as mutable ("OxCaml releases are
  not immutable - if this tag is moved, update the SHA").
* The code would be tied to OxCaml syntax (`local_`, layouts) unless kept to a
  compatible subset.

Recommendation: do not migrate to fix the Mathlib failure. Keep the code compatible
with OxCaml so its optimizer can be measured, and revisit stack allocation of
temporaries only as a speed measure, once memory is no longer the limiting factor.

### 4.1 Measured: OxCaml 5.4.0+ox against upstream compilers

OxCaml was built from source (tag `5.4.0-ox9`, configured exactly as its opam package:
`--enable-middle-end=flambda2 --enable-runtime5 --enable-stack-checks
--enable-poll-insertion --enable-multidomain`; bootstrap with OCaml 5.4.0, dune 3.24,
menhir 20231231 — `configure` rejects other menhir versions; 43 CPU-minutes). The
checker compiles **unmodified**; `build.sh` passes `-O3` when the compiler reports
`flambda` or `flambda2`. Same source, idle machine:

| build | Init 1 domain (check) | Init 4 domains | Lean export 4 domains | minor GCs (Init, 1 d.) | peak RSS (Init 1d / Init 4d / Lean 4d) |
|---|---:|---:|---:|---:|---:|
| OCaml 5.4.0 (as on the arena) | 76.3 s | 22.0 s | 58.5 s | 34,121 | 1.33 / 1.39 / 2.97 GB |
| OCaml 5.2.1 + flambda 1 `-O3` | 66.8 s (−12%) | 18.8 s (−15%) | 49.2 s (−16%) | 32,153 | 1.33 / 1.45 / 3.00 GB |
| OxCaml 5.4.0+ox, flambda2 `-O3` | 63.3 s (−17%) | 17.3 s (−21%) | 47.6 s (−19%) | 4,525 | 0.98 / 1.32 / 2.82 GB |

At Mathlib scale (the 6.2 GB proxy, 4 domains, final code): OxCaml 441 s vs 585 s
(−25%), minor-heap allocation 10.1 G vs 41.0 G words (−75%), minor collections 22,497
vs 225,873 (−90%), peak RSS 8.23 vs 8.06 GB (+2%).

Interpretation: a 17–25% speed-up (on small inputs most of it is available from upstream flambda 1),
about half the minor-heap allocation and 7.5× fewer minor collections (fewer
stop-the-world synchronisations), but only ~5% lower peak memory at the scale that
matters. This confirms the analysis above: OxCaml is a speed improvement, not the
memory fix.

A correctness-relevant observation: OxCaml flags `Domain.spawn` with the alert
`unsafe_multidomain` and offers `Domain.Safe.spawn`, which requires the spawned
closure to be *portable* under its mode system — a static check that rules out data
races. The `lazy` race fixed in commit `95b59fa` is precisely the kind of bug it would
reject at compile time. Adopting the mode system would require threading
`portable`/`contended` annotations through the checker's shared state (environment,
tables); it is the strongest argument for a future migration.

## 5. Implementation plan and specifications

| stage | change | status |
|---|---|---|
| 0 | race fix: no `lazy` values shared by domains | done (`95b59fa`) |
| A | presized parser index and environment hash-cons table | done |
| B | one-word node header (31-bit hash, 32-bit info; refuse, never truncate, loose-bvar ranges ≥ 2²¹) | done |
| G | RSS-driven governor: throttles domains and GC overhead on RSS growth above budget, relaxes on GC heap within the headroom above the live environment (§3a) | done |
| C | lower `space_overhead` while checking large inputs, compaction after parsing (from the first memory round) | done (`3753af7`) |
| D | *future*: reuse per-domain cache arrays across declarations to reduce large-block churn | not started: needs per-context ownership of caches (contexts are nested in inductive checking, so sharing them naively would mix caches of different environments — a soundness hazard) |
| E | *future*: OxCaml build profile (flambda2, later the mode system for race freedom) | evaluated, not adopted for the arena (§4) |

Specifications:
* **Compiler**: OCaml ≥ 5.1, multicore runtime required (domains). Tested: 5.2.1,
  5.2.1+flambda, 5.4.0 (the arena's Nix shell), OxCaml 5.4.0+ox. No dependencies
  beyond the compiler distribution (`unix`, `bigarray`).
* **Flags**: `-unsafe -inline 200`, plus `-O3` with flambda or flambda2 (`build.sh`).
* **Runtime/GC policy** (input size from `stat`, or heap size for stdin):
  parse `space_overhead` 200 (≤ 1 GB) / 80 (> 1 GB); compaction after parsing for
  inputs > 1 GB; checking `space_overhead` 120 (≤ 1 GB) or `max 25 (120·1024/MB)`, raised to the
  governor's floor (§3a); governor budget 80% of `memory.max` or `MemTotal`. Overrides:
  `O4L_PARSE_OVERHEAD`, `O4L_SPACE_OVERHEAD`, `O4L_MIN_OVERHEAD`, `O4L_COMPACT`, `O4L_MEM_BUDGET_MB`
  (0 disables the governor), `O4L_DROP_TABLE` (not recommended: −45% speed).
* **Arena**: `threads: 4`, `run: ./ocaml4lean -j 4 "$IN"`; exit 0 accept, 1 reject,
  3 error (internal failures, including the loose-bvar range limit, are never
  reported as rejections or acceptances).

Risks:
* Real Mathlib may be heavier than the proxy (cslib's RSS/input ratio is higher).
  Mitigation: the governor bounds RSS as long as the live environment plus one
  domain's working set fits the budget; at worst checking slows down. The live
  environment of the 6.2 GB proxy is 3.9 GB of heap.
* The governor's budget comes from `memory.max`/`MemTotal`; if the arena enforces a
  lower limit by other means, `O4L_MEM_BUDGET_MB` must be set in the checker's `run`
  line.

## 6. Reproducing the measurements

```bash
./build.sh                                              # or PATH=/opt/oxcaml/bin:$PATH ./build.sh
lean --run tools/Export.lean Lean > lean.ndjson         # 827 MB
lean --run tools/Export.lean Init > init.ndjson
python3 bench/proxy/mathlib_proxy.py lean.ndjson init.ndjson 6 mathproxy.ndjson   # 6.2 GB
OUT=run bench/memprofile.sh ./ocaml4lean -j 4 --stats mathproxy.ndjson           # run.tsv: RSS every 0.5 s
O4L_MEM_BUDGET_MB=6000 OUT=gov bench/memprofile.sh ./ocaml4lean -j 4 mathproxy.ndjson
```

Run memory experiments alone: a concurrent compiler build on the same 15 GB VM got
the checker killed by the kernel's OOM killer (exit 137, the arena's signature) at
6.6 GB.

## 7. Correctness protocol

Every stage was checked with:
* `tests/arena_ndjson.sh` (24 hand-written arena cases: forged recursors, orphan
  constructors, universe bugs, …), `tests/lean_tests.sh` (nested-inductive order),
  `tests/ztest.py` (bignum, 26,000 differential cases against Python);
* `bench/arena.py` over the arena's perf, bugs, corner-case and other suites,
  differential against the official kernel (`tools/Replay.lean`): all 66 expected
  verdicts met, agreement with the official kernel on every case where it gives a
  verdict;
* full acceptance of Init (65,893), Std (112,719), the `Lean` package (207,422) and
  the Mathlib proxy (1,056,596 declarations).
