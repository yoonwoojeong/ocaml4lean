# Restart proposal: prune to the kernel

Status: **proposal, waiting for the owner's decision.** Nothing has been deleted
or rewritten yet. Every number below is from `git log`/`wc` on this repository
or from a measurement already recorded in `docs/` or `PERFORMANCE.md`.

## 1. What the history shows

The kernel logic has barely changed since the first commit (`4fae34b`); the
growth is in the memory and performance layer around it.

| file | first commit | `main` (`6f94226`) | what changed |
|---|---:|---:|---|
| `tc.ml` (typing, whnf, defeq) | 910 | 916 | lazy constants made eager (race fix) |
| `inductive.ml` | 598 | 598 | 4 lines (nested-order fix) |
| `level.ml`, `name.ml`, `env.ml`, `json.ml`, `vec.ml` | 459 | 467 | nothing of substance |
| `expr.ml` | 347 | 611 | hash-cons tiers, `Emap`/`Pset`/`Memo`/`MemoH` caches, budgeted `equal`, packed header |
| `hc.ml` | 49 | 154 | two tiers, off-heap hash array, presizing, slot tracking |
| `check.ml` | 275 | 409 | memory governor (feedback on RSS), driver knobs |
| `bin/main.ml` | 52 | 158 | GC policy by input size, compaction, memlog, budget |
| `parse.ml` + `fastline.ml` | 193 | 388 | allocation-free scanner, index arrays |

PR by PR: PR #1 built the checker and the perf layer (243 s to 64 s on Init,
`PERFORMANCE.md`); PR #2 fixed a real false rejection (nested order) and
started the size-dependent GC policy; PR #3 and PR #5 added and then re-tuned
the governor (feedback control that latched on the arena). The open PR #6
removed the NbE cores and tuning knobs, fixed two hash-table defects, added the
independent reference checker `ref/` (2,042 lines) and mutation testing, and
found one real defect with it (blocks started after a rejection).

So: **the "initial version" is still there**, inside `src/tc.ml`,
`src/inductive.ml`, `src/level.ml`. What got messier is the adaptive layer:
three memory policies selected by input size, a governor, debug/measurement
hooks in the product, five documents that partly supersede each other.

## 2. Options

**A. Grow `ref/` into the product.** Rejected. It is about 7x slower than
`src/` on Init and cannot run the perf suites or Mathlib because plain trees lose
the export's sharing (`ref/README.md`). To fix that it would need exactly the
machinery of `src/expr.ml` and `src/hc.ml` (hash-consed environment,
lifting-aware substitution, per-domain isolation), and it would stop being an
independent oracle. Its value is independence; keep it as the oracle.

**B. Prune `src/` to the kernel (recommended).** Keep the kernel files as they
are, delete the adaptive layer, replace three memory policies by one rule,
rewrite the driver, consolidate the docs. Expected size: about 3,000 lines of
`src/` + `bin/` (from 3,936), zero tuning environment variables (from 4 on
`main`, 2 on the branch), one memory rule instead of three.

**C. Rewrite from scratch.** Rejected. The kernel files are already the initial
design, validated on 94 arena cases, Init, Std, the `Lean` package and the proxy,
and agree with the official kernel wherever it gave a verdict. A rewrite re-risks
exactly the bugs the reference needed three fixes for (`ref/README.md`).

## 3. Plan under B: keep / delete / rewrite

**Keep unchanged** (trusted base, `docs/DESIGN.md` §3): `tc.ml`, `inductive.ml`,
`level.ml`, `name.ml`, `z.ml`, `env.ml`, `json.ml`, `fastline.ml`, `parse.ml`
(reader), `vec.ml`; `ref/` entire; `tests/`, `tools/`, `bench/arena.py`,
`bench/proxy`, `arena/`.

**Delete** (each a separate, individually verified commit):

| item | lines | why |
|---|---:|---|
| governor (`Check.governor_*`, `run`'s pause loop, budget in `main.ml`), `O4L_MEM_BUDGET_MB`, `O4L_MIN_OVERHEAD` | ~130 | feedback control; verdict timing depends on the machine; latched once already |
| memlog phases, `/proc` readers in `main.ml`, `O4L_MEMLOG` | ~40 | measurement belongs in `bench/memprofile.sh` (external sampling), not the product |
| three GC policies by input size (200/80, 120/25, compaction over 1 GB) | ~25 | replaced by one rule (below) |
| `MemoH` wrapper, `O4L_DEBUG` dumps in `check.ml` | ~20 | trivial after phase 1; debug output moves behind `O4L_CHECK` |
| expression scratch tier bookkeeping (`track`/`used` in `hc.ml`) | ~25 | fresh expressions are never interned since `66161eb`; only names and levels use the local tier |
| `PERFORMANCE.md` "what made it fast", `docs/MEMORY.md` stages, `docs/NBE.md`, `docs/CLOSURE.md` as separate live docs | — | move to one dated `docs/HISTORY.md` of measurement records; `README.md` and `arena/ocaml4lean.yaml` lose the governor paragraph |

**Rewrite:**

| item | into |
|---|---|
| `bin/main.ml` (158 lines) | ~60 lines: parse, one memory rule, run, report; `--stats`, `-q`, `-j` only |
| `Check.run` driver | a plain work queue over domains, the first-rejection cut-off, no scheduling feedback |
| memory policy | one rule computed once after parsing: `space_overhead = clamp(60% of memory / live heap − 1, 25, 120)`; domains fixed by `-j`; out of memory is exit 3, never a different verdict. **Must be validated on the Mathlib proxy before the governor is deleted** (`DESIGN.md` §12) |
| `Expr.equal` budget (4096) + pair memo | decide by measurement between (a) as is and (b) memo from the start above a size bound; keep whichever is simpler within the 1.5x allowance |
| `docs/DESIGN.md` | becomes the design of the code as it is (no "compared with main"), with every rule's reason |

**Add:** `O4L_CHECK=1` invariant mode (I1–I3, I7 of `DESIGN.md` §7), a
`tests/gates.sh` that runs every gate below in one command, and a determinism
test (`-j 1` vs `-j 4` byte-identical output).

## 4. Gates for every commit

1. `tests/arena_ndjson.sh` on the arena's hand-written cases (24).
2. `bench/arena.py` on bugs, corner-cases, other and perf suites; verdict agrees
   with the official kernel wherever it has one (needs Lean).
3. Acceptance of Init, Std, the `Lean` package and the Mathlib proxy (needs Lean
   to export; exports are not in the repository).
4. `-j 1` and `-j 4` give byte-identical output on Init and Std.
5. `ref/refcheck` and `ocaml4lean` agree on every arena case and on N mutants of
   `tests/mutate.py` (N = 2,000 per step).
6. Time within 1.5x of `main` on Init (1 and 4 domains), Std and the perf suite;
   peak RSS on the proxy within the arena's 16 GB at 4 domains.

## 5. Branch mechanics (nothing forced)

`main` is not rewritten. PR #6 is a strict improvement of `main` (same verdicts,
within 5% in time, one defect fixed) and is the natural base: either merge it
first and do §3 as PR #7 onwards, or append §3 to it. Each deletion in §3 is one
commit with the gates' results in its message, so any step can be reverted alone.

## 6. Decisions needed from the owner

1. Option B (prune `src/`, keep `ref/` as oracle), or A or C?
2. Merge PR #6 first, or fold the pruning into it?
3. Memory: accept the static rule, with "out of memory, exit 3" as the honest
   failure on the arena if the proxy validation fails? (The alternative is to keep
   a governor, which §2 of `DESIGN.md` rules out.)
4. Keep parallel checking at 4 domains (recommended: it is ~3x on the arena's
   time for ~50 lines, and gate 4 pins it down)?
5. Measurement records: keep in `docs/HISTORY.md` (recommended) or drop?
6. Permission to install Lean 4.34.1 via elan in the work environment, needed for
   gates 2, 3 and 6 (OCaml 5.4.0 is being installed via apt/opam).

## 7. Corrections to earlier notes

- "58% of `instantiate` work is redundant, ceiling 1.8x" was wrong: 8.4%
  within one declaration (`docs/CLOSURE.md` §2).
- `README.md` says "~3,600 lines"; `src/` + `bin/` is 3,936 on `main`.
- `arena/ocaml4lean.yaml` and `README.md` describe the governor as a feature;
  under this plan it is removed.

## 8. State of the branch, verified in the proposal's environment (2026-11-09)

OCaml 5.4.0 (opam), 4 vCPU, 15 GB; Lean not installed, so gates 2, 3 and 6
were not run.

| check | result |
|---|---|
| `tests/arena_ndjson.sh`, production checker | 24/24 as expected |
| same, `ref/refcheck` | 24/24 as expected |
| production vs reference exit codes on the 24 cases | identical |
| `ref/tests/run_levels.sh` (level procedure vs brute force) | 20,000 pairs, 0 mismatches |
| `tests/ztest.py` (bignum vs Python) | 26,000 cases, 0 mismatches |
| `tests/mutate.py`, 400 mutants of `corner-cases/proof-param-ok` + 300 of `bugs/rec-missing-ih` | 0 disagreements |
