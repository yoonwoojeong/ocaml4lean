# ocaml4lean — a small, fast Lean 4 proof checker in OCaml

`ocaml4lean` is an independent checker ("external kernel") for Lean 4. It reads an
environment in the [lean4export](https://github.com/leanprover/lean4export) NDJSON
format (v3.x) and re-checks every declaration: axioms, definitions, theorems,
opaques, the quotient package, and (mutual, nested) inductive types, whose
constructors and recursors it re-derives and compares with the exported ones.

It follows the semantics of Lean's C++ kernel (`src/kernel/type_checker.cpp`,
`inductive.cpp`, `level.cpp`, `quot.cpp` at v4.35.0), including its definitional
equality heuristics (lazy delta reduction, proof irrelevance, eta, structure eta,
unit-like types, Nat/String literal extensions, `eagerReduce`).

* **Correct on everything tested**: all of Lean's `Init` (65 893 constants) and `Std`
  (112 719 constants) are accepted, and on the 94 soundness/corner/perf cases of the
  [lean-kernel-arena](https://arena.lean-lang.org) run here it meets every expected
  outcome and agrees with the official kernel wherever both could run (see
  [PERFORMANCE.md](PERFORMANCE.md#validation)).
* **Small trusted core, no dependencies**: ~3 600 lines of OCaml using only the
  compiler distribution (its own small bignum module, `src/z.ml`, for `Nat`
  literals). No OCaml `Obj` magic except reading two fixed record fields (see
  `Expr.hash`).
* **Fast**: on one core it needs 1.18× (`Init`) to 1.38× (`Std`) the official kernel's
  time; declarations are checked in parallel on OCaml 5 domains, and with 4 domains it
  checks `Init` in 0.35× and `Std` in 0.46× of the official kernel's time.

See [PERFORMANCE.md](PERFORMANCE.md) for the benchmark results and analysis.

## Build

Needs only an OCaml ≥ 5.1 compiler (tested with 5.2.1 and 5.4.0; an `flambda`
compiler is ~11% faster):

```bash
./build.sh
```

This produces `./ocaml4lean`. With dune installed, `dune build` builds the same
sources (binary `_build/default/bin/main.exe`). `tests/ztest.py` checks the bignum
module against Python integers.

## Usage

```bash
./ocaml4lean [-j N] [--stats] [-q] FILE.ndjson
```

`FILE` may be `-` for stdin. `-j N` checks with N domains. Exit codes follow the
lean-kernel-arena: 0 = accepted, 1 = rejected (the first failing declaration is
printed), 3 = error (I/O, unparsable input, or an internal failure such as running
out of stack or memory, which is never reported as a rejection). The checker never
declines (code 2).
Axioms other than `propext`, `Classical.choice`, `Quot.sound` are accepted (as the
official kernel does) but listed on stderr. `O4L_TIMES=1` prints the slowest
declarations.

### Producing inputs and the official baseline

Building `lean4export` was not possible in the environment this was developed in, so
`tools/` contains two small Lean programs that need only a Lean toolchain:

* `tools/Export.lean` — writes the lean4export v3.1.0 NDJSON format, dependency
  ordered (`lean --run tools/Export.lean Init > init.ndjson`; `-- decl…` restricts the
  output to the given declarations and their dependencies). Unsafe declarations and
  `mdata` are omitted, as lean4export does by default.
* `tools/Replay.lean` — re-checks the same constants with Lean's official C++ kernel
  (`Kernel.Environment.replay` into an empty environment, as the arena's "official"
  checker does) and reports the kernel time.

## Benchmarks and tests

* `bench/run.sh [WORKDIR] [Init Std …]` — exports each module, then measures the
  official kernel and ocaml4lean with 1/2/4 domains (wall time, peak RSS, GC stats)
  into `WORKDIR/results.tsv`.
* `bench/arena.py ARENA_DIR WORKDIR [globs]` — compiles each lean-kernel-arena test,
  exports its declarations, runs both checkers and compares with the expected outcome.
* `tests/arena_ndjson.sh ARENA_DIR` — the arena's hand-written `.ndjson` cases (fast
  regression test).

## Design

| file | lines | role |
|---|---|---|
| `src/name.ml`, `src/level.ml` | 270 | names; universe levels (normalisation, `≤`, equivalence) |
| `src/expr.ml` | 610 | terms, hash-consing, instantiate/abstract, structural equality, caches |
| `src/tc.ml` | 910 | type inference, whnf, definitional equality, literals, quotients |
| `src/inductive.ml` | 600 | inductive types: nested→mutual, positivity, universes, recursors |
| `src/check.ml` | 280 | per-declaration checks, quotient & builtin validation, parallel driver |
| `src/parse.ml`, `json.ml`, `fastline.ml` | 490 | NDJSON reader (generic JSON + allocation-free fast path) |
| `src/z.ml` | 260 | arbitrary-precision naturals for `Nat` literals |

**Terms.** Locally nameless: de Bruijn indices for bound variables, free variables
carry their type (and let-value), so inference needs no local context lookups.
Binder names and binder infos are not stored (they do not affect typing), which makes
alpha-equivalent terms identical. Each node caches its structural hash, a
loose-bound-variable range, has-fvar/has-universe-param flags, a saturating tree size
and a "global" bit, all packed in one int; a node is a single 5-word block.

**Hash-consing.** The environment read from the file is hash-consed into a global
table (shared, read-only after parsing, so safe for parallel readers). Terms built
during checking are *not* interned: maintaining a mutable scratch table (write
barriers, growth, GC marking of the table) cost more than sharing saved. They are
only looked up in the global table when all their children are global. Equality is
`==` for two global nodes and otherwise a hash-guarded structural comparison
(memoised for large DAGs).

**Memoisation.** Per declaration: inference (two modes), whnf, whnf_core, definition
unfolding, and def-eq success/failure caches, all open-addressing tables that store
hashes inline. Substitution traversals memoise on (node, offset); small traversals use
a short-lived table, large ones migrate to a reusable flat-array table.

**Parallelism and visibility.** Every declaration block gets its position in the
stream; while checking block *p* only constants of blocks *< p* are visible (plus the
block's own constants where the kernel adds them first). So the parallel check
accepts exactly what a sequential replay would, while all blocks are checked
independently on a work queue of domains.

**Inductive types.** Nothing exported for an inductive block is trusted: the types,
constructors, `numNested`, `isRec`, `isReflexive`, recursor types, rules, `k`, … are
derived as `inductive.cpp` does (including the nested-to-mutual translation and the
restoration of auxiliary recursors `rec_1…`) and the exported declarations must be
identical to the derived ones (matched by name; universe parameter names compared
up to renaming).
Exported constructors or recursors not derived from the block are rejected.

**Builtins.** The `Nat`/`String` literal extensions are enabled only when `Nat`,
`Nat.zero`, `Nat.succ` (and `Bool`, `String.ofList`, `Char.ofNat`, `List`) have the
expected inductive shapes and the accelerated `Nat.*` functions have the expected
types. As in the official kernel, the accelerated functions themselves are trusted to
be the standard ones. The quotient package must be declared as one block with exactly
the four expected types, after a well-formed `Eq`.

### Trusted base

The OCaml compiler and runtime, the bignum module `src/z.ml`, the NDJSON reader,
and the checker sources above. Like the official kernel, it trusts that `Nat.add`,
`Nat.mul`, … in the input are the standard definitions when accelerating them.

## Lean Kernel Arena

`arena/ocaml4lean.yaml` is the checker definition submitted to the
[Lean Kernel Arena](https://github.com/leanprover/lean-kernel-arena) (it goes in its
`checkers/` directory). It builds with `./build.sh` using the arena's Nix shell, which
provides OCaml, and runs `./ocaml4lean -j 4 "$IN"`.
