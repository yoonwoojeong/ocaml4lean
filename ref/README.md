# Reference checker

A second, deliberately simple checker for Lean 4 exports, written to be read and
trusted rather than to be fast. It shares **no code** with `src/` (own JSON
reader, bignum, terms, levels, type checker, inductive derivation), so a bug in
one is unlikely to be in the other. It exists to be the oracle that faster
checkers are tested against.

Build and run (OCaml >= 5.1, nothing else):

```
ref/build.sh                       # produces ref/refcheck
ref/refcheck [-q] [-j N] FILE.ndjson   # same exit codes as ocaml4lean: 0 / 1 / 3
ref/tests/run_levels.sh            # universe-level decision procedure vs brute force
python3 tests/mutate.py BASE.ndjson N SEED CHECKER_A CHECKER_B   # mutation differential
```

## What is different from `src/` (on purpose)

| | `src/` (production) | `ref/` |
|---|---|---|
| terms | hash-consed, packed metadata | plain trees, substitution without lifting (substituted terms are always closed) |
| caches | many, with invariants I1-I3 | exact memo tables keyed by whole terms (infer, whnf, defeq) |
| checking | `infer_only` mode, flags (`eager`, `cheap_proj`) | everything always fully checked; no flags |
| `let` | free variables with values | substituted |
| universe levels | normal forms | **decided semantically**: for all assignments of the parameters. Exact (split on parameters under `imax`, then term domination), cross-checked against brute force |
| literals | gated on verified builtins | same gating for conversion; typing a literal only needs `Nat`/`String` to exist, as in the official kernel |
| parallelism, memory policy | domains, governor | none |

The conversion *rules* are Lean's (docs/DESIGN.md section 6.1). The search order
follows Lean's lazy delta reduction, because unfolding order decides which
inputs terminate.

## Known differences in verdict

* `corner-cases/imax-nested-absorption`, `imax-right-successor` (`outcome: either`):
  the reference **accepts** because the two levels are equal for every assignment;
  the official kernel and `src/` reject them (incomplete normalization). Accepting
  is sound, and the tests allow it.
* Everything in the performance suites and large libraries that needs sharing:
  plain trees lose the DAG structure of the export, so such inputs time out or
  run out of memory (exit 3 or a signal), never a wrong verdict.

## Evidence so far

* `tests/arena_ndjson.sh`-style cases: 24/24 as expected.
* Exported suite cases (perf, bugs, corner-cases, other; 71): 51 agree with
  `src/`, 2 are the `imax` cases above, 18 are timeouts / out-of-memory on
  performance cases. No wrong verdict.
* Init prefixes: the first 26,023 of 66,110 declarations are accepted (255 s,
  about 7x slower than `src/`); the whole of Init does not finish in 25 minutes.
* Mutation testing (`tests/mutate.py`): random single corruptions of Init
  prefixes and the hand-written arena files; the two checkers must give the
  same verdict on every mutant.

## Bugs the reference had, found by running the arena (kept as a record)

* `is_prop` answered "no" for a stuck type of a type instead of failing
  (`bugs/proj-of-subst-prop`, lean4 PR 14807): accepted a proof of `False`.
* Literal typing was gated on declarations that appear later in the file.
* The first universe-level procedure enumerated assignments and blew up with
  many parameters; replaced by the exact procedure.
