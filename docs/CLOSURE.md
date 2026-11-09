# A closure-based evaluator: analysis and decision record

Status: **analysis only, no evaluator built.** The measurements below argue
against building one in the form that was asked for. This document records them
so the decision can be made on evidence.

## 1. What a faster core would have to remove

Profile of the checking phase on Init (docs/DESIGN.md section 8): about 75% of
the time is the substitution machinery and its memory: `instantiate` and
`instantiate_lparams` 19%, structural equality of freshly built terms 17.5%,
hash-cons lookups 7%, GC 26%. The kernel's own logic is about 7%.

## 2. How much of that is repeated work?

Measured with an instrumented scratch build (not in the tree): every node visit
of `instantiate_core` / `instantiate1` is keyed by (node, binder depth, the
substituted terms) and looked up in a table of everything seen before.

| scope of the table | node visits that repeat an earlier one |
|---|---:|
| whole run (across declarations) | 58% |
| **within one declaration (block)** | **8.4%** (core 8.2%, `instantiate1` 9.2%) |

Only the second line is usable: each block is checked in a fresh context, and
anything kept across blocks is a cross-block cache with its memory and GC cost.
An earlier statement in this project's notes that "58% of the work is redundant,
ceiling 1.8x" was wrong for that reason; the achievable ceiling from removing
repeats inside a block is a few percent.

Two direct experiments agree (Init, 1 domain, 4 vCPU, same machine):

| change | time |
|---|---:|
| baseline | 80.9-83.2 s |
| checked inference results also used by `infer_only` | 82.8-85.7 s (no change) |
| exact whole-call `instantiate` cache, 2^18 direct-mapped slots | 104.5 s, +0.5 GB, 17.5% hit rate |

## 3. What the earlier closure/NbE attempts showed

`docs/NBE.md`: a closure-based core (v1) took 80 s against 76 s for the
substitution checker, doing 392 M evaluations; every form of memoisation that
kept values alive made it slower (promotion and intern lookups cost more than
the work saved); with integer handles outside the GC's reach it was level on 1
domain and 12-16% slower on 4. So replacing substitution by closures moved the
cost (closure and neutral allocation) without removing it.

## 4. Why a *complete* closure checker is harder than the prototypes were

Lean's definitional equality is untyped and calls `infer` on arbitrary terms
(proof irrelevance, eta, struct eta, unit-like, K). A value-based checker
therefore needs one of:

1. **Typed values**: every neutral carries its type, lambdas carry a way to
   infer their body type (a term-directed `infer` over closures), and
   environment entries carry types. This keeps Lean's algorithm but is a
   second, larger type checker.
2. **Type-directed conversion** (Coquand-style). Simpler, but it is a
   *different algorithm* from Lean's. The soundness-regression tests
   (`bugs/alg-conv-*`, `proj-of-subst-prop`, `rec-k-lie`, ...) exist because the
   exact shape of the algorithm decides which inputs it accepts; the reference
   checker needed two fixes to get them right. Any such change must be
   re-validated against all of them and against the official kernel.

Neither is a small change; both would sit next to `Tc` for inductive blocks
(which are term-level) unless those are ported too.

## 5. Conclusion and options

Evidence: the repeated-work route is closed (8% inside a block); the closure
route has been measured twice at parity or worse; a complete version is a large
rewrite whose expected gain over the substitution core is, on that evidence,
small.

Options, with what each would need:

* **Do not build it.** Keep `src/` + `ref/`. Spend effort on what the reference
  made possible: official-kernel mutation differential, more bug-class tests.
* **Build it as a bounded experiment** (typed values, option 1 above) in the
  reference's plain-tree setting first (`ref/`-style, no hash-consing), so the
  evaluation strategy is compared with the substitution engine on the same data
  structures. Gate: at least 1.3x faster than the substitution engine on the
  same inputs and the same verdicts on every reference case and mutant;
  otherwise stop.
* **Reduce per-step cost in the current design** instead (representation,
  allocation, equality of fresh terms: 17.5% + 26% + 7% of the profile). These
  are measured costs with identifiable causes, unlike the repeated-work idea.
