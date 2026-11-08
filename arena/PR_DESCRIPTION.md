Add ocaml4lean checker

This adds [ocaml4lean](https://github.com/yoonwoojeong/ocaml4lean), an independent Lean 4 kernel written in OCaml 5. It follows the official kernel's algorithm. It re-derives every inductive block, including nested and mutual ones, and requires the exported constructors and recursors to be identical to the derived ones. Declarations are checked on 4 OCaml domains.

- **Build:** `./build.sh` uses only the `ocaml` compiler from the arena's flake (5.4 in nixos-26.05). It needs no dune or opam packages; `Nat` literals use its own bignum module. Built and run from a fresh clone of the pinned rev with OCaml 5.4.0.
- **Exit codes:** 0 accept, 1 reject, 3 error. It never declines and accepts any axiom, as the official kernel does. Unparsable input and internal failures (stack or memory exhaustion) exit with 3 and are never reported as a rejection.
- **Checked locally against the official kernel (v4.35.0):**
  - Exports of `Init` and `Std` are accepted.
  - On the arena's perf, bugs, corner-cases and other tests, every expected accept and reject is met. Where both kernels give a verdict they agree, and both run until the time limit on the two `eta-struct-major-*-no-whnf` cases.
  - The `tutorial` group was not run locally, because it needs lean4export.
- **Performance:**
  - Checking `Init` took 65 s on one core and 19 s on 4 domains; the official kernel took 55 s.
  - Peak memory is about six times the export size, so the `mathlib` test may run out of memory on the arena's machines. That would show up as an error, not a rejection.

Written by Claude (Anthropic), directed by @yoonwoojeong.
