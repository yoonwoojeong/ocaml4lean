# ocaml4lean: design

This document describes the kernel as it is. Every rule and every cache has a
stated reason; code without one has been removed.

## 1. Why it looks like this

The kernel logic (`tc.ml`, `inductive.ml`, `level.ml`) is the first version of
this project and has not changed in substance. What was added later to chase
benchmark time (a memory governor driven by the resident set, two NbE value
cores, tuning environment variables, GC settings chosen by input size) has been
removed: none of it changed a verdict, the NbE cores were not faster, and the
governor was a feedback loop whose behaviour depended on the machine. What
remains is one checker, one term representation, one memory rule.

## 2. Goals and non-goals

In priority order:

1. **Soundness.** Never accept an export that Lean's official kernel (v4.35.0)
   rejects. Every acceptance is justified by the rules in §5 and §6 alone.
2. **Stability.** The verdict and the exit code depend only on the input:
   - not on the number of domains, the scheduling, the timing or the
     machine's memory;
   - no feedback loops, no step limits that change verdicts, no hidden modes.
   A resource failure is reported as such (exit 3), never as a verdict.
3. **Completeness on real libraries.** Accept everything the official kernel
   accepts in Init, Std, Lean, Mathlib and the arena's test suites, within the
   arena's limits (16 GB, about 95 min for Mathlib).
4. **Simplicity.** One checker, one term representation, one algorithm. Every
   rule and every cache has a stated reason (§5–§7). Code that has no reason
   is removed.
5. **Performance**, as a consequence of 1–4, not a goal of its own. The target
   is the order of the official kernel. Losing up to 1.5× is acceptable in
   exchange for 1–4.

Non-goals:
- matching the fastest arena kernels;
- alternative cores (NbE or others);
- tuning for one benchmark;
- runtime adaptation to the machine.

## 3. Trusted base

Trusted:
- **Type checking:** `src/tc.ml`, the typing and conversion rules of §5–§6.
- **Inductive declarations:** `src/inductive.ml`, re-derivation and
  comparison.
- **Quotient checks:** in `src/check.ml`.
- **Terms and their equality:** `src/expr.ml`, `src/level.ml`, `src/name.ml`;
  term equality is load-bearing, see I1–I2.
- **Nat literals:** `src/z.ml`.

Trusted by assumption, as in the official kernel:
- the bodies of `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.mod`,
  `Nat.gcd`, `Nat.beq`, `Nat.ble`, `Nat.land`, `Nat.lor`, `Nat.xor`,
  `Nat.shiftLeft`, `Nat.shiftRight`, `Nat.pow` and of the `String`
  literal encoding, once `Check.builtins` has verified that `Nat`, `Bool`,
  `String`, `Char` and `List` have their expected types and constructors.

Not trusted (a bug there can only make a valid input fail or crash, never make
an invalid one pass):
- the parser and the NDJSON scanner, except that they must build terms
  exactly as written: the parser is part of the trusted base for *fidelity*;
- the driver, scheduling and statistics.

## 4. Architecture

```
export file ──parse──▶ environment (frozen, shared read-only)
                          │
                          ▼
              blocks in file order ──▶ worker domains (N, fixed)
                          │                 │
                          │      per block: Tc context (caches),
                          │                 per-domain scratch tier
                          ▼
                 verdict = first failing block in file order
```

1. **Parse** the whole file into an environment: constants, plus blocks in
   file order. Every term is hash-consed into the *global tier*. After
   parsing the environment is frozen.
2. **Check** blocks in parallel. Block `i` sees only constants introduced by
   blocks `< i`, plus its own members. A block is a single declaration, the
   quotient package, or an inductive block (types, constructors, recursors).
3. **Report** the first failing block in file order, or acceptance. Once a
   block is known to be rejected, later blocks are not started (they cannot
   change the verdict, and they may depend on declarations that were never
   verified: found by mutation testing, where a bogus recursor made a later
   proof exhaust memory instead of answering "reject").

There is exactly one checking path per kind of declaration, with no
fallbacks.

## 5. Typing rules (soundness-critical)

`check(e)` infers the type of a closed term with free variables carrying their
types (locally nameless), as Lean's `infer_type_core` with `infer_only = false`.
The rules are Lean's, and only the official kernel decides what they are:

| term | rule |
|---|---|
| `Sort u` | `u`'s parameters are declared; type `Sort (u+1)` |
| `c.{us}` | `c` is visible; `|us|` = its parameter count; every parameter in `us` is declared; unsafe / partial use rules; type: `c`'s type with `us` substituted |
| `fun x : A => b` | `A : Sort _`; type `Π x : A, type(b)` |
| `Π x : A, B` | `A : Sort u`, `B : Sort v`; type `Sort (imax u v)` |
| `f a` | `type(f)` reduces to `Π x : A, B`; `type(a) ≡ A`; type `B[a]` |
| `let x : A := v; b` | `A : Sort _`; `type(v) ≡ A`; type `type(b[v])` |
| `e.i` (projection) | `type(e)` reduces to a structure `S ps`; field `i` exists; if `S` is a `Prop`, field `i` must be a `Prop`, and so must every earlier field that a later field's type depends on; type: the field's type instantiated |
| Nat / String literal | the extension is enabled (`builtins`); size limits |

Declarations:
- an axiom's type is a sort;
- a definition's or opaque's value has the declared type (`≡`);
- a theorem's type is a `Prop` and its value has that type;
- unsafe and partial definitions see their mutual group;
- the quotient package must match the expected constants exactly;
- an inductive block is re-derived (positivity, universe constraints,
  parameters, nested-to-mutual translation, recursors, rules), and every
  exported member must equal the derived one.

## 6. Definitional equality and reduction

### 6.1 Rules: what `≡` means (soundness-critical)

These are equations of Lean's type theory. A rule may be applied only when its
side conditions hold. Each must match the official kernel exactly: an extra
rule, or a missing side condition, is a soundness bug.

| rule | equation | side conditions |
|---|---|---|
| β | `(fun x => b) a ≡ b[a]` | — |
| δ | `c.{us} ≡ value(c)[us]` | `c` is a definition or theorem, visible; not opaque |
| ζ | `let x := v; b ≡ b[v]` | — |
| ι | `rec … (ctor fields) … ≡ rule rhs` | rule of that constructor; argument counts; K-like recursors: the major premise is replaced by the constructor if the types agree |
| proj | `(mk ps fs).i ≡ fs_i` | `mk` is the structure's constructor |
| quot | `Quot.lift f h (Quot.mk r a) ≡ f a`, the same for `Quot.ind` | quotient package checked |
| η | `fun x => f x ≡ f` | `x` does not occur in `f`: this holds by construction when comparing |
| struct-η | `s ≡ mk ps (s.1) … (s.n)` | `S` is a non-recursive structure; types agree |
| proof irrelevance | `p ≡ q` | `type(p) : Prop`, `type(p) ≡ type(q)` |
| unit-like | `a ≡ b` | `type(a) ≡ type(b)` is a non-recursive structure with one zero-field constructor |
| Nat literals | `n ≡ succ^n zero`; `Nat.op lit lit ≡ lit` | builtins verified; size limits |
| String literals | `"s" ≡ String.ofList [chars]` | builtins verified |
| levels | `Sort u ≡ Sort v` iff `u ≡ v` (normal form) | — |

### 6.2 Strategy: how `≡` is searched (not soundness-critical)

Everything in this subsection affects only time, and completeness when a
resource runs out. It never affects soundness, because it only decides which
rules of §6.1 to try and in what order.

- **Order of attempts:** Lean's `is_def_eq_core`, which is quick checks,
  `whnf_core`, proof irrelevance, lazy δ by definitional height, then
  application congruence, η, struct-η, literals, unit-like. Kept, because
  completeness on real libraries depends on following the official kernel's
  order; every departure must be justified by a test case.
- **Same-head shortcut** (compare the arguments before unfolding): kept, as
  Lean.
- **Caches:** see §7.
- **Heuristics with no counterpart in Lean's kernel:** none.

Each `whnf` or `≡` call either returns or raises a resource error (stack or
memory). There are no step limits. Like the official kernel, ocaml4lean may
diverge on inputs that diverge in Lean; the arena's timeout handles those.

## 7. Invariants

Each invariant states what it guarantees and how it is, or is to be, checked.
The debug-mode checks (I1–I3) are not implemented yet (§11).

**I1. Global maximal sharing.** Two structurally equal terms in the global tier
are physically equal. Consequence: for two global terms, `==` is structural
equality, which is what `Expr.equal`'s shortcut relies on.
*Check:* after parsing, rehash every global node and assert uniqueness.

**I2. Equality is never concluded from distinctness.** `Expr.equal a b`
concludes "different" only from structure, never from `a != b`, except when
both are global (I1). Fresh terms (built during checking) are compared
structurally behind a hash check.
*Check:* in debug mode, every `Expr.equal` result is compared with a plain
structural equality.

**I3. Caches are memo tables.** Every cache returns exactly what recomputing in
the same context would return.

| cache | key | value | scope |
|---|---|---|---|
| `infer_tbl`, `infer_only_tbl` | term (structural) | its type | block (Tc context) |
| `whnf_core_tbl`, `whnf_tbl` | term | its normal form; only full (not cheap) reductions are stored | block |
| `unfold_tbl` | `c.{us}` | the instantiated value | block |
| `success`, `failure` | unordered term pair | `≡` holds / the same-head shortcut failed | block |
| traversal memos (`instantiate`, `lift`, `abstract`, `instantiate_lparams`) | (node, binder offset) | the result | one traversal |

"Context" means: environment view (position, local constants), universe
parameters, safety. All are fixed for a block, so block scope is sound.
`eager` affects only which rules are tried, not their results.
*Check:* in debug mode, a sample of cache hits (every k-th) is recomputed and
compared.

**I4. Position-based visibility.** Block `i` reads only constants with
`pos < i`, and its own members through `local`. Nothing a block learns is
visible to another block.
*Check:* differential runs with 1 and N domains give identical outputs (§10).

**I5. Domain isolation.** Mutable state is either per domain (scratch
hash-cons tier, traversal memos, Tc contexts) or immutable after parsing.
Lazy values are never shared between domains (OCaml 5 raises on concurrent
forcing).
*Check:* code review rule: no module-level mutable or `lazy` values outside
`Domain.DLS`, enforced by a grep test.

**I6. Verdicts versus errors.** Only `Kernel_error` is a verdict (reject,
exit 1). Stack overflow, out of memory and internal exceptions are exit 3,
never a rejection or an acceptance.

**I7. No truncation.** Packed metadata (hash, size, loose bound-variable range)
saturates or raises; a value is never truncated. A truncated loose-bvar range
could make an open term look closed.
*Check:* unit tests at the limits.

**I8. Extensions are gated.** Nat and String literal rules apply only when
`builtins` verified the declarations they rely on (§3).

## 8. Resources

**Cost model.** Measured on Init: about 75% of checking time goes to the
substitution machinery and the memory it allocates (rebuilding terms in
`instantiate` and `instantiate_lparams` 19%, structural equality of fresh terms
17.5%, hash-cons lookups 7%, GC 26%). The kernel logic itself is about 7%. This
is the official kernel's algorithm, so parity with it is the realistic ceiling.
Repeated `instantiate` work inside one declaration is only 8.4% of node visits
(58% across declarations, which no per-block cache can use); an exact
whole-call cache was slower (104.5 s against 83 s on Init), and two
closure-based cores were at parity or worse. Improvements must come from lower
per-step cost, never from approximations.

**Memory model.** Peak ≈ E·(1 + o/100) + N·W, where E is the live environment
(about 0.65× the export size after hash-consing), o the GC space overhead, N
the number of domains and W the largest working set among blocks checked at
the same time. E dominates on Mathlib-scale input.

**Memory rule (`bin/main.ml`), computed once.** After parsing, the heap is
compacted and the live size L is read. The overhead for checking is the largest
o in [25, 120] with L·(1 + o/100) at most 30% of the machine's memory (cgroup
limit or physical). Nothing is adjusted afterwards. Running out of memory is an
error (exit 3), never a verdict. The 30% is measured: with 4 domains the peak
resident set is about 1.8× the heap target (a 50% target peaked at 13.3 GB on
the 6.2 GB Mathlib proxy on a 16 GB machine).

Measured with 4 domains on 4 vCPU / 16 GB (wall time / peak resident set):

| input | declarations | o | time | peak |
|---|---:|---:|---:|---:|
| Init | 66,110 | 120 | 27.4 s | 1.43 GB |
| Std | 113,988 | 120 | 47.3 s | 1.94 GB |
| Lean package | 207,493 | 120 | 59.5 s | 3.02 GB |
| Mathlib proxy (6.2 GB) | 1,055,791 | 25 | 391.9 s | 8.35 GB |

The governor it replaces took 357.8 s and 8.66 GB on the proxy. The arena's
runner has shown about 35% more resident memory than this machine for the same
input, which would put the proxy near 11.3 GB of its 16 GB.

## 9. Environment variables

`O4L_TIMES=1` prints the slowest blocks; `O4L_DEBUG=1` prints both sides when
an exported inductive member differs from the derived one. Neither changes
what is checked. There are no tuning variables.

## 10. Verification

Gates for every change, all of which must pass:

1. **Arena suites:** `tests/arena_ndjson.sh`, and `bench/arena.py` over the
   bugs, corner-case, other and perf suites. Every prescribed outcome is met,
   and the result agrees with the official kernel wherever it gives a verdict.
2. **Acceptance:** all of Init, Std, the `Lean` package and the Mathlib proxy.
3. **Determinism:** identical output with `-j 1` and `-j 4` on Init and Std
   (I4, I5).
4. **Invariant mode** (I1–I3, I7): not implemented yet (§11).
5. **Unit tests:** `tests/ztest.py` (bignum), level normalization, and the I7
   limits.

6. **Reference differential:** `ref/` (section 13) and `src/` give the same
   verdict on every arena case and on every mutant produced by
   `tests/mutate.py` (random corruption of expressions, levels, declarations).

To add:
- **Mutation testing against the official kernel:** require rejection wherever
  the official kernel rejects (today only the two checkers are compared).
  nano-lean's `nl-mutate` is a model.
- **Official-kernel differential:** `tools/Replay.lean` on every test, where
  the official kernel is available.

## 11. Not done yet

- Debug-mode checks for I1–I3 and unit tests at the packing limits (I7).
- Mutation testing against the official kernel (today the two checkers are
  compared with each other).
- `Expr.equal` starts memoising node pairs after 4096 comparisons; the bound
  is a measured compromise, not derived.

## 13. Two checkers

`ref/` is a second checker whose only job is to be easy to trust (`ref/README.md`):
plain terms, no hash-consing, exact memo tables only, no search heuristics beyond
Lean's lazy-delta order, universe levels decided semantically, and no code shared
with `src/`. It is slow (about 7x on Init and without sharing it cannot do the
performance suites), so it is a test oracle, not a product. Any faster core
is accepted only
if it gives the reference's verdict on everything the reference can decide.

Differences in verdict are recorded, not hidden: the reference accepts
`corner-cases/imax-*` (equal levels that the official kernel's normalization does
not see; outcome `either`).

Findings so far from running the two against each other:
- the reference initially accepted `bugs/proj-of-subst-prop` (it answered "not a
  proposition" for a stuck sort instead of failing; lean4 PR 14807);
- `src/` kept checking after a rejection and could be driven out of memory by a
  later block (section 4, step 3; fixed).
