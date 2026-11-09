# ocaml4lean: design

Status: **draft for review.** It describes the kernel as it should be, compared
with `main` at `6f94226`. Decisions still open are marked **[open]**.

## 1. Why this document

Recent work optimized one number, the arena's time, by borrowing techniques
from other kernels piece by piece: a memory governor, then two NbE value cores
(`docs/MEMORY.md`, `docs/NBE.md`). Each piece solved a problem of the system it
came from and created new ones here. The fixes for those piled up as limits,
fallbacks and environment variables. None of the NbE variants beat the current
checker, and the governor is a feedback controller compensating for memory
behaviour that was never designed.

This document starts again from what a kernel must guarantee, and keeps only
what that requires.

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
   is the order of the official kernel (currently 1.2–1.8× its instructions
   outside Mathlib). Losing up to 1.5× is acceptable in exchange for 1–4.

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
3. **Report** the first failing block in file order, or acceptance.

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
- **Heuristics with no counterpart in Lean's kernel:** none. Today there are
  none on `main` either; the NbE branch's bounded `same`, fuel and depth
  limits go with the NbE code (§9).

Each `whnf` or `≡` call either returns or raises a resource error (stack or
memory). There are no step limits. Like the official kernel, ocaml4lean may
diverge on inputs that diverge in Lean; the arena's timeout handles those.

## 7. Invariants

Each invariant states what it guarantees, and how it is checked
(`O4L_CHECK=1`, one debug switch, §10).

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

**Cost model.** Measured on Init (`docs/NBE.md` §1; profile in the
investigation of PR #6). About 75% of checking time goes to the substitution
machinery and the memory it allocates:
- rebuilding terms in `instantiate` and `instantiate_lparams`: 19%;
- structural equality of fresh terms: 17.5%;
- looking up new nodes in the hash-cons table: 7%;
- GC: 26%.

The kernel logic itself is about 7%. That matches the official kernel's
algorithm, which ocaml4lean follows. Improvements within this design must come
from not doing redundant work, sharing-aware and with exact caches, and never
from approximations. One flaw is suspected and to be verified: `Emap`, `Pset`
and `Memo` set bit 0 of every key and also use the low bits as the slot index,
so half the slots are never used directly and probe chains cluster.

**Memory model.** Peak ≈ E·(1 + o/100) + N·W, where:
- E is the live environment (about the export size);
- o is the GC space overhead while checking;
- N is the number of domains;
- W is the largest per-block working set among blocks checked at the same
  time.

E dominates on Mathlib.

**Policy: static, computed once at startup [open: validate on the Mathlib
proxy].** Choose o from the machine's memory and E, so that E·(1 + o/100) is
at most 60% of memory, clamped to [25, 120]. Fix N (4 in the arena). There
is no runtime governor:
- it changes scheduling and GC pacing based on timing;
- it latched on the arena's Mathlib (PR #5);
- it is a feedback loop that §2.2 rules out.

If the static policy cannot fit Mathlib on the arena runner, the honest
outcome is exit 3 (out of memory), and the fix is reducing E or W by design
(representation), not control.

## 9. What to delete

| item | reason |
|---|---|
| `src/nbe.ml`, `src/nbh.ml`, `O4L_NBE*`, the hooks in `check.ml` | no performance benefit (`docs/NBE.md`); a second checker breaks "one path" |
| memory governor (`Check.governor_*`, `O4L_MEM_BUDGET_MB`, `O4L_MIN_OVERHEAD`) | feedback control (§8) [open: until the static policy is validated] |
| `O4L_SPACE_OVERHEAD`, `O4L_PARSE_OVERHEAD`, `O4L_COMPACT`, `O4L_DROP_TABLE` | tuning knobs; one computed policy instead |
| `O4L_MIGRATE`, `O4L_MEMO_MIN` and the two-stage `MemoH` (small table that migrates to a flat memo) | one traversal memo, one rule |
| `Expr.equal`'s budget and pair memo | to replace with a sharing-aware equality: memoize on node pairs from the start for terms above a size bound. Keep the semantics; remove the magic number 4096 [open: measure] |

Kept:
- `O4L_TIMES` and `--stats` (diagnostics);
- `O4L_DEBUG`, renamed to `O4L_CHECK` (§10).

## 10. Verification

Gates for every change, all of which must pass:

1. **Arena suites:** `tests/arena_ndjson.sh`, and `bench/arena.py` over the
   bugs, corner-case, other and perf suites. Every prescribed outcome is met,
   and the result agrees with the official kernel wherever it gives a verdict.
2. **Acceptance:** all of Init, Std, the `Lean` package and the Mathlib proxy.
3. **Determinism:** identical output with `-j 1` and `-j 4` on Init and Std
   (I4, I5).
4. **Invariant mode:** `O4L_CHECK=1` on Init passes (I1–I3, I7).
5. **Unit tests:** `tests/ztest.py` (bignum), level normalization, and the I7
   limits.

To add:
- **Mutation testing:** perturb exports (a constructor's type, a recursor rule,
  a universe level) and require rejection wherever the official kernel
  rejects. nano-lean's `nl-mutate` is a model.
- **Official-kernel differential:** `tools/Replay.lean` on every test, where
  the official kernel is available.

## 11. Plan

Each phase ends with all gates passing (§10) and no new environment variables.

1. **Strip.** Delete §9's items except the governor. Fix the suspected
   slot-indexing flaw if it is confirmed. *Exit:* gates pass; line count and
   knobs reduced; performance within 5% of today.
2. **Make the invariants checkable.** Add `O4L_CHECK` and the determinism and
   unit tests. *Exit:* gate 4 passes on Init and Std.
3. **Static memory policy.** Replace the governor; validate on the Mathlib
   proxy with the arena's memory-to-environment ratio. *Exit:* proxy peak
   within budget at 4 domains, with no throttling code.
4. **Exact-sharing traversals and equality.** Unify the traversal memos and
   `Expr.equal` under one memo discipline (I3). *Exit:* no magic thresholds;
   performance at least as today.
5. **Mutation testing.** *Exit:* every mutation class has a rejection test.

## 12. Open questions

- Can the static memory policy fit Mathlib at 4 domains on 16 GB? It needs a
  measurement on the proxy at the arena's ratio before the governor goes.
- Should terms built during checking be hash-consed in the scratch tier, so
  that equality is physical everywhere and I2 becomes trivial? This was
  reverted in 66161eb for speed; under §2's priorities it may be worth a
  modest slowdown. Decide by measurement against the 1.5× allowance.
- Which arena perf tests, if any, rely on heuristics beyond Lean's order? None
  is known; check during phase 4.
