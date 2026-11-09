# NbE prototype: measurements

Prototype of a value-based checker for declaration values (`src/nbe.ml`, enabled
with `O4L_NBE=1`; any exception falls back to `Tc`, so every rejection is `Tc`'s).
All numbers: `Init` export (66,110 declarations), 4 vCPU / 15 GB VM, OCaml 5.4.0,
`O4L_NBE_FUEL=300000`, `O4L_NBE_STATS=1` for the counters. "check" is the checking
phase on 1 domain; the current checker (Tc) takes ~76 s for it (32.9 s wall on
4 domains for the whole run).

## Versions

| version | check (1 domain) | minor / promoted / major (G words) | evals | neutrals | unfolds | conversions |
|---|---:|---:|---:|---:|---:|---:|
| Tc (current checker) | ~76 s | 9.1 / 0.56 / 0.98 | — | — | — | — |
| v1: closures, no memo except closed terms (`430b505`) | 80 s | 18.0 / 1.01 / 1.10 | 392 M | 217 M | 33.6 M | 39.9 M |
| global interning of thunks, environments, neutrals, binders | 243 s | 19.9 / 3.24 / 7.65 | 116 M | 48 M | 15.4 M | 23.1 M |
| step 1: memo in objects (unfold on neutral + closure application cache) | 134 s | 15.1 / 3.69 / 3.77 | 247 M | 154 M | 18.0 M | 39.6 M |
| step 1, unfold memo only | 108 s | 17.6 / 2.35 / 2.43 | 371 M | 207 M | 29.7 M | — |
| step 1, closure cache only | 134 s | 15.8 / 3.84 / 3.92 | 256 M | 161 M | 22.6 M | — |
| step 2: global interning without the binder table | 211 s | 18.9 / 3.23 / 6.96 | 116 M | 48 M | 15.4 M | — |
| step 2: interning only thunks of terms of size >= 16 | 329 s | 25.0 / 5.11 / 9.56 | 228 M | 81 M | 24.9 M | — |

| step 3, `src/nbh.ml` (`O4L_NBE=2`): integer handles in unscanned Bigarray storage, interning environments, neutrals and thunks (`O4L_NBH_INTERN=1`) | 129 s | 13.4 / 0.10 / 0.16 | 116 M | 48 M | 12.2 M | 23.1 M |
| step 3, integer handles, memo for closed terms only (default) | 81 s | 10.2 / 0.12 / 0.21 | 283 M | 206 M | 29.7 M | 39.4 M |

On 4 domains (wall, whole run): v1 36.8 s, step 1 55.6 s, step 3 interned 45.7 s.
Final comparison run back to back: Tc 30.2 s / 30.2 s, step 3 (default) 33.8 s / 35.0 s.
Std on 4 domains: Tc 64.5 s, step 3 65.9 s (113,988 accepted, 109,969 decided by Nbh).

Global interning, minor heap size (OCAMLRUNPARAM s=): 2M words 259 s, 8M 281 s,
32M 288 s; promotion stays ~3.1 G words, so it is not a minor-heap-size effect:
the intern tables are large arrays in the major heap, and every value stored in
them is promoted by the write barrier.

## Table hit rates under global interning (Init)

| table | hits | misses (= inserts) |
|---|---:|---:|
| thunks (evaluation memo by term, substitution, environment) | 102 M | 163 M |
| environments | 171 M | 108 M |
| neutrals | 52 M | 48 M |
| binders | 55 | 63 M |
| success cache | 0.7 M | — |
| failure cache | 12 k | — |

## Step 3 notes

* Integer handles remove the GC cost: promoted words fall from 3.2 G (global
  interning) to 0.1 G, below Tc's 0.56 G.
* With interning, lookups are then the cost: 47% of the time was in the intern
  tables' probe loop, at ~1.1 probes per lookup, i.e. a cache miss on the slot and
  another on the record. Packing epoch, hash tag and id into one slot word and
  writing the hot lookups without closures took it to 37%, still 129 s.
* Without interning (closed-term memo only) the handle core is v1 without its GC
  share: 81 s on 1 domain, roughly Tc's ~76 s, and 12-16% slower than Tc on
  4 domains.

## Conclusion so far

Every form of memoization that keeps OCaml values reachable for the rest of a
declaration (global tables, caches on closures or neutrals) makes them survive
minor collections; the promotion and major-GC cost exceeds the work saved, even
where the work falls 3x. Moving the values out of the GC's reach (step 3)
removes that cost, but then the intern lookups cost more than they save, and
without them the NbE core does as much work as Tc's substitutions. None of the
versions beats the current checker: the best (step 3 without interning) is on
par on 1 domain and 12-16% slower on 4. All versions accept all of Init; v1 and
step 3 also all of Std; tests/arena_ndjson.sh passes with each.
