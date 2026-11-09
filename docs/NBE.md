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

On 4 domains: v1 36.8 s wall, step 1 55.6 s (Tc: 32.9 s).

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

## Conclusion so far

Every form of memoization that keeps OCaml values reachable for the rest of a
declaration (global tables, caches on closures or neutrals) makes them survive
minor collections; the promotion and major-GC cost exceeds the work saved, even
where the work falls 3x. All versions accept all of Init (and v1 all of Std).
