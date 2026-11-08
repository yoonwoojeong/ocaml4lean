#!/usr/bin/env python3
"""Build a Mathlib-scale, semantically valid export for memory experiments.

Mathlib's 5.8 GB export cannot be produced here, so this builds an input of the
same size and shape from real Lean code:

    BASE (e.g. the `Lean` package export, which contains Init)
    + K copies of every BASE declaration that is not in SHARED (e.g. Init),
      with all names re-rooted under a fresh root `C_k`.

References from a copy to SHARED constants keep their original names, all other
references point into the same copy.  SHARED must be closed under dependencies
(Init only depends on Init) and contain every name the kernel treats specially
(Nat, Eq, Quot, ...), so each copy is an alpha-renamed duplicate of real code and
the whole file is a valid environment: every declaration must be accepted.
Like Mathlib, the copies share the prelude and differ elsewhere, so hash-consing
deduplicates only what genuinely coincides.

usage: mathlib_proxy.py BASE.ndjson SHARED.ndjson K OUT.ndjson
"""
import json, sys

DECL_KINDS = {"axiom", "def", "thm", "opaque", "quot"}


def full_names(path):
    """name index -> full name string, and the set of declared constant names."""
    names, decls = {0: ""}, set()
    def s_of(i):
        return names[i]
    with open(path, encoding="utf-8") as f:
        for l in f:
            if l.startswith('{"in"') or '"in":' in l[:14]:
                o = json.loads(l)
                if "str" in o:
                    p = names[o["str"]["pre"]]; names[o["in"]] = (p + "." if p else "") + o["str"]["str"]
                else:
                    p = names[o["num"]["pre"]]; names[o["in"]] = (p + "." if p else "") + str(o["num"]["i"])
            elif '"in":' not in l and '"il":' not in l and '"ie":' not in l and '"meta"' not in l:
                o = json.loads(l)
                kind = next(iter(o))
                d = o[kind]
                if kind == "inductive":
                    for part in ("types", "ctors", "recs"):
                        for t in d[part]: decls.add(names[t["name"]])
                else:
                    decls.add(names[d["name"]])
    return names, decls


def main():
    base, shared, k, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
    _, shared_decls = full_names(shared)
    names, _ = full_names(base)
    kept = {i for i, s in names.items() if s in shared_decls}   # name indices of shared constants
    lines = [l for l in open(base, encoding="utf-8").read().split("\n") if l]
    maxn = max(names)
    maxl = maxe = 0
    for l in lines:
        if '"il":' in l[:14] or l.startswith('{"il"'):
            maxl = max(maxl, json.loads(l)["il"])
        elif '"ie":' in l:
            o = json.loads(l)
            if "ie" in o: maxe = max(maxe, o["ie"])
    NN, NL, NE = maxn + 2, maxl + 1, maxe + 1
    with open(out, "w", encoding="utf-8") as f:
        for l in lines:
            f.write(l + "\n")
        for c in range(1, k + 1):
            dn, dl, de = c * NN, c * NL, c * NE
            root = dn + NN - 1                       # index of the new root name C_c
            f.write(json.dumps({"in": root, "str": {"pre": 0, "str": "C_%d" % c}}, separators=(",", ":")) + "\n")
            nm = lambda i: i + dn if i != 0 else root      # re-rooted copy of name i
            cn = lambda i: i if i in kept else i + dn      # constant reference
            lv = lambda i: i + dl if i != 0 else 0
            ex = lambda i: i + de
            def expr_obj(o):
                key = next(k2 for k2 in o if k2 != "ie")
                v = o[key]
                if key == "bvar": pass
                elif key == "sort": o[key] = lv(v)
                elif key == "const": v["name"] = cn(v["name"]); v["us"] = [lv(x) for x in v["us"]]
                elif key == "app": v["fn"] = ex(v["fn"]); v["arg"] = ex(v["arg"])
                elif key in ("lam", "forallE"):
                    v["name"] = nm(v["name"]); v["type"] = ex(v["type"]); v["body"] = ex(v["body"])
                elif key == "letE":
                    v["name"] = nm(v["name"]); v["type"] = ex(v["type"]); v["value"] = ex(v["value"]); v["body"] = ex(v["body"])
                elif key == "proj": v["typeName"] = cn(v["typeName"]); v["struct"] = ex(v["struct"])
                elif key == "mdata": v["expr"] = ex(v["expr"])
                elif key in ("natVal", "strVal"): pass
                else: raise ValueError("unknown expr kind " + key)
                o["ie"] = ex(o["ie"])
                return o
            def level_obj(o):
                for key in ("succ",):
                    if key in o: o[key] = lv(o[key])
                for key in ("max", "imax"):
                    if key in o: o[key] = [lv(x) for x in o[key]]
                if "param" in o: o["param"] = nm(o["param"])
                o["il"] = lv(o["il"])
                return o
            def const_common(d):
                d["name"] = cn(d["name"]); d["levelParams"] = [nm(x) for x in d["levelParams"]]
                d["type"] = ex(d["type"])
                if "value" in d: d["value"] = ex(d["value"])
                if "all" in d: d["all"] = [cn(x) for x in d["all"]]
            for l in lines:
                o = json.loads(l)
                if "meta" in o: continue
                if "in" in o:
                    if "str" in o: o["str"]["pre"] = nm(o["str"]["pre"])
                    else: o["num"]["pre"] = nm(o["num"]["pre"])
                    o["in"] = nm(o["in"])
                elif "il" in o: o = level_obj(o)
                elif "ie" in o: o = expr_obj(o)
                else:
                    kind = next(iter(o)); d = o[kind]
                    if kind == "inductive":
                        if all(t["name"] in kept for t in d["types"]): continue
                        for t in d["types"]:
                            const_common(t); t["ctors"] = [cn(x) for x in t["ctors"]]
                        for t in d["ctors"]:
                            const_common(t); t["induct"] = cn(t["induct"])
                        for t in d["recs"]:
                            const_common(t)
                            for r in t["rules"]: r["ctor"] = cn(r["ctor"]); r["rhs"] = ex(r["rhs"])
                    elif kind in DECL_KINDS:
                        if d["name"] in kept: continue
                        const_common(d)
                    else:
                        raise ValueError("unknown line kind " + kind)
                f.write(json.dumps(o, separators=(",", ":"), ensure_ascii=False) + "\n")
            print("copy %d done" % c, file=sys.stderr, flush=True)


main()
