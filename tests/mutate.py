#!/usr/bin/env python3
"""Differential mutation testing of two checkers on corrupted exports.

usage: mutate.py BASE.ndjson N SEED CHECKER_A CHECKER_B [OUTDIR]

Takes a valid export, applies one random mutation (a corrupted expression,
level or declaration line), runs both checkers, and reports every mutant on
which their verdicts differ (accept / reject / could-not-decide).  A
disagreement is a bug in one of them (or a documented difference such as the
reference checker's semantic universe levels; see ref/README.md).
Verdicts are exit codes: 0 accept, 1 reject, 3 undecided, 'timeout'.
"""
import json, os, random, subprocess, sys, tempfile, shutil

def run(checker, path, timeout):
    try:
        p = subprocess.run(["bash", "-c", 'ulimit -v 8000000; exec "$0" -q "$1"', checker, path],
                           capture_output=True, text=True, timeout=timeout)
        return p.returncode if p.returncode in (0, 1, 3) else 3, p.stdout.strip()[:120]
    except subprocess.TimeoutExpired:
        return "timeout", ""

def mutate_line(obj, nexpr, nlevel, nname, rnd):
    """Return (mutated object, description) or None.  New references point only
    to definitions made before this line, so mutants stay well formed and the
    type checker (not the reader) has to find the corruption."""
    r = rnd.random
    be = obj.get("ie", nexpr); bl = obj.get("il", nlevel)
    def rexpr(): return rnd.randrange(1, max(2, be))
    def rlevel(): return rnd.randrange(0, max(1, bl))
    def rname(): return rnd.randrange(1, max(2, nname))
    if "ie" in obj:
        if "bvar" in obj:
            obj["bvar"] = max(0, obj["bvar"] + rnd.choice([-1, 1, 2]))
            return obj, "bvar"
        if "sort" in obj:
            obj["sort"] = rlevel(); return obj, "sort level"
        if "const" in obj:
            c = obj["const"]
            if c["us"] and r() < 0.5:
                i = rnd.randrange(len(c["us"])); c["us"][i] = rlevel(); return obj, "const level"
            c["name"] = rname(); return obj, "const name"
        for k in ("app",):
            if k in obj:
                f = rnd.choice(["fn", "arg"]); obj[k][f] = rexpr(); return obj, "app " + f
        for k in ("lam", "forallE"):
            if k in obj:
                f = rnd.choice(["type", "body"]); obj[k][f] = rexpr(); return obj, k + " " + f
        if "letE" in obj:
            f = rnd.choice(["type", "value", "body"]); obj["letE"][f] = rexpr(); return obj, "let " + f
        if "proj" in obj:
            if r() < 0.5: obj["proj"]["idx"] = max(0, obj["proj"]["idx"] + rnd.choice([-1, 1]))
            else: obj["proj"]["struct"] = rexpr()
            return obj, "proj"
        if "natVal" in obj:
            v = int(obj["natVal"]); obj["natVal"] = str(max(0, v + rnd.choice([-1, 1, 7]))); return obj, "nat literal"
        return None
    if "il" in obj:
        for k in ("succ",):
            if k in obj: obj[k] = rlevel(); return obj, "level succ"
        for k in ("max", "imax"):
            if k in obj:
                if r() < 0.4:
                    del obj[k]; obj["imax" if k == "max" else "max"] = None
                    return None  # handled below
                i = rnd.randrange(2); obj[k][i] = rlevel(); return obj, "level " + k
        return None
    for kind in ("def", "thm", "opaque", "axiom"):
        if kind in obj:
            d = obj[kind]
            f = rnd.choice([x for x in ("type", "value") if x in d])
            d[f] = rexpr(); return obj, kind + " " + f
    if "inductive" in obj:
        d = obj["inductive"]
        c = rnd.choice(["numParams", "isRec", "k", "rule", "rectype", "ctortype", "numNested", "isReflexive"])
        if c == "numParams":
            t = rnd.choice(d["types"]); t["numParams"] = max(0, t["numParams"] + rnd.choice([-1, 1])); return obj, "ind numParams"
        if c in ("isRec", "isReflexive"):
            t = rnd.choice(d["types"]); t[c] = not t[c]; return obj, "ind " + c
        if c == "numNested":
            t = rnd.choice(d["types"]); t[c] = t[c] + 1; return obj, "ind numNested"
        if c == "k":
            if not d["recs"]: return None
            t = rnd.choice(d["recs"]); t["k"] = not t["k"]; return obj, "rec k"
        if c == "rule":
            rs = [x for x in d["recs"] if x["rules"]]
            if not rs: return None
            t = rnd.choice(rs); ru = rnd.choice(t["rules"])
            ru[rnd.choice(["rhs", "nfields"])] = rexpr() if r() < 0.7 else ru["nfields"] + 1
            return obj, "rec rule"
        if c == "rectype":
            if not d["recs"]: return None
            rnd.choice(d["recs"])["type"] = rexpr(); return obj, "rec type"
        if c == "ctortype":
            if not d["ctors"]: return None
            rnd.choice(d["ctors"])["type"] = rexpr(); return obj, "ctor type"
    return None

def main():
    base, n, seed, ca, cb = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
    outdir = sys.argv[6] if len(sys.argv) > 6 else "mutants"
    os.makedirs(outdir, exist_ok=True)
    rnd = random.Random(seed)
    lines = open(base, "rb").read().split(b"\n")
    if lines and lines[-1] == b"": lines.pop()
    nexpr = nlevel = nname = 0
    kinds = []  # (line index, class)
    for i, l in enumerate(lines):
        if l.startswith(b'{"ie":'): nexpr += 1; kinds.append(i)
        elif l.startswith(b'{"il":'): nlevel += 1; kinds.append(i)
        elif l.startswith(b'{"in":'): nname += 1
        elif l.startswith((b'{"def"', b'{"thm"', b'{"opaque"', b'{"axiom"', b'{"inductive"')):
            kinds.extend([i] * 3)  # declaration lines are more likely targets
    names_before = []
    cnt = 0
    for l in lines:
        names_before.append(cnt)
        if l.startswith(b'{"in":'): cnt += 1
    stats = {}
    disagree = 0
    done = 0
    tmp = tempfile.mkdtemp()
    while done < n:
        i = rnd.choice(kinds)
        obj = json.loads(lines[i])
        m = mutate_line(obj, nexpr + 1, nlevel + 1, names_before[i] + 1, rnd)
        if m is None: continue
        obj, what = m
        if obj is None or any(v is None for v in obj.values()): continue
        new = json.dumps(obj, separators=(",", ":")).encode()
        if new == lines[i]: continue
        path = os.path.join(tmp, "m.ndjson")
        with open(path, "wb") as f:
            f.write(b"\n".join(lines[:i] + [new] + lines[i + 1:]) + b"\n")
        ra, ma = run(ca, path, 60)
        rb, mb = run(cb, path, 60)
        done += 1
        key = (what, ra, rb)
        stats[key] = stats.get(key, 0) + 1
        if ra != rb and not (ra == "timeout" and rb == "timeout"):
            disagree += 1
            keep = os.path.join(outdir, f"mutant_{seed}_{done}.ndjson")
            shutil.copy(path, keep)
            print(f"DISAGREE #{done} line {i + 1} ({what}): A={ra} B={rb}\n   A: {ma}\n   B: {mb}\n   saved {keep}", flush=True)
    shutil.rmtree(tmp, ignore_errors=True)
    print(f"\n{done} mutants, {disagree} disagreements")
    acc = sum(v for (w, a, b), v in stats.items() if a == 0 and b == 0)
    rej = sum(v for (w, a, b), v in stats.items() if a == 1 and b == 1)
    print(f"both accept: {acc}, both reject: {rej}, other: {done - acc - rej}")
    return 1 if disagree else 0

if __name__ == "__main__":
    sys.exit(main())
