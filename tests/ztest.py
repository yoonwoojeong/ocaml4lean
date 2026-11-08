#!/usr/bin/env python3
"""Differential test of src/z.ml against Python integers."""
import random, subprocess, sys
random.seed(1)
def rnd():
    k = random.choice([0, 1, 5, 27, 28, 29, 55, 56, 57, 64, 100, 300, 1000])
    return random.getrandbits(k) if k else random.randint(0, 3)
ops = {"add": lambda a, b: a + b, "sub": lambda a, b: max(a - b, 0), "mul": lambda a, b: a * b,
       "div": lambda a, b: a // b if b else 0, "mod": lambda a, b: a % b if b else a,
       "gcd": lambda a, b: __import__("math").gcd(a, b), "and": lambda a, b: a & b,
       "or": lambda a, b: a | b, "xor": lambda a, b: a ^ b, "cmp": lambda a, b: (a > b) - (a < b),
       "bits": lambda a, b: a.bit_length()}
lines, exp = [], []
for _ in range(20000):
    op = random.choice(list(ops)); a, b = rnd(), rnd()
    lines.append(f"{op} {a} {b}"); exp.append(str(ops[op](a, b)))
for _ in range(2000):
    a, k = rnd(), random.randint(0, 200)
    for op, f in (("shl", lambda: a << k), ("shr", lambda: a >> k), ("pow", lambda: rnd() ** 0)):
        pass
    lines.append(f"shl {a} {k}"); exp.append(str(a << k))
    lines.append(f"shr {a} {k}"); exp.append(str(a >> k))
    b = random.randint(0, 3000); e = random.randint(0, 40)
    lines.append(f"pow {b} {e}"); exp.append(str(b ** e))
out = subprocess.run([sys.argv[1]], input="\n".join(lines) + "\n", capture_output=True, text=True).stdout.split("\n")
bad = [(l, e, o) for l, e, o in zip(lines, exp, out) if e != o]
print(f"{len(lines)} cases, {len(bad)} mismatches")
for b in bad[:10]: print(b)
sys.exit(1 if bad else 0)
