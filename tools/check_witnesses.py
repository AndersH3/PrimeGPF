#!/usr/bin/env python3
"""Independent finite arithmetic checks. This is NOT Lean verification."""
from pathlib import Path
import json


def gpf(n):
    if n <= 1:
        raise ValueError("requires n > 1")
    d, best = 2, 1
    while d * d <= n:
        while n % d == 0:
            best, n = d, n // d
        d += 1
    return max(best, n)


def add(p, q): return gpf(p + q + 1)
def mul(p, q): return gpf(p * q + 1)
def exp(p, q): return gpf(p ** q + 1)


cases = [
    ("3.2 exponential noncommutativity", [exp(2,3), exp(3,2)], [3,5]),
    ("3.3 additive nonassociativity", [add(add(2,2),5), add(2,add(2,5))], [11,5]),
    ("3.3 multiplicative nonassociativity", [mul(mul(2,2),3), mul(2,mul(2,3))], [2,5]),
    ("3.3 exponential nonassociativity", [exp(exp(2,2),2), exp(2,exp(2,2))], [13,11]),
    ("3.5 odd multiplicative closure failure", [mul(3,5)], [2]),
    ("3.6 additive cancellation failure", [add(2,2), add(2,7)], [5,5]),
    ("3.6 multiplicative cancellation failure", [mul(2,2), mul(2,7)], [5,5]),
    ("3.6 multiplicative distributivity failure", [mul(2,add(2,3)), add(mul(2,2),mul(2,3))], [7,13]),
    ("3.6 additive distributivity failure", [add(2,mul(2,2)), mul(add(2,2),add(2,2))], [2,13]),
    ("3.7 mixed add/mul", [mul(add(2,2),2), add(2,mul(2,2))], [11,2]),
    ("3.7 mixed add/exp", [exp(add(2,2),2), add(2,exp(2,2))], [13,2]),
    ("3.7 mixed mul/exp", [exp(mul(2,2),2), mul(2,exp(2,2))], [13,11]),
    ("3.8 additive monotonicity", [add(3,3), add(5,3)], [7,3]),
    ("3.8 multiplicative monotonicity", [mul(3,3), mul(5,3)], [5,2]),
    ("3.8 exponential base monotonicity", [exp(5,2), exp(7,2)], [13,5]),
    ("3.8 exponential exponent monotonicity", [exp(2,2), exp(2,3)], [5,3]),
    ("7.3 fixed point and two-cycle", [add(2,3), add(2,2), add(2,5)], [3,5,2]),
    ("8.4 exceptional identity", [exp(2,3)], [3]),
]
results = []
for name, actual, expected in cases:
    assert actual == expected, (name, actual, expected)
    results.append({"name": name, "actual": actual, "expected": expected, "passed": True})
p, q, m = 3, 5, 1
r = mul(p,q)
assert q % r == pow(p, 2**m - 1, r)
assert r % (2**(m+1)) != 1
results.append({"name": "5.5 counterexample", "p":p, "q":q, "m":m, "r":r,
                "hypothesis_satisfied":True, "conclusion_false":True, "passed":True})
report = {"kind":"finite arithmetic checks, not formal verification", "passed":len(results),
          "lean_checked":False, "checks":results}
path = Path(__file__).resolve().parents[1] / "evidence" / "witness_checks.json"
path.write_text(json.dumps(report, indent=2) + "\n")
print(f"{len(results)} finite arithmetic checks passed; Lean verification was not performed.")
