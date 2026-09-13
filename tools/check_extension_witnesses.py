#!/usr/bin/env python3
"""Finite arithmetic sanity checks only. Does NOT validate Lean proofs."""
from pathlib import Path
import json

def prime(n):
    return n >= 2 and all(n % d for d in range(2, int(n**0.5)+1))

def gpf(n):
    largest=0
    d=2
    while d*d <= n:
        while n % d == 0:
            largest=d
            n//=d
        d+=1
    return max(largest,n) if n>1 else largest

def order(p,r):
    v=1
    for k in range(1,r):
        v=v*p%r
        if v==1:
            return k
    raise AssertionError((p,r))

counts={'cofactor_identities':0,'diagonal_orders':0,'corrected_dyadic_instances':0,'collision_instances':0}
for p in range(2,41):
    c=1
    for n in range(13):
        assert (p+1)*c == p**(2*n+1)+1
        if p%2: assert c%2 == 1
        if n: assert c>1
        counts['cofactor_identities']+=1
        c+=(p-1)*p**(2*n+1)
ps=[n for n in range(2,101) if prime(n)]
for p in ps:
    r=gpf(p*p+1)
    assert r%4==1 and order(p,r)==4
    counts['diagonal_orders']+=1
    for q in ps:
        a=gpf(p+q+1);r=gpf(p*q+1)
        if a==r:
            assert (p*p+p-1)%r==0
            assert (q*q+q-1)%r==0
            assert (2*p+1)**2%r==5%r
            if r not in (2,5): assert r%5 in (1,4)
            counts['collision_instances']+=1
        for m in range(1,6):
            if r!=2 and q%r==pow(p,2**m-1,r):
                assert order(p,r)==2**(m+1)
                assert r%(2**(m+1))==1
                assert (pow(p,2**m,r)+1)%r==0
                counts['corrected_dyadic_instances']+=1
# The newly discovered dependency counterexample.
assert prime(3) and pow(2,0,3)==1
assert 3-1 != 0  # 0 does not divide 2.
report={'formal_verification':False,'notice':'Finite arithmetic checks only; no Lean compiler run.','counts':counts,'order_dependency_zero_counterexample':[3,2,0]}
(Path(__file__).resolve().parents[1]/'evidence/extension_witness_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
