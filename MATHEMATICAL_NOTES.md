# Proof extension: mathematical arguments and limits

All described arguments have Lean scripts in this revision; none has been
compiler-verified. These notes explain the arguments, not a proof certificate.
The original notes are preserved as `evidence/original_MATHEMATICAL_NOTES.md`.
The current coverage inventory takes precedence over their old gap list.

## No exponential output two without Zsigmondy

For p >= 2 define C(p,0)=1 and

    C(p,n+1) = C(p,n) + (p-1)*p^(2*n+1).

Induction gives

    (p+1)*C(p,n) = p^(2*n+1)+1.

If p is odd, C(p,n) is odd. If n>0, it is greater than one, so it has an odd
prime factor. Consequently an odd base and odd exponent >=3 cannot give GPF
2. The base p=2 is handled by parity, and exponent q=2 by the existing
square-output lemma. This establishes the argument for 8.1 independently of
primitive-divisor existence and supplies the exponential clause in 3.5.

## Positive multiplicative orders

The finite witness specification `ExactOrder p r k` is identified with
`orderOf (p : ZMod r) = k` for k>0. A nonzero element of the prime field has
order dividing r-1, using mathlib's finite-field theorem.

Positivity cannot be omitted. The draft's `PrimitiveDivisor r p 0` always
holds when r is prime: the zeroth power is one and there are no smaller
positive exponents. Thus the old unrestricted dependency is false. Its
refutation and the positive-exponent repair are both supplied.

## Diagonal and dyadic forcing

For prime r != 2, if p^(2^m) = -1 in ZMod r, that power is not one and its
square is one. The prime-power order lemma gives exact order 2^(m+1).
This order divides r-1, hence r is one modulo 2^(m+1).

For diagonal output r=GPF(p^2+1), the existing square-output argument excludes
r=2. Taking m=1 gives order four and r=1 modulo four, yielding 5.2, 5.3 and 8.2.
For corrected 5.5, multiply q=p^(2^m-1) modulo r by p and combine with
pq=-1. The resulting p^(2^m)=-1 gives every clause of the corrected statement.
The original, without r!=2, retains the counterexample (3,5,1).

## Quadratic characters and collisions

A square witness in Fin r is equivalent to `IsSquare` in ZMod r. This
identifies the draft's finite quadraticCharacter with mathlib's quadraticChar.
From pq=-1, multiplicativity gives the product identity in 5.4. The square
criterion for -1 separates r=1 and r=3 modulo four and gives the two character
patterns.

For a common additive and multiplicative output, elimination gives
r | p^2+p-1 and r | q^2+q-1. The explicit discriminant identity is

    (2*p+1)^2 = 4*(p^2+p-1)+5.

Thus 2*p+1 is a square-root witness for 5 modulo r. Reciprocity at the prime
5 transfers squareness to r modulo 5. The five residues have square values
0,1,4,4,1; primality and r!=5 exclude zero. This supplies 9.6 and, together
with the existing 9.7 argument, 9.8.

## Unbounded sections, all three clauses

Use Dirichlet's theorem as already formalized in mathlib v4.19.0.

- Additive: choose a prime r greater than the desired bound and p+1. Its
  nonzero residue -p-1 has a prime representative q; r divides p+q+1.
- Multiplicative: choose r greater than the bound and p. The nonzero residue
  -p^(-1) has a prime representative q; r divides pq+1.
- Exponential with fixed odd q: choose a large prime r and a prime base
  representative p of -1 modulo r. Then p^q=-1 modulo r.
- Exponential with q=2: choose a prime r=1 modulo four above the bound, using
  Dirichlet. A square root a of -1 exists modulo r and is nonzero. Use
  Dirichlet again to choose a prime p in the residue class a.

In every case, the greatest-prime-factor specification makes the output at
least r. These arguments do not require the missing Zsigmondy input.

## Exact progression reduction and analytic boundary

For nonzero a,b in a prime field, aq+b=0 has the unique residue -b/a. Its
natural representative c has 0<c<r. The affine lemma supplies the
multiplicative and additive residue classes and therefore equality of the
filtered finite counting sets in 6.1. If a+1=0 modulo r, the additive divisors
among primes are exactly q=r.

`PrimeAPInput` is still needed for the specific asymptotic limit; Dirichlet's
infinitude theorem alone is insufficient to prove that limit. The smooth
number bounds of 6.2 and the limiting arguments of 6.3 also remain absent.

The specialized primitive-divisor existence input has not been formalized
here. Its statement and its consequences remain explicitly conditional.
No claim is made that the new order lemma proves primitive-divisor existence.
