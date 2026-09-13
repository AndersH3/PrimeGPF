# Mathematical audit and remaining proof obligations

## Result 5.5 is false without an odd-output hypothesis

The counterexample is p=3, q=5, m=1, r=2. The source hypotheses hold,
but both the claimed order 4 and the claimed congruence 2 ≡ 1 modulo 4
fail. The problematic proof step is the assertion that
p^(2^m) ≡ −1 implies p^(2^m) is not congruent to 1. This needs r≠2.

Adding r≠2 repairs this obstruction. With odd prime r, the assumed
congruence and pq≡−1 yield p^(2^m)≡−1. The multiplicative order t then
divides 2^(m+1) and does not divide 2^m. Every divisor of a power of two
is a power of two, so t=2^(m+1). Lagrange's theorem gives t∣r−1.
The minimal-order statement supplies the primitive-divisor conclusion.
This is the proof route for `t5_5_corrected`, not a claim that its Lean
proof has been completed.

There is also a family of counterexamples to the uncorrected statement:
keep p=3, q=5 and choose any m≥1. The congruence hypothesis still holds
modulo 2, but 2 is not 1 modulo 2^(m+1).

## Definition 4.1 and the cofactor one

Definition 2.1 only defines P⁺(n) for n>1. Theorem 4.1 uses P⁺(s) when
s≥1. In particular, s=1 occurs when the kernel is prime. The source's
following “equivalently smooth” sentence gives the appropriate interpretation.

The Lean statement is

```
gpf n = r ↔ ∃ s, 0 < s ∧ n = r*s ∧ Smooth r s
```

with r prime and n>1. `Smooth r 1` holds because 1 has no prime divisors.
The implementation totalizes GPF at 0 and 1 by zero; substantive theorems
never use that convention to create a greatest prime divisor of 1.
This is a domain clarification, not a new prime factorization rule.

## The diagonal proof needs an explicit exclusion of output two

Theorem 5.2 appears correct, but its proof uses p²≢1 modulo r after
establishing p²≡−1. As in 5.5, that requires r≠2. Unlike 5.5, the diagonal
hypotheses force this exclusion: p=2 gives GPF(5)=5; odd p gives p²+1>2
and p²+1≡2 modulo 4, so it is not a power of two.

`gpf_ne_two_of_mod_four` and `square_output_ne_two` contain scripts for
this preliminary argument. The finite-field order argument and its
connection to the full `t5_2` still need implementation and checking.

## Uniformity in the density argument

A fixed-anchor estimate with a threshold depending on the anchor cannot
simply be summed over all anchors p≤x without further justification.
This is a proof-detail gap in the last paragraph of 6.3, not a numerical
counterexample to its conclusion.

For a uniform repair, let S_r(X) count positive r-smooth integers ≤X.
For each p≤x, multiplication sends each eligible q≤x injectively to
pq+1≤x²+1. Addition sends it injectively to p+q+1≤2x+1. Therefore

- N_r^mul(x) ≤ π(x) S_r(x²+1);
- N_r^add(x) ≤ π(x) S_r(2x+1).

The elementary exponent-box bound gives S_r(X)=O_r((log X)^π(r)).
Combining these uniform inequalities with π(x)~x/log x gives both
global zero-density conclusions. This repair remains an outstanding
Lean proof. The inventory includes `UniformPolylogFibers`, so the
r-only implied constant in 6.2 is not silently weakened to an arbitrary
anchor-dependent constant. Its eventual threshold may depend on the
fixed anchor, which is made explicit in the quantifier order.

## Statement conventions

- The carrier is the subtype `{p : ℕ // Nat.Prime p}`. The arithmetic
  kernels in the source are positive, so using natural numbers preserves
  their meaning. Subtraction in p²+p−1 and exponent q−1 is natural-number
  subtraction; the relevant prime hypotheses prevent truncation.
- “Odd prime” is encoded as `Nat.Prime p` and `p≠2`.
- Congruences use natural remainders or `Nat.ModEq`. A congruence to −1 is
  expressed by divisibility of the corresponding expression plus one.
- Modular inverse assertions use explicit witnesses for inverses.
- `quadraticCharacter` is the usual Legendre character specified by a
  finite square test. Its required multiplicativity and reciprocity laws
  have not been connected to mathlib in this draft.
- A primitive divisor is encoded by primality and the absence of smaller
  positive exponents giving residue one. In the displayed positive prime
  base cases, this is the same primitive-divisor property for p^k−1.
- Counts use natural cutoffs. Since the counted quantities change only at
  integers, this is the natural discrete formulation of the source's
  asymptotic claims. A real-cutoff equivalence lemma is not supplied.
- Bounds use positive exponents where the kernel exceeds one. Forms such
  as q+3=2^m preserve the source's q=2^m−3 under those bounds.
- Statement definitions are not evidence. `t8_3`, for example, is merely
  a proposition until a proof is supplied. Conditional consequences take
  their dependencies as visible arguments; no such dependency is a global
  axiom or a hidden admission.

## What remains before completion

First, compile and repair the draft against the specified Lean/mathlib
release. No proof script, including a short computational one, has been
accepted by Lean in this session. Library APIs referenced in the draft
were checked selectively against public documentation, not against a
local v4.19.0 installation.

After that, implement the outstanding unconditional arguments:

1. **5.2 and corrected 5.5:** modular orders, divisors of powers of two,
   Lagrange's theorem, and primitive-divisor certificates.
2. **5.4 and the last clause of 9.6:** Legendre-character laws and the
   quadratic-reciprocity specialization to 5. The polynomial elimination
   in 9.6 is already represented by a partial proof script.
3. **6.1:** residue-class counting identities and the prime number theorem
   in arithmetic progressions. Dirichlet infinitude alone does not prove
   the asymptotic statement.
4. **6.2:** the injective exponent-vector encoding of smooth integers,
   finite counting bound, logarithmic bounds, and the uniform constant.
5. **6.3:** ratio limits, the prime number theorem, and the uniform global
   argument described above.
6. **6.4:** prime-existence arguments in the required progressions, including
   finite-field roots of order 2q for the exponential section.
7. **8.3:** the precise Bang–Zsigmondy primitive-divisor theorem with the
   exceptional pair (2,3), plus the finite-field order divisibility input.
   `ZsigmondyInput` and `OrderDividesPrimePred` are explicit, unproved
   dependency propositions. The script deriving 8.3 from them does not
   establish either dependency.

Once these are proved, replace conditional proof applications with the
established dependency proofs and update the coverage inventory. Retain
5.5's original refutation and clearly distinguish the corrected theorem.
A complete final axiom audit must contain no theory-specific assumptions.

## Reference material used for Lean interfaces

- [Lean installation](https://lean-lang.org/install/)
- [mathlib prime definitions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Prime/Defs.html)
- [mathlib prime lemmas](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Prime/Basic.html)
- [Natural-number divisibility](https://leanprover-community.github.io/mathlib4_docs/Init/Data/Nat/Dvd.html)
- [Natural-number congruences](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/ModEq.html)
- [Finite-set counting and pigeonhole principles](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Card.html)

The mathematical claims and theorem numbering come from the attachment,
which is included unchanged. The documentation links describe library
interfaces; they are not substitutes for a successful Lean build.
