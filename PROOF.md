# Specialized primitive-divisor proof

Let p and q be prime, q odd, and (p,q) different from (2,3). Write q=2n+1 and
N=oddCofactor p n, so (p+1)N=p^q+1.

1. The recurrence proves that N is odd and N>q outside the excluded pair.
2. If a prime r divides N and p+1, reduction modulo r gives N congruent to q.
   Hence r=q.
3. If every prime divisor of N divides p+1, the existing prime-support theorem
   gives N=q^k with k>0; furthermore q divides p+1 and does not divide p.
4. Mathlib's lifting-the-exponent theorem gives
   v_q(p^q+1)=v_q(p+1)+1. The factorization gives the same valuation as
   v_q(p+1)+k. Thus k=1, contradicting N>q.
5. There is consequently an odd prime r dividing p^q+1 but not p+1. In ZMod r,
   p^q=-1 and p^2 is not 1. The order criterion gives orderOf(p)=2q, which the
   project's existing equivalence converts to the required primitive divisor.

This proves exactly the project's ZsigmondyInput. It does not claim the full
general Bang–Zsigmondy theorem. The four existing implication theorems then
give unconditional 8.3, 8.4, 8.5 and 9.3.

## GitHub proofs used

- [Lifting the exponent](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/NumberTheory/Multiplicity.lean): `padicValNat.pow_add_pow`.
- [Valuation products and prime powers](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/NumberTheory/Padics/PadicVal/Basic.lean).
- [Finite-order criterion](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/GroupTheory/OrderOfElement.lean): `orderOf_eq_of_pow_and_pow_div_prime`.

[Mathlib PR #28895](https://github.com/leanprover-community/mathlib4/pull/28895)
was also investigated, at commit a70e9b34ac7dda414253748552beedf5fc1a7c89.
Its general Zsigmondy proof requires a newer environment and polynomial
homogenization. The delivered proof instead uses the pinned mathlib and existing
project lemmas; it does not import that PR.
