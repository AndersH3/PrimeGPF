# PrimeAPInput proof development

This addition targets the exact `PrimeAPInput` already used by results 6.1 and 6.3.
It keeps Lean 4.19.0, the pinned mathlib revision, the theorem statements, and
the existing Counting and Density developments.

The validation workflow is `.github/workflows/pnt-proof.yml`. Until both its
build and axiom checks pass, this development must be treated as a draft.

## Proof structure

1. Apply the proved Wiener–Ikehara theorem with its Chebyshev hypothesis to
   von Mangoldt restricted to a reduced residue class. Nonnegativity and
   domination by the unrestricted function give summability and the Chebyshev
   bound. Mathlib supplies the analytic continuation at the line Re(s)=1.
2. Remove higher prime powers, comparing their contribution with the total
   unrestricted prime-power error.
3. Convert the resulting sum of log(p) to the ordinary prime count by splitting
   at N^delta, for 0<delta<1. The contribution of small integers is negligible;
   large integers satisfy log(n)>=delta*log(N). Letting delta approach 1 gives
   the desired count normalization.
4. Translate to `APAsymptotic` and instantiate both existing conditional proofs.

The resulting declarations are `proof_primeAP_dependency`, `proof_6_1`, and
`proof_6_3`. In particular, `proof_primeAP_dependency` must have type
`PrimeAPInput` without any additional theorem hypothesis.

## Verification

```bash
bash verify_prime_ap.sh
```

This runs Lean compilation and checks the transitive axiom lists of the
analytic input, the counting conversion, and both numbered results. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted. It writes raw
build and audit logs to `evidence/prime-ap-*`.

Successful compilation alone is insufficient: the axiom audit must also pass.
Coverage and default imports are updated only after these checks succeed.

## Sources

The retained Wiener–Ikehara development comes from
[PrimeNumberTheoremAnd, revision d3cea761](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/d3cea76119684a766d2cd195b05b137442205653).
That revision uses the same Lean and mathlib versions as this project.
Its later unfinished statements are excluded. See PNT_PROVENANCE.md and
THIRD_PARTY_LICENSE for attribution and the exact source modifications.

The residue-class analytic continuation is supplied by
[mathlib's PrimesInAP.lean](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/NumberTheory/LSeries/PrimesInAP.lean).
