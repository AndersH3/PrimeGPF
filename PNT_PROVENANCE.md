# Provenance of the prime-AP proof

The new proof `PrimeGPF.proof_primeAP_dependency : PrimeAPInput` and results
6.1 and 6.3 compiled and passed the transitive axiom audit in
[run 34795580169](https://github.com/AndersH3/PrimeGPF/actions/runs/34795580169).

## Upstream source

Files under `PrimeGPF/PNT/` come from
[AlexKontorovich/PrimeNumberTheoremAnd at d3cea76119684a766d2cd195b05b137442205653](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/d3cea76119684a766d2cd195b05b137442205653).
That revision uses Lean 4.19.0 and mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b`, matching this project.

The source is licensed under Apache 2.0. Its license is retained as
`THIRD_PARTY_LICENSE`, together with the original source copyright notices.

Adaptations:

- Import paths change from `PrimeNumberTheoremAnd` to `PrimeGPF.PNT`.
- `Wiener.lean` ends before `section auto_cheby`, retaining the proved
  `WienerIkeharaTheorem'` with summability and Chebyshev hypotheses.
  Subsequent unfinished formulations and AP declarations are excluded.
- `Consequences.lean` ends before `chebyshev_asymptotic'`, retaining
  the earlier proved consequences needed for the prime-power comparison.
- The private `primeFactorsPiBij` helper family in
  `Mathlib/Data/Nat/FinMulAntidiagonal.lean` is renamed to
  `pntPrimeFactorsPiBij` to avoid generated-declaration collisions with
  mathlib's `Mathlib.Algebra.Order.Antidiag.Nat`. No proposition changes.

No unfinished upstream AP theorem is used to discharge the project input.

## Connecting proofs

`PrimeAPAnalytic.lean` applies Wiener–Ikehara to
`vonMangoldt.residueClass`. Nonnegativity and domination by unrestricted
von Mangoldt provide summability and the Chebyshev bound. Pinned mathlib's
`vonMangoldt.continuousOn_LFunctionResidueClassAux` and
`vonMangoldt.eqOn_LFunctionResidueClassAux` provide the analytic continuation
and pole calculation.

Changing from strict to inclusive sums contributes a negligible endpoint term.
The higher-prime-power error is bounded by the unrestricted error, whose
normalized limit is zero.

`WeightedCounting.lean` converts a positive limiting log-weighted sum divided
by N into the corresponding ordinary count times log(N)/N. The upper estimate
splits at N^δ, for 0 < δ < 1.

`PrimeAP.lean` identifies the project count, uses φ(r)=r−1 for prime r,
and produces the exact input and the two unconditional theorem wrappers.

## Integration and validation

Baseline: AndersH3/PrimeGPF `0a571c495625aa8d3f584a6342c47b0ec3bab906`.
The `codex/pnt-ap-lean419` work is combined with
`prove-prime-ap-input-20260913`, retaining both histories and the compiled
root-level experiments. The original broad Mathlib import in Core is preserved.

The root experimental `WienerIkeharaInput` remains an abstract research
interface; the completed proof does not assume it.

`verify_prime_ap.sh` compiles the new dependency and wrappers and permits
only `propext`, `Classical.choice`, and `Quot.sound` in their transitive
axiom dependencies. `verify.sh` also checks the whole library and the
conjunction `PrimeGPF.proof_all_39`.
