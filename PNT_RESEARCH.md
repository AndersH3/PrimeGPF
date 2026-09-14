> Historical note: the proposed route below is now completed and compiler-verified. See [README_PRIME_AP.md](README_PRIME_AP.md). The incomplete-status statements below describe the earlier research checkpoint.

# Remaining dependency: PrimeAPInput

Status: NOT PROVED by this patch. Results 6.1 and 6.3 remain conditional.

An especially useful version-compatible research source is
[PrimeNumberTheoremAnd at d3cea76119684a766d2cd195b05b137442205653](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/d3cea76119684a766d2cd195b05b137442205653).
Its toolchain is Lean 4.19.0 and its mathlib manifest matches c44e0c8.

Its Wiener.lean contains a proved `WienerIkeharaTheorem'` with a Chebyshev bound
hypothesis, and `vonMangoldt_cheby`. However, later alternate formulations and
the AP theorem contain placeholders at that revision. Importing those unproved
statements would not discharge the project's input.

A potential route is to retain only the proved Wiener–Ikehara development and
combine it with the pinned mathlib's existing
`vonMangoldt.continuousOn_LFunctionResidueClassAux` and
`vonMangoldt.eqOn_LFunctionResidueClassAux`.
Nonnegativity and domination by the unrestricted von Mangoldt function supply
the required summability and Chebyshev hypotheses for each reduced residue class.

The further steps are:

1. Obtain the von Mangoldt sum in a reduced residue class divided by N tending
   to 1/phi(q).
2. Remove the nonprime prime powers by comparison with the unrestricted error.
3. Convert the log-weighted prime sum to the unweighted AP count. One elementary
   approach splits at N^delta for fixed 0<delta<1. The small part contributes
   at most (N^delta+1)log(N)/N; the large part is bounded using
   log(n)>=delta*log(N). Then let delta approach 1.
4. Translate the resulting count normalization to the project's exact
   APAsymptotic and PrimeAPInput definitions.

An adaptation was drafted but did not reach compiler verification before the
workspace refresh removed the experimental files and runtime. None of these
steps is reported as a completed Lean theorem here. The approximately 5,000-line
supporting PNT development also requires a transitive axiom audit before use.

The unpublished local Density.lean should be preserved when integrating the
finished input. No change to theorem statements or counting conventions is needed.
