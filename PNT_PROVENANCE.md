# Arithmetic-progression proof development

This is an experimental checkpoint. New modules are not yet compiler-verified.
Do not mark results 6.1 or 6.3 unconditional based on this checkpoint.

PrimeGPF/PNT contains portions of AlexKontorovich/PrimeNumberTheoremAnd at
d3cea76119684a766d2cd195b05b137442205653, licensed under Apache 2.0.
The license is included as THIRD_PARTY_LICENSE. Original copyright notices remain.
Imports were renamed from PrimeNumberTheoremAnd to PrimeGPF.PNT. Wiener.lean was
truncated before `section auto_cheby`, excluding all subsequent proof_wanted and
sorry declarations; Consequences.lean was truncated before chebyshev_asymptotic'.
Other retained upstream Lean files were not mathematically modified.

Project baseline: AndersH3/PrimeGPF commit 9c8eedf9be72f824185eefa27b9b86cde48898d5.
Core's broad Mathlib import was narrowed for the validation checkout only.
Lean 4.19.0; mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.

The new development consists of PrimeAPAnalytic.lean (Wiener–Ikehara applied to
von Mangoldt in a residue class, followed by removal of prime powers),
WeightedCounting.lean (log-weighted to ordinary counting conversion), and
PrimeAP.lean (exact project input and theorem wrappers).

Required validation: lake build PrimeGPF.PrimeAP, then #print axioms for the
new input and both theorem wrappers. No new assumptions may be introduced to
make those checks pass.
