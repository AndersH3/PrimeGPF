# Coverage of the 39 source results

**No Lean proof in this package has been compiler-verified.** Full script means a proof body with no admissions has been supplied; it does not certify elaboration or tactic success.

| Result | Topic | Development status | Proof / remaining dependency |
|---|---|---|---|
| 3.1 | Closure and divisibility | Full script, uncompiled | `proof_3_1`; Complete target has a proof script; no compiler acceptance claimed. |
| 3.2 | Commutativity | Full script, uncompiled | `proof_3_2`; Complete target has a proof script; no compiler acceptance claimed. |
| 3.3 | Nonassociativity | Full script, uncompiled | `proof_3_3`; Complete target has a proof script; no compiler acceptance claimed. |
| 3.4 | Anti-projection, idempotents, identities | Full script, uncompiled | `proof_3_4`; Complete target has a proof script; no compiler acceptance claimed. |
| 3.5 | Odd-prime closure | Full script, uncompiled | `proof_3_5`, `proof_3_5_from_8_1`; Direct exponential argument; no Zsigmondy input. New script; NOT compiler-verified. |
| 3.6 | Cancellation and distributivity | Full script, uncompiled | `proof_3_6`; Complete target has a proof script; no compiler acceptance claimed. |
| 3.7 | Mixed associativity | Full script, uncompiled | `proof_3_7`; Complete target has a proof script; no compiler acceptance claimed. |
| 3.8 | Monotonicity | Full script, uncompiled | `proof_3_8`; Complete target has a proof script; no compiler acceptance claimed. |
| 4.1 | Exact fibers | Full script, uncompiled | `proof_4_1`; Complete target has a proof script; no compiler acceptance claimed. |
| 4.2 | Prime and two outputs | Full script, uncompiled | `proof_4_2`; Complete target has a proof script; no compiler acceptance claimed. |
| 4.3 | Small fibers | Full script, uncompiled | `proof_4_3`; Complete target has a proof script; no compiler acceptance claimed. |
| 5.1 | Modular inverses | Full script, uncompiled | `proof_5_1`; Complete target has a proof script; no compiler acceptance claimed. |
| 5.2 | Diagonal order and congruence | Full script, uncompiled | `proof_5_2`; Finite-field dyadic order and positive-order divisibility. New script; NOT compiler-verified. |
| 5.3 | Diagonal orbits | Full script, uncompiled | `proof_5_3`, `proof_5_3_from_5_2`; Discharged using the new proof_5_2. New script; NOT compiler-verified. |
| 5.4 | Legendre-symbol constraint | Full script, uncompiled | `proof_5_4`; Custom quadratic character identified with mathlib quadraticChar. New script; NOT compiler-verified. |
| 5.5 | Dyadic cyclotomic forcing | False original | `counterexample_5_5`, `refutation_5_5`; Original remains false; separate proof_5_5_corrected supplies the complete corrected statement with r ≠ 2, uncompiled. |
| 5.6 | Parity split | Full script, uncompiled | `proof_5_6`; Complete target has a proof script; no compiler acceptance claimed. |
| 6.1 | Progressions and PNT-AP | Conditional script, uncompiled | `proof_6_1_from_PNT_AP`, `multiplicative_progression`, `additive_progression`, `additive_degenerate_progression`; All arithmetic and exact counting identities supplied; PrimeAPInput (PNT-AP limit) remains unproved. |
| 6.2 | Polylogarithmic fibers | Statement only | ; Statement only; exponent-vector counting and uniform asymptotic bound remain. |
| 6.3 | Zero density | Statement only | ; Statement only; limits and uniform pair bound remain. |
| 6.4 | Unbounded sections | Full script, uncompiled | `proof_6_4`; All three clauses, using mathlib Dirichlet primes in residue classes. New script; NOT compiler-verified. |
| 7.1 | Additive fixed points | Full script, uncompiled | `proof_7_1`; Complete target has a proof script; no compiler acceptance claimed. |
| 7.2 | Multiplicative fixed points | Full script, uncompiled | `proof_7_2`; Complete target has a proof script; no compiler acceptance claimed. |
| 7.3 | Anchor-two additive dynamics | Full script, uncompiled | `proof_7_3`; Complete target has a proof script; no compiler acceptance claimed. |
| 7.4 | Dual self-output | Full script, uncompiled | `proof_7_4`; Complete target has a proof script; no compiler acceptance claimed. |
| 7.5 | Finite-state periodicity | Full script, uncompiled | `proof_7_5`; Complete target has a proof script; no compiler acceptance claimed. |
| 8.1 | No output two | Full script, uncompiled | `proof_8_1`, `proof_8_1_from_8_3`; Direct odd-cofactor argument, independently of primitive divisors. New script; NOT compiler-verified. |
| 8.2 | Exponent-two congruence | Full script, uncompiled | `proof_8_2`, `proof_8_2_from_5_2`; Discharged using the new diagonal congruence. New script; NOT compiler-verified. |
| 8.3 | Zsigmondy lower bound | Conditional script, uncompiled | `proof_8_3_from_zsigmondy`, `proof_8_3_from_external`; Only ZsigmondyInput remains an explicit unproved input to this new wrapper. Positive-order divisibility and 8.1 have proof scripts. NOT compiler-verified. |
| 8.4 | Near anti-projection | Conditional script, uncompiled | `proof_8_4_from_zsigmondy`, `proof_8_4_from_bounds`; Only ZsigmondyInput remains an explicit unproved input to this new wrapper. Positive-order divisibility and 8.1 have proof scripts. NOT compiler-verified. |
| 8.5 | Exponential dynamics | Conditional script, uncompiled | `proof_8_5_from_zsigmondy`, `proof_8_5_from_bounds`; Only ZsigmondyInput remains an explicit unproved input to this new wrapper. Positive-order divisibility and 8.1 have proof scripts. NOT compiler-verified. |
| 9.1 | Bridge identities | Full script, uncompiled | `proof_9_1`; Complete target has a proof script; no compiler acceptance claimed. |
| 9.2 | Second-column rigidity | Full script, uncompiled | `proof_9_2`; Complete target has a proof script; no compiler acceptance claimed. |
| 9.3 | Exponential dominance | Conditional script, uncompiled | `proof_9_3_from_zsigmondy`, `proof_9_3_from_8_3`; Only ZsigmondyInput remains an explicit unproved input to this new wrapper. Positive-order divisibility and 8.1 have proof scripts. NOT compiler-verified. |
| 9.4 | Collision compatibility | Full script, uncompiled | `proof_9_4`; Complete target has a proof script; no compiler acceptance claimed. |
| 9.5 | Finite common outputs | Full script, uncompiled | `proof_9_5`; Complete target has a proof script; no compiler acceptance claimed. |
| 9.6 | Quadratic-residue restriction | Full script, uncompiled | `proof_9_6`, `collision_two_polynomials`; Explicit discriminant square and quadratic reciprocity at five. New script; NOT compiler-verified. |
| 9.7 | Multiplicative-exponential obstruction | Full script, uncompiled | `proof_9_7`; Complete target has a proof script; no compiler acceptance claimed. |
| 9.8 | Triple obstruction | Full script, uncompiled | `proof_9_8`, `proof_9_8_from_9_6_9_7`; Discharged using the new proof_9_6 and existing proof_9_7. New script; NOT compiler-verified. |

Counts: **31 full scripts, five conditional scripts, two statement-only results, one false original.** The corrected 5.5 is an additional full script outside the count of 39.

New full scripts: 3.5, 5.2, 5.3, 5.4, 6.4, 8.1, 8.2, 9.6, 9.8; additionally corrected 5.5.

Remaining mathematical inputs:

- `ZsigmondyInput`: primitive-divisor existence for 8.3, hence 8.4, 8.5 and 9.3.
- `PrimeAPInput`: the ratio-limit form of the prime number theorem in arithmetic progressions for 6.1.
- 6.2: smooth-number box counting and uniform polylogarithmic estimates.
- 6.3: relative and pair-density limits.
- Original 5.5: false and retained with its counterexample.

The old unrestricted order dependency was also false because `PrimitiveDivisor r p 0` is permitted. `OrderDividesPrimePredOriginal` preserves that statement and `refutation_order_dependency` refutes it. The repaired `OrderDividesPrimePred` requires a positive exponent.
