# Coverage of the 39 source results

The project builds successfully under **Lean 4.19.0**. Proofs marked **compiler-verified** have been accepted by Lean and audited for forbidden proof shortcuts. The accepted axiom dependencies are limited to the usual foundational axioms `propext`, `Classical.choice`, and `Quot.sound` where needed.

| Result | Topic | Status | Proof / remaining dependency |
|---|---|---|---|
| 3.1 | Closure and divisibility | Full proof, compiler-verified | `proof_3_1`; Complete target is compiler-verified under Lean 4.19.0. |
| 3.2 | Commutativity | Full proof, compiler-verified | `proof_3_2`; Complete target is compiler-verified under Lean 4.19.0. |
| 3.3 | Nonassociativity | Full proof, compiler-verified | `proof_3_3`; Complete target is compiler-verified under Lean 4.19.0. |
| 3.4 | Anti-projection, idempotents, identities | Full proof, compiler-verified | `proof_3_4`; Complete target is compiler-verified under Lean 4.19.0. |
| 3.5 | Odd-prime closure | Full proof, compiler-verified | `proof_3_5`, `proof_3_5_from_8_1`; Direct exponential argument; no Zsigmondy input. Compiler-verified under Lean 4.19.0. |
| 3.6 | Cancellation and distributivity | Full proof, compiler-verified | `proof_3_6`; Complete target is compiler-verified under Lean 4.19.0. |
| 3.7 | Mixed associativity | Full proof, compiler-verified | `proof_3_7`; Complete target is compiler-verified under Lean 4.19.0. |
| 3.8 | Monotonicity | Full proof, compiler-verified | `proof_3_8`; Complete target is compiler-verified under Lean 4.19.0. |
| 4.1 | Exact fibers | Full proof, compiler-verified | `proof_4_1`; Complete target is compiler-verified under Lean 4.19.0. |
| 4.2 | Prime and two outputs | Full proof, compiler-verified | `proof_4_2`; Complete target is compiler-verified under Lean 4.19.0. |
| 4.3 | Small fibers | Full proof, compiler-verified | `proof_4_3`; Complete target is compiler-verified under Lean 4.19.0. |
| 5.1 | Modular inverses | Full proof, compiler-verified | `proof_5_1`; Complete target is compiler-verified under Lean 4.19.0. |
| 5.2 | Diagonal order and congruence | Full proof, compiler-verified | `proof_5_2`; Finite-field dyadic order and positive-order divisibility. Compiler-verified under Lean 4.19.0. |
| 5.3 | Diagonal orbits | Full proof, compiler-verified | `proof_5_3`, `proof_5_3_from_5_2`; Discharged using the new proof_5_2. Compiler-verified under Lean 4.19.0. |
| 5.4 | Legendre-symbol constraint | Full proof, compiler-verified | `proof_5_4`; Custom quadratic character identified with mathlib quadraticChar. Compiler-verified under Lean 4.19.0. |
| 5.5 | Dyadic cyclotomic forcing | False original; refutation verified | `counterexample_5_5`, `refutation_5_5`; Original remains false; separate proof_5_5_corrected supplies the complete corrected statement with r ≠ 2, uncompiled. |
| 5.6 | Parity split | Full proof, compiler-verified | `proof_5_6`; Complete target is compiler-verified under Lean 4.19.0. |
| 6.1 | Progressions and PNT-AP | Conditional proof, compiler-verified | `proof_6_1_from_PNT_AP`, `multiplicative_progression`, `additive_progression`, `additive_degenerate_progression`; All arithmetic and exact counting identities supplied; PrimeAPInput (PNT-AP limit) remains unproved. |
| 6.2 | Polylogarithmic fibers | Full proof, compiler-verified | `proof_6_2`, `proof_uniformPolylogFibers`, `proof_smoothPolylog`, `smoothCount_le_smoothBoxBound`, `fiberCount_add_le_smoothCount_sq`, `fiberCount_mul_le_smoothCount_sq`; Complete unconditional proof. Includes the explicit smooth-number box bound, smooth polylogarithmic estimate, and uniform additive and multiplicative fiber bounds. Compiler-verified under Lean 4.19.0. |
| 6.3 | Zero density | Statement only | —; Statement only; limits and uniform pair bound remain. |
| 6.4 | Unbounded sections | Full proof, compiler-verified | `proof_6_4`; All three clauses, using mathlib Dirichlet primes in residue classes. Compiler-verified under Lean 4.19.0. |
| 7.1 | Additive fixed points | Full proof, compiler-verified | `proof_7_1`; Complete target is compiler-verified under Lean 4.19.0. |
| 7.2 | Multiplicative fixed points | Full proof, compiler-verified | `proof_7_2`; Complete target is compiler-verified under Lean 4.19.0. |
| 7.3 | Anchor-two additive dynamics | Full proof, compiler-verified | `proof_7_3`; Complete target is compiler-verified under Lean 4.19.0. |
| 7.4 | Dual self-output | Full proof, compiler-verified | `proof_7_4`; Complete target is compiler-verified under Lean 4.19.0. |
| 7.5 | Finite-state periodicity | Full proof, compiler-verified | `proof_7_5`; Complete target is compiler-verified under Lean 4.19.0. |
| 8.1 | No output two | Full proof, compiler-verified | `proof_8_1`, `proof_8_1_from_8_3`; Direct odd-cofactor argument, independently of primitive divisors. Compiler-verified under Lean 4.19.0. |
| 8.2 | Exponent-two congruence | Full proof, compiler-verified | `proof_8_2`, `proof_8_2_from_5_2`; Discharged using the new diagonal congruence. Compiler-verified under Lean 4.19.0. |
| 8.3 | Zsigmondy lower bound | Conditional proof, compiler-verified | `proof_8_3_from_zsigmondy`, `proof_8_3_from_external`; Only ZsigmondyInput remains an explicit unproved input to this new wrapper. Positive-order divisibility and 8.1 have proof scripts. Wrapper compiler-verified under Lean 4.19.0. |
| 8.4 | Near anti-projection | Conditional proof, compiler-verified | `proof_8_4_from_zsigmondy`, `proof_8_4_from_bounds`; Only ZsigmondyInput remains an explicit unproved input to this new wrapper. Positive-order divisibility and 8.1 have proof scripts. Wrapper compiler-verified under Lean 4.19.0. |
| 8.5 | Exponential dynamics | Conditional proof, compiler-verified | `proof_8_5_from_zsigmondy`, `proof_8_5_from_bounds`; Only ZsigmondyInput remains an explicit unproved input to this new wrapper. Positive-order divisibility and 8.1 have proof scripts. Wrapper compiler-verified under Lean 4.19.0. |
| 9.1 | Bridge identities | Full proof, compiler-verified | `proof_9_1`; Complete target is compiler-verified under Lean 4.19.0. |
| 9.2 | Second-column rigidity | Full proof, compiler-verified | `proof_9_2`; Complete target is compiler-verified under Lean 4.19.0. |
| 9.3 | Exponential dominance | Conditional proof, compiler-verified | `proof_9_3_from_zsigmondy`, `proof_9_3_from_8_3`; Only ZsigmondyInput remains an explicit unproved input to this new wrapper. Positive-order divisibility and 8.1 have proof scripts. Wrapper compiler-verified under Lean 4.19.0. |
| 9.4 | Collision compatibility | Full proof, compiler-verified | `proof_9_4`; Complete target is compiler-verified under Lean 4.19.0. |
| 9.5 | Finite common outputs | Full proof, compiler-verified | `proof_9_5`; Complete target is compiler-verified under Lean 4.19.0. |
| 9.6 | Quadratic-residue restriction | Full proof, compiler-verified | `proof_9_6`, `collision_two_polynomials`; Explicit discriminant square and quadratic reciprocity at five. Compiler-verified under Lean 4.19.0. |
| 9.7 | Multiplicative-exponential obstruction | Full proof, compiler-verified | `proof_9_7`; Complete target is compiler-verified under Lean 4.19.0. |
| 9.8 | Triple obstruction | Full proof, compiler-verified | `proof_9_8`, `proof_9_8_from_9_6_9_7`; Discharged using the new proof_9_6 and existing proof_9_7. Compiler-verified under Lean 4.19.0. |

Counts: **32 complete compiler-verified proofs, 5 compiler-verified conditional proofs, 1 statement-only result, 1 false original statement.**

The corrected 5.5 is an additional compiler-verified theorem outside the 39-result count.

## Remaining mathematical obligations

- **6.1:** `PrimeAPInput`, the stated PNT-in-arithmetic-progressions ratio limit.
- **6.3:** relative-density and pair-density limits.
- **8.3:** `ZsigmondyInput`; consequently 8.4, 8.5, and 9.3 remain conditional.
- **Original 5.5:** false as stated; retained together with its verified counterexample and refutation.

Thus, excluding the known-false original 5.5, six original results still lack unconditional proofs.
