# Coverage of the 39 corrected results

All 39 numbered results now have unconditional Lean 4.19.0 proofs. Results 6.1 and 6.3 and their shared `PrimeAPInput` passed the [build and transitive axiom audit](https://github.com/AndersH3/PrimeGPF/actions/runs/34795580169). Allowed axioms are `propext`, `Classical.choice`, and `Quot.sound` only.

The numbered theorem 5.5 is the previously corrected statement with `r ≠ 2`. The original false statement and its refutation remain separately available.

| Result | Topic | Proof | Status |
|---|---|---|---|
| 3.1 | Closure and divisibility | `proof_3_1` | Unconditional, compiler-verified |
| 3.2 | Commutativity | `proof_3_2` | Unconditional, compiler-verified |
| 3.3 | Nonassociativity | `proof_3_3` | Unconditional, compiler-verified |
| 3.4 | Anti-projection, idempotents, identities | `proof_3_4` | Unconditional, compiler-verified |
| 3.5 | Odd-prime closure | `proof_3_5` | Unconditional, compiler-verified |
| 3.6 | Cancellation and distributivity | `proof_3_6` | Unconditional, compiler-verified |
| 3.7 | Mixed associativity | `proof_3_7` | Unconditional, compiler-verified |
| 3.8 | Monotonicity | `proof_3_8` | Unconditional, compiler-verified |
| 4.1 | Exact fibers | `proof_4_1` | Unconditional, compiler-verified |
| 4.2 | Prime and two outputs | `proof_4_2` | Unconditional, compiler-verified |
| 4.3 | Small fibers | `proof_4_3` | Unconditional, compiler-verified |
| 5.1 | Modular inverses | `proof_5_1` | Unconditional, compiler-verified |
| 5.2 | Diagonal order and congruence | `proof_5_2` | Unconditional, compiler-verified |
| 5.3 | Diagonal orbits | `proof_5_3` | Unconditional, compiler-verified |
| 5.4 | Legendre-symbol constraint | `proof_5_4` | Unconditional, compiler-verified |
| 5.5 | Dyadic cyclotomic forcing | `proof_5_5` | Unconditional, compiler-verified |
| 5.6 | Parity split | `proof_5_6` | Unconditional, compiler-verified |
| 6.1 | Progressions and PNT-AP | `proof_6_1` | Unconditional, compiler-verified |
| 6.2 | Polylogarithmic fibers | `proof_6_2` | Unconditional, compiler-verified |
| 6.3 | Zero density | `proof_6_3` | Unconditional, compiler-verified |
| 6.4 | Unbounded sections | `proof_6_4` | Unconditional, compiler-verified |
| 7.1 | Additive fixed points | `proof_7_1` | Unconditional, compiler-verified |
| 7.2 | Multiplicative fixed points | `proof_7_2` | Unconditional, compiler-verified |
| 7.3 | Anchor-two additive dynamics | `proof_7_3` | Unconditional, compiler-verified |
| 7.4 | Dual self-output | `proof_7_4` | Unconditional, compiler-verified |
| 7.5 | Finite-state periodicity | `proof_7_5` | Unconditional, compiler-verified |
| 8.1 | No output two | `proof_8_1` | Unconditional, compiler-verified |
| 8.2 | Exponent-two congruence | `proof_8_2` | Unconditional, compiler-verified |
| 8.3 | Zsigmondy lower bound | `proof_8_3` | Unconditional, compiler-verified |
| 8.4 | Near anti-projection | `proof_8_4` | Unconditional, compiler-verified |
| 8.5 | Exponential dynamics | `proof_8_5` | Unconditional, compiler-verified |
| 9.1 | Bridge identities | `proof_9_1` | Unconditional, compiler-verified |
| 9.2 | Second-column rigidity | `proof_9_2` | Unconditional, compiler-verified |
| 9.3 | Exponential dominance | `proof_9_3` | Unconditional, compiler-verified |
| 9.4 | Collision compatibility | `proof_9_4` | Unconditional, compiler-verified |
| 9.5 | Finite common outputs | `proof_9_5` | Unconditional, compiler-verified |
| 9.6 | Quadratic-residue restriction | `proof_9_6` | Unconditional, compiler-verified |
| 9.7 | Multiplicative-exponential obstruction | `proof_9_7` | Unconditional, compiler-verified |
| 9.8 | Triple obstruction | `proof_9_8` | Unconditional, compiler-verified |

`PrimeGPF.proof_all_39` combines the 39 corrected statements. Run `bash verify.sh` to build and audit the full conjunction. `coverage.json` lists additional helper declarations and retained conditional interfaces.
