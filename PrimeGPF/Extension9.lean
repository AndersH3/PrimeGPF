import PrimeGPF.Extension9Revised

/-!
# Extension 9: triple collisions with second input 2

The proof is developed modularly in `PrimeGPF.Extension9Revised`. This file
keeps the original public theorem name used by the report and downstream code.
-/
namespace PrimeGPF

/-- Complete classification of triple collisions with second input `2`:
`add p 2 = mul p 2 = exp p 2` exactly for `p = 2` or `p = 7`. -/
theorem extension9_triple_second_two {p : ℕ} (hp : Nat.Prime p) :
    (add p 2 = mul p 2 ∧ add p 2 = exp p 2) ↔ p = 2 ∨ p = 7 :=
  extension9_triple_second_two_revised hp

end PrimeGPF
