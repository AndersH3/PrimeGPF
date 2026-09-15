import PrimeGPF.Extension34Residues

/-!
# Extension 3 and 4 residue helper layer

This module is intentionally small.  The goal is to separate elementary
congruence manipulations from the larger fiber-classification proofs.

Future refactors can replace repeated `Nat.pow_mod` calculations with these
lemmas without changing the mathematical structure of the proofs.
-/

namespace PrimeGPF

/-- If an exponent is odd, the power of five has residue two modulo three. -/
lemma five_pow_mod_three_odd (n : ℕ) (hn : n % 2 = 1) :
    5 ^ n % 3 = 2 := by
  simpa [Nat.pow_mod] using extension_two_pow_mod_three_of_odd hn

/-- The product of two numbers with residue one modulo two has residue one. -/
lemma odd_product_mod_two {a b : ℕ}
    (ha : a % 2 = 1) (hb : b % 2 = 1) :
    (a * b) % 2 = 1 := by
  simp [Nat.mul_mod, ha, hb]

end PrimeGPF
