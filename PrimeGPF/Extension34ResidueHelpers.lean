import PrimeGPF.Extension34Residues

/-!
# Extension 3 and 4 residue helper layer

This module is intentionally small. The goal is to separate elementary
congruence and positivity manipulations from the larger fiber-classification
proofs.

The later refactoring of the candidate-pair proofs will use these lemmas to
avoid repeating low-level `simp`, `norm_num`, and logarithm positivity blocks.
-/

namespace PrimeGPF

open PrimeGPF.Analytic

/-- If an exponent is odd, the power of five has residue two modulo three. -/
lemma five_pow_mod_three_odd (n : ℕ) (hn : n % 2 = 1) :
    5 ^ n % 3 = 2 := by
  simpa [Nat.pow_mod] using extension_two_pow_mod_three_of_odd hn

/-- The product of two numbers with residue one modulo two has residue one. -/
lemma odd_product_mod_two {a b : ℕ}
    (ha : a % 2 = 1) (hb : b % 2 = 1) :
    (a * b) % 2 = 1 := by
  simp [Nat.mul_mod, ha, hb]

/-- Positive logarithm facts used repeatedly by weighted-triangle arguments. -/
lemma log_three_pos : 0 < Real.log (3 : ℝ) := by
  exact Real.log_pos (by norm_num)

lemma log_five_pos : 0 < Real.log (5 : ℝ) := by
  exact Real.log_pos (by norm_num)

lemma log_two_pos : 0 < Real.log (2 : ℝ) := by
  exact Real.log_pos (by norm_num)

end PrimeGPF
