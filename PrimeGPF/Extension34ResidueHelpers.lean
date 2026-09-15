import PrimeGPF.Extension34Residues

/-!
# Extensions 3 and 4: elementary proof helpers

This module collects the small arithmetic and analytic facts that recur in the
Extension 3/4 classification and counting proofs.  Keeping them here has two
benefits:

* the structural proofs can focus on the mathematical reduction rather than
  repeated `simp`/`norm_num` bookkeeping;
* quotient reconstruction is proved once and reused whenever a classified
  exponent pair is converted back into a kernel factorisation.

No fiber classification or counting theorem belongs in this file.
-/

namespace PrimeGPF

/-- If an exponent is odd, the power of five has residue two modulo three.
This is the residue needed for the anchor-3 reconstruction formula. -/
lemma five_pow_mod_three_odd (n : ℕ) (hn : n % 2 = 1) :
    5 ^ n % 3 = 2 := by
  simpa [Nat.pow_mod] using extension_two_pow_mod_three_of_odd hn

/-- The product of two numbers that are both `1 mod 2` is again `1 mod 2`. -/
lemma odd_product_mod_two {a b : ℕ}
    (ha : a % 2 = 1) (hb : b % 2 = 1) :
    (a * b) % 2 = 1 := by
  simp [Nat.mul_mod, ha, hb]

/-- Reconstruct a kernel equation from an exact quotient formula.

If `d ∣ N - 1` and `q = (N - 1) / d`, then the natural-number quotient has no
rounding loss and therefore `d*q + 1 = N`.  This removes the same
`Nat.mul_div_cancel'`/`omega` block from several Extension 3/4 proofs. -/
lemma quotient_sub_one_reconstruct
    {d N q : ℕ} (hN : 1 ≤ N) (hdiv : d ∣ N - 1)
    (hq : q = (N - 1) / d) :
    d * q + 1 = N := by
  rw [hq]
  have hcancel : d * ((N - 1) / d) = N - 1 :=
    Nat.mul_div_cancel' hdiv
  omega

/-- Positive logarithm facts used repeatedly by weighted-triangle arguments. -/
lemma log_two_pos : 0 < Real.log (2 : ℝ) := by
  exact Real.log_pos (by norm_num)

lemma log_three_pos : 0 < Real.log (3 : ℝ) := by
  exact Real.log_pos (by norm_num)

lemma log_five_pos : 0 < Real.log (5 : ℝ) := by
  exact Real.log_pos (by norm_num)

end PrimeGPF
