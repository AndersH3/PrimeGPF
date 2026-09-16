import PrimeGPF.Extension34ParityCounting

/-!
# Extensions 3 and 4: setup for the odd-divisor Möbius count

After the parity reduction, the only missing leading-constant improvement in
Extensions 3 and 4 is coprimality.  Because every relevant exponent is odd,
any common divisor of the exponents is itself odd.  This is why the report's
Möbius factor is a sum over odd divisors rather than over all positive
integers.

This file records the elementary facts needed before introducing Möbius
inversion itself:

* a divisor of an odd natural number is odd;
* a common divisor of the relevant exponent pair is therefore odd;
* dividing both exponents by a common divisor scales the weighted logarithmic
  sum by exactly that divisor;
* consequently a point with common divisor `g` reduces to a weighted triangle
  with cutoff divided by `g`.

Keeping these facts independent of the Möbius API makes the later analytic
step both shorter and easier to audit.
-/
namespace PrimeGPF

/-- Every positive divisor of an odd natural number is odd.  The positivity
assumption excludes the degenerate divisor `0`. -/
lemma mod_two_eq_one_of_dvd_mod_two_eq_one
    {d n : ℕ} (_hd : 0 < d) (hdn : d ∣ n) (hn : n % 2 = 1) :
    d % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one d with hdeven | hdodd
  · have h2d : 2 ∣ d := Nat.dvd_of_mod_eq_zero hdeven
    have h2n : 2 ∣ n := dvd_trans h2d hdn
    have hnzero := Nat.mod_eq_zero_of_dvd h2n
    omega
  · exact hdodd

/-- Any positive common divisor of two odd exponents is odd.  This is the
parity fact behind the odd-only Möbius sum in equations (4) and (6). -/
lemma common_divisor_of_odd_exponents_is_odd
    {d α β : ℕ} (hd : 0 < d) (hdα : d ∣ α) (_hdβ : d ∣ β)
    (hαodd : α % 2 = 1) (_hβodd : β % 2 = 1) :
    d % 2 = 1 :=
  mod_two_eq_one_of_dvd_mod_two_eq_one hd hdα hαodd

/-- Dividing both exponents by a common divisor and then multiplying back by
that divisor recovers the original weighted logarithmic sum exactly. -/
lemma weighted_sum_factor_common_divisor
    {d α β : ℕ} (hdα : d ∣ α) (hdβ : d ∣ β) (u v : ℝ) :
    (α : ℝ) * u + (β : ℝ) * v =
      (d : ℝ) *
        ((((α / d : ℕ) : ℝ) * u) + (((β / d : ℕ) : ℝ) * v)) := by
  have hαformNat : α = d * (α / d) :=
    (Nat.mul_div_cancel' hdα).symm
  have hβformNat : β = d * (β / d) :=
    (Nat.mul_div_cancel' hdβ).symm
  have hαform :
      (α : ℝ) = (d : ℝ) * ((α / d : ℕ) : ℝ) := by
    exact_mod_cast hαformNat
  have hβform :
      (β : ℝ) = (d : ℝ) * ((β / d : ℕ) : ℝ) := by
    exact_mod_cast hβformNat
  rw [hαform, hβform]
  ring

/-- A weighted exponent pair whose coordinates share a positive divisor `d`
reduces to the same weighted triangle with cutoff divided by `d`. -/
lemma weighted_sum_div_common_divisor_le
    {d α β : ℕ} {u v L : ℝ}
    (hd : 0 < d) (hdα : d ∣ α) (hdβ : d ∣ β)
    (hweighted : (α : ℝ) * u + (β : ℝ) * v ≤ L) :
    (((α / d : ℕ) : ℝ) * u) + (((β / d : ℕ) : ℝ) * v) ≤ L / d := by
  have hfactor := weighted_sum_factor_common_divisor hdα hdβ u v
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [hfactor] at hweighted
  apply (le_div_iff₀ hdR).2
  calc
    ((((α / d : ℕ) : ℝ) * u) + (((β / d : ℕ) : ℝ) * v)) * (d : ℝ) =
        (d : ℝ) *
          ((((α / d : ℕ) : ℝ) * u) + (((β / d : ℕ) : ℝ) * v)) := by
      ring
    _ ≤ L := hweighted

/-- In the Extension-3 classification, every positive common divisor of the
exponents is odd. -/
lemma extension3_common_divisor_is_odd
    {d α β : ℕ} (hd : 0 < d) (hdα : d ∣ α) (_hdβ : d ∣ β)
    (hαodd : α % 2 = 1) :
    d % 2 = 1 := by
  exact mod_two_eq_one_of_dvd_mod_two_eq_one hd hdα hαodd

/-- In the Extension-4 classification, where both exponents are odd, every
positive common divisor is likewise odd. -/
lemma extension4_common_divisor_is_odd
    {d α β : ℕ} (hd : 0 < d) (hdα : d ∣ α) (hdβ : d ∣ β)
    (hαodd : α % 2 = 1) (hβodd : β % 2 = 1) :
    d % 2 = 1 := by
  exact common_divisor_of_odd_exponents_is_odd
    hd hdα hdβ hαodd hβodd

end PrimeGPF
