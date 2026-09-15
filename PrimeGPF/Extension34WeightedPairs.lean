import PrimeGPF.Extension34Exact
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Extensions 3 and 4: weighted exponent triangles

The exact output-5 classifications reduce the remaining counting problem to
lattice points in two weighted triangles.  This file formalizes that
arithmetic-to-geometric reduction independently of the later floor-sum and
Möbius arguments.
-/
namespace PrimeGPF

/-- An anchor-2 exponent representation below input cutoff `X` lies in the
weighted triangle `α log 3 + β log 5 ≤ log(2X+1)`. -/
theorem extension3_exponents_weighted_le
    {q X α β : ℕ}
    (hfac : 2 * q + 1 = 3 ^ α * 5 ^ β)
    (hqX : q ≤ X) :
    (α : ℝ) * Real.log 3 + (β : ℝ) * Real.log 5 ≤
      Real.log ((2 * X + 1 : ℕ) : ℝ) := by
  have hprodNat : 3 ^ α * 5 ^ β ≤ 2 * X + 1 := by
    rw [← hfac]
    omega
  have hprod :
      ((3 ^ α * 5 ^ β : ℕ) : ℝ) ≤ ((2 * X + 1 : ℕ) : ℝ) := by
    exact_mod_cast hprodNat
  have hlog :
      Real.log (((3 ^ α * 5 ^ β : ℕ) : ℝ)) ≤
        Real.log ((2 * X + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) hprod
  calc
    (α : ℝ) * Real.log 3 + (β : ℝ) * Real.log 5 =
        Real.log (((3 ^ α * 5 ^ β : ℕ) : ℝ)) := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]
      norm_num
    _ ≤ Real.log ((2 * X + 1 : ℕ) : ℝ) := hlog

/-- Every nonexceptional anchor-2 output-5 fiber input gives a positive,
primitive exponent pair in the weighted triangle. -/
theorem extension3_fiber_gives_weighted_pair
    {q X : ℕ} (hq : Nat.Prime q) (hout : mul 2 q = 5)
    (hq2 : q ≠ 2) (hqX : q ≤ X) :
    ∃ α β : ℕ,
      0 < α ∧ 0 < β ∧ α % 2 = 1 ∧ Nat.Coprime α β ∧
      (α : ℝ) * Real.log 3 + (β : ℝ) * Real.log 5 ≤
        Real.log ((2 * X + 1 : ℕ) : ℝ) := by
  obtain ⟨α, β, hα, hβ, hodd, hcop, hqform⟩ :=
    (extension3_exact_classification hq).mp hout |>.resolve_left hq2
  let N := 3 ^ α * 5 ^ β
  have hNmod : N % 2 = 1 := by
    dsimp [N]
    simp [Nat.mul_mod]
  have hdec := Nat.mod_add_div N 2
  have hsub : N - 1 = 2 * (N / 2) := by omega
  have hdiv : 2 ∣ N - 1 := by
    rw [hsub]
    exact dvd_mul_right 2 (N / 2)
  have hqmul : q * 2 = N - 1 := by
    rw [hqform]
    exact Nat.div_mul_cancel hdiv
  have hqpos : 0 < q := hq.pos
  have hfac : 2 * q + 1 = 3 ^ α * 5 ^ β := by
    dsimp [N] at hqmul ⊢
    omega
  exact ⟨α, β, hα, hβ, hodd, hcop,
    extension3_exponents_weighted_le hfac hqX⟩

/-- An anchor-3 exponent representation below input cutoff `X` lies in the
weighted triangle `α log 2 + β log 5 ≤ log(3X+1)`. -/
theorem extension4_exponents_weighted_le
    {q X α β : ℕ}
    (hfac : 3 * q + 1 = 2 ^ α * 5 ^ β)
    (hqX : q ≤ X) :
    (α : ℝ) * Real.log 2 + (β : ℝ) * Real.log 5 ≤
      Real.log ((3 * X + 1 : ℕ) : ℝ) := by
  have hprodNat : 2 ^ α * 5 ^ β ≤ 3 * X + 1 := by
    rw [← hfac]
    omega
  have hprod :
      ((2 ^ α * 5 ^ β : ℕ) : ℝ) ≤ ((3 * X + 1 : ℕ) : ℝ) := by
    exact_mod_cast hprodNat
  have hlog :
      Real.log (((2 ^ α * 5 ^ β : ℕ) : ℝ)) ≤
        Real.log ((3 * X + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) hprod
  calc
    (α : ℝ) * Real.log 2 + (β : ℝ) * Real.log 5 =
        Real.log (((2 ^ α * 5 ^ β : ℕ) : ℝ)) := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]
      norm_num
    _ ≤ Real.log ((3 * X + 1 : ℕ) : ℝ) := hlog

/-- Every anchor-3 output-5 fiber input gives a positive primitive odd-odd
exponent pair in the weighted triangle. -/
theorem extension4_fiber_gives_weighted_pair
    {q X : ℕ} (hq : Nat.Prime q) (hout : mul 3 q = 5)
    (hqX : q ≤ X) :
    ∃ α β : ℕ,
      0 < α ∧ 0 < β ∧ α % 2 = 1 ∧ β % 2 = 1 ∧
      Nat.Coprime α β ∧
      (α : ℝ) * Real.log 2 + (β : ℝ) * Real.log 5 ≤
        Real.log ((3 * X + 1 : ℕ) : ℝ) := by
  obtain ⟨α, β, hα, hβ, hαodd, hβodd, hcop, hqform⟩ :=
    (extension4_exact_classification hq).mp hout
  let N := 2 ^ α * 5 ^ β
  have h2 : 2 ^ α % 3 = 2 := extension_two_pow_mod_three_of_odd hαodd
  have h5 : 5 ^ β % 3 = 2 := by
    simpa [Nat.pow_mod] using extension_two_pow_mod_three_of_odd hβodd
  have hNmod : N % 3 = 1 := by
    dsimp [N]
    norm_num [Nat.mul_mod, h2, h5]
  have hdec := Nat.mod_add_div N 3
  have hsub : N - 1 = 3 * (N / 3) := by omega
  have hdiv : 3 ∣ N - 1 := by
    rw [hsub]
    exact dvd_mul_right 3 (N / 3)
  have hqmul : q * 3 = N - 1 := by
    rw [hqform]
    exact Nat.div_mul_cancel hdiv
  have hqpos : 0 < q := hq.pos
  have hfac : 3 * q + 1 = 2 ^ α * 5 ^ β := by
    dsimp [N] at hqmul ⊢
    omega
  exact ⟨α, β, hα, hβ, hαodd, hβodd, hcop,
    extension4_exponents_weighted_le hfac hqX⟩

end PrimeGPF