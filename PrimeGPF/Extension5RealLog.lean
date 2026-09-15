import PrimeGPF.Extensions
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Extension 5: report-shaped base-two logarithmic visit bound

`Extensions.lean` proves the discrete form of equation (8) using `Nat.log 2`.
This file gives the same statement with the literal real base-two logarithm and
natural floor appearing in the report.
-/
namespace PrimeGPF

/-- Report-shaped index form of equation (8): if the `n`-th nonexceptional
iterate is at most `X`, then `n` is bounded by the floor of the real base-two
logarithm of `(X+1)/(q+1)`. -/
theorem extension5_index_real_logb_bound
    {a q X n : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q)
    (h0 : (a, q) ≠ (2, 3)) (hX : expIterNat a q n ≤ X) :
    n ≤ ⌊Real.logb (2 : ℝ)
      (((X + 1 : ℕ) : ℝ) / ((q + 1 : ℕ) : ℝ))⌋₊ := by
  have hprod : 2 ^ n * (q + 1) ≤ X + 1 :=
    le_trans (extension5_exponential_escape ha hq h0 n) (by omega)
  have hqpos : 0 < ((q + 1 : ℕ) : ℝ) := by positivity
  have hprodR :
      (2 : ℝ) ^ n * ((q + 1 : ℕ) : ℝ) ≤ ((X + 1 : ℕ) : ℝ) := by
    exact_mod_cast hprod
  have hpowR :
      (2 : ℝ) ^ n ≤
        ((X + 1 : ℕ) : ℝ) / ((q + 1 : ℕ) : ℝ) :=
    (le_div_iff₀ hqpos).2 hprodR
  have hlog :
      Real.logb (2 : ℝ) ((2 : ℝ) ^ n) ≤
        Real.logb (2 : ℝ)
          (((X + 1 : ℕ) : ℝ) / ((q + 1 : ℕ) : ℝ)) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) hpowR
  have hlogb2 : Real.logb (2 : ℝ) (2 : ℝ) = 1 :=
    Real.logb_self_eq_one (by norm_num)
  rw [Real.logb_pow, hlogb2] at hlog
  simp only [mul_one] at hlog
  exact Nat.le_floor hlog

/-- The finite set of visit indices cut off using the literal real logarithm
from equation (8). -/
noncomputable def expVisitIndicesRealLogb (a q X : ℕ) : Finset ℕ := by
  classical
  exact
    (Finset.range
      (⌊Real.logb (2 : ℝ)
          (((X + 1 : ℕ) : ℝ) / ((q + 1 : ℕ) : ℝ))⌋₊ + 1)).filter
      (fun n => expIterNat a q n ≤ X)

/-- Equation (8) in the report's literal floor/logarithm notation. -/
theorem extension5_visit_count_real_logb
    {a q X : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q)
    (h0 : (a, q) ≠ (2, 3)) :
    (∀ n, expIterNat a q n ≤ X → n ∈ expVisitIndicesRealLogb a q X) ∧
    (expVisitIndicesRealLogb a q X).card ≤
      1 + ⌊Real.logb (2 : ℝ)
        (((X + 1 : ℕ) : ℝ) / ((q + 1 : ℕ) : ℝ))⌋₊ := by
  constructor
  · intro n hn
    have hb := extension5_index_real_logb_bound ha hq h0 hn
    simp only [expVisitIndicesRealLogb, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hn⟩
  · calc
      (expVisitIndicesRealLogb a q X).card ≤
          (Finset.range
            (⌊Real.logb (2 : ℝ)
                (((X + 1 : ℕ) : ℝ) / ((q + 1 : ℕ) : ℝ))⌋₊ + 1)).card := by
        exact Finset.card_filter_le _ _
      _ = 1 + ⌊Real.logb (2 : ℝ)
          (((X + 1 : ℕ) : ℝ) / ((q + 1 : ℕ) : ℝ))⌋₊ := by
        simp [Nat.add_comm]

end PrimeGPF
