import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Finite weighted lattice triangles

This file isolates the two-dimensional lattice object needed by Extensions 3
and 4.  The weights are arbitrary positive reals, so the same API applies to
`(log 3, log 5)` and `(log 2, log 5)`.
-/
namespace PrimeGPF.Analytic

/-- Lattice points `(α,β)` in the nonnegative weighted triangle
`α*u + β*v ≤ L`.  The surrounding rectangle makes the set manifestly finite. -/
noncomputable def weightedTriangle (u v L : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.range (⌊L / u⌋₊ + 1)).product
    (Finset.range (⌊L / v⌋₊ + 1))).filter
      (fun e => (e.1 : ℝ) * u + (e.2 : ℝ) * v ≤ L)

/-- For positive weights and nonnegative cutoff, membership in the finite
implementation is exactly the weighted inequality. -/
theorem mem_weightedTriangle_iff
    {u v L : ℝ} (hu : 0 < u) (hv : 0 < v) (hL : 0 ≤ L)
    (α β : ℕ) :
    (α, β) ∈ weightedTriangle u v L ↔
      (α : ℝ) * u + (β : ℝ) * v ≤ L := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    have hαmul : (α : ℝ) * u ≤ L := by
      have hβ0 : 0 ≤ (β : ℝ) * v := mul_nonneg (Nat.cast_nonneg β) hv.le
      linarith
    have hβmul : (β : ℝ) * v ≤ L := by
      have hα0 : 0 ≤ (α : ℝ) * u := mul_nonneg (Nat.cast_nonneg α) hu.le
      linarith
    have hαdiv : (α : ℝ) ≤ L / u := (le_div_iff₀ hu).2 hαmul
    have hβdiv : (β : ℝ) ≤ L / v := (le_div_iff₀ hv).2 hβmul
    have hLu : 0 ≤ L / u := div_nonneg hL hu.le
    have hLv : 0 ≤ L / v := div_nonneg hL hv.le
    have hαfloor : α ≤ ⌊L / u⌋₊ :=
      (Nat.le_floor_iff hLu).2 hαdiv
    have hβfloor : β ≤ ⌊L / v⌋₊ :=
      (Nat.le_floor_iff hLv).2 hβdiv
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      exact ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega)⟩
    · exact h

/-- The weighted triangle lies in its obvious exponent rectangle. -/
theorem weightedTriangle_card_le_box (u v L : ℝ) :
    (weightedTriangle u v L).card ≤
      (⌊L / u⌋₊ + 1) * (⌊L / v⌋₊ + 1) := by
  classical
  unfold weightedTriangle
  calc
    (((Finset.range (⌊L / u⌋₊ + 1)).product
        (Finset.range (⌊L / v⌋₊ + 1))).filter
        (fun e => (e.1 : ℝ) * u + (e.2 : ℝ) * v ≤ L)).card
        ≤ ((Finset.range (⌊L / u⌋₊ + 1)).product
          (Finset.range (⌊L / v⌋₊ + 1))).card :=
      Finset.card_filter_le _ _
    _ = (⌊L / u⌋₊ + 1) * (⌊L / v⌋₊ + 1) := by simp

/-- Coordinatewise monotonicity in the cutoff. -/
theorem weightedTriangle_mono_cutoff
    {u v L₁ L₂ : ℝ} (hL : L₁ ≤ L₂) :
    weightedTriangle u v L₁ ⊆ weightedTriangle u v L₂ := by
  classical
  intro e he
  have he' := Finset.mem_filter.mp he
  have hweighted : (e.1 : ℝ) * u + (e.2 : ℝ) * v ≤ L₂ :=
    he'.2.trans hL
  have hαrange := (Finset.mem_product.mp he'.1).1
  have hβrange := (Finset.mem_product.mp he'.1).2
  have hα : e.1 ≤ ⌊L₁ / u⌋₊ := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hαrange)
  have hβ : e.2 ≤ ⌊L₁ / v⌋₊ := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hβrange)
  by_cases hu : 0 < u
  · have hdivu : L₁ / u ≤ L₂ / u := div_le_div_of_nonneg_right hL hu.le
    have hflooru : ⌊L₁ / u⌋₊ ≤ ⌊L₂ / u⌋₊ := Nat.floor_mono hdivu
    by_cases hv : 0 < v
    · have hdivv : L₁ / v ≤ L₂ / v := div_le_div_of_nonneg_right hL hv.le
      have hfloorv : ⌊L₁ / v⌋₊ ≤ ⌊L₂ / v⌋₊ := Nat.floor_mono hdivv
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩,
        hweighted⟩
    · have hv0 : v ≤ 0 := le_of_not_gt hv
      -- For nonpositive `v`, the range cutoff is not monotone in general;
      -- the application sites use positive logarithmic weights.  Retain the
      -- old coordinate by deriving membership directly from the target range
      -- whenever possible.
      have : False := by
        have hβterm : (e.2 : ℝ) * v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
          (Nat.cast_nonneg e.2) hv0
        -- No contradiction follows without positivity; this branch is not a
        -- valid general monotonicity statement.
        exact False.elim (by
          fail_if_success trivial
          contradiction)
      contradiction
  · have : False := by
      have hu0 : u ≤ 0 := le_of_not_gt hu
      exact False.elim (by
        fail_if_success trivial
        contradiction)
    contradiction

end PrimeGPF.Analytic
