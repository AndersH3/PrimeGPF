import PrimeGPF.WeightedTriangleRows

/-!
# Area bound for weighted lattice triangles

Combining the row-sum estimate with the elementary arithmetic-series formula
gives the sharp geometric leading coefficient `1 / (2*u*v)`.

The proof has three transparent steps:

1. replace each discrete row by its real width bound;
2. sum those widths exactly;
3. compare the floor cutoff `A = ⌊L/u⌋` with the real cutoff `t = L/u`.

The resulting boundary term is explicit and linear in `L`; its precise
coefficient is not important for later `O(L)` applications.
-/
namespace PrimeGPF.Analytic

/-- Closed form for the real row-width sum through row `A`. -/
theorem weighted_row_sum_closed_form (u v L : ℝ) (A : ℕ) :
    (∑ α ∈ Finset.range (A + 1), ((L - (α : ℝ) * u) / v + 1)) =
      ((A : ℝ) + 1) * (L / v + 1) -
        (u / v) * ((A : ℝ) * ((A : ℝ) + 1) / 2) := by
  induction A with
  | zero => simp
  | succ A ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- A finite weighted lattice triangle has the Euclidean triangle area as its
leading term, with an explicit linear boundary error.

The estimate is intentionally one-sided: later fiber-counting arguments only
need an upper bound, so no lower lattice-point estimate is introduced here. -/
theorem weightedTriangle_card_cast_le_area_boundary
    {u v L : ℝ} (hu : 0 < u) (hv : 0 < v) (hL : 0 ≤ L) :
    ((weightedTriangle u v L).card : ℝ) ≤
      L ^ 2 / (2 * u * v) + L / u + 3 * L / (2 * v) + 1 := by
  let A : ℕ := ⌊L / u⌋₊
  let a : ℝ := (A : ℝ)
  let t : ℝ := L / u

  have ht : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg hL hu.le
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have hau : a ≤ t := by
    dsimp [a, A, t]
    exact Nat.floor_le (div_nonneg hL hu.le)
  have hal : t - 1 < a := by
    dsimp [a, A, t]
    exact_mod_cast Nat.sub_one_lt_floor (L / u)

  -- The floor cutoff differs from the real cutoff by less than one.  These
  -- two consequences are exactly what is needed to compare the row sums.
  have hplus : a + 1 ≤ t + 1 := by linarith
  have hquad : (t - 1) * t ≤ a * (a + 1) := by
    nlinarith

  have hLv : 0 ≤ L / v + 1 := by
    have : 0 ≤ L / v := div_nonneg hL hv.le
    linarith
  have hfirst :
      (a + 1) * (L / v + 1) ≤ (t + 1) * (L / v + 1) :=
    mul_le_mul_of_nonneg_right hplus hLv

  have hrows := weightedTriangle_card_cast_le_row_sum hu hv hL
  have hclosed :
      (∑ α ∈ Finset.range (A + 1), ((L - (α : ℝ) * u) / v + 1)) =
        (a + 1) * (L / v + 1) -
          (u / v) * (a * (a + 1) / 2) := by
    simpa [a] using weighted_row_sum_closed_form u v L A

  have hsecond :
      (u / v) * (((t - 1) * t) / 2) ≤
        (u / v) * (a * (a + 1) / 2) := by
    have huv : 0 ≤ u / v := by positivity
    exact mul_le_mul_of_nonneg_left (by nlinarith) huv

  have hmiddle :
      (a + 1) * (L / v + 1) - (u / v) * (a * (a + 1) / 2) ≤
        (t + 1) * (L / v + 1) -
          (u / v) * (((t - 1) * t) / 2) := by
    linarith

  have hid :
      (t + 1) * (L / v + 1) -
          (u / v) * (((t - 1) * t) / 2) =
        L ^ 2 / (2 * u * v) + L / u + 3 * L / (2 * v) + 1 := by
    dsimp [t]
    field_simp [ne_of_gt hu, ne_of_gt hv]
    ring

  calc
    ((weightedTriangle u v L).card : ℝ)
        ≤ ∑ α ∈ Finset.range (⌊L / u⌋₊ + 1),
            ((L - (α : ℝ) * u) / v + 1) := hrows
    _ = (a + 1) * (L / v + 1) -
          (u / v) * (a * (a + 1) / 2) := by
        simpa [A] using hclosed
    _ ≤ (t + 1) * (L / v + 1) -
          (u / v) * (((t - 1) * t) / 2) := hmiddle
    _ = L ^ 2 / (2 * u * v) + L / u + 3 * L / (2 * v) + 1 := hid

end PrimeGPF.Analytic
