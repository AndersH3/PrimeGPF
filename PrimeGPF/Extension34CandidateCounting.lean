import PrimeGPF.Extension34CandidatePairs
import PrimeGPF.WeightedTriangleArea

/-!
# Extensions 3 and 4: finite candidate-pair counting

This module is the interface between the arithmetic classification and the
analytic lattice-counting layer.

The argument deliberately proceeds in two monotone steps:

1. the arithmetic candidate set is a filtered subset of the corresponding
   weighted lattice triangle;
2. `WeightedTriangleArea` bounds that triangle by its Euclidean area plus an
   explicit linear boundary term.

At this stage we **do not** use the parity or coprimality restrictions to
improve the leading constant.  Those density corrections belong to the later
Möbius/parity layer.  Consequently the coefficient proved here is the raw
triangle coefficient `1 / (2*u*v)`.
-/
namespace PrimeGPF

open PrimeGPF.Analytic

/-- The anchor-2 candidate set is no larger than its ambient weighted
triangle.  This finite inclusion is intentionally kept separate from the
analytic area estimate. -/
theorem extension3_candidatePairs_card_le_triangle (X : ℕ) :
    (extension3CandidatePairs X).card ≤
      (weightedTriangle (Real.log 3) (Real.log 5)
        (Real.log ((2 * X + 1 : ℕ) : ℝ))).card := by
  apply Finset.card_le_card
  intro x hx
  exact (Finset.mem_filter.mp hx).1

/-- The anchor-3 candidate set is no larger than its ambient weighted
triangle. -/
theorem extension4_candidatePairs_card_le_triangle (X : ℕ) :
    (extension4CandidatePairs X).card ≤
      (weightedTriangle (Real.log 2) (Real.log 5)
        (Real.log ((3 * X + 1 : ℕ) : ℝ))).card := by
  apply Finset.card_le_card
  intro x hx
  exact (Finset.mem_filter.mp hx).1

/-- Explicit area-plus-boundary bound for the anchor-2 candidate pairs.

Writing `L = log(2X+1)`, the main term is
`L^2 / (2 log 3 log 5)`.  The later parity/coprimality analysis can only
reduce this candidate count and is responsible for the sharper report
constant. -/
theorem extension3_candidatePairs_card_cast_le_area_boundary (X : ℕ) :
    ((extension3CandidatePairs X).card : ℝ) ≤
      (Real.log ((2 * X + 1 : ℕ) : ℝ)) ^ 2 /
          (2 * Real.log 3 * Real.log 5) +
        Real.log ((2 * X + 1 : ℕ) : ℝ) / Real.log 3 +
        3 * Real.log ((2 * X + 1 : ℕ) : ℝ) / (2 * Real.log 5) + 1 := by
  let L : ℝ := Real.log ((2 * X + 1 : ℕ) : ℝ)
  have hL : 0 ≤ L := by
    dsimp [L]
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 2 * X + 1 by omega)
  have hcard :
      ((extension3CandidatePairs X).card : ℝ) ≤
        ((weightedTriangle (Real.log 3) (Real.log 5) L).card : ℝ) := by
    exact_mod_cast extension3_candidatePairs_card_le_triangle X
  have harea :=
    weightedTriangle_card_cast_le_area_boundary
      (u := Real.log 3) (v := Real.log 5) (L := L)
      log_three_pos log_five_pos hL
  dsimp [L] at hcard harea ⊢
  exact hcard.trans harea

/-- Explicit area-plus-boundary bound for the anchor-3 candidate pairs.

Here `L = log(3X+1)` and the raw geometric main term is
`L^2 / (2 log 2 log 5)`. -/
theorem extension4_candidatePairs_card_cast_le_area_boundary (X : ℕ) :
    ((extension4CandidatePairs X).card : ℝ) ≤
      (Real.log ((3 * X + 1 : ℕ) : ℝ)) ^ 2 /
          (2 * Real.log 2 * Real.log 5) +
        Real.log ((3 * X + 1 : ℕ) : ℝ) / Real.log 2 +
        3 * Real.log ((3 * X + 1 : ℕ) : ℝ) / (2 * Real.log 5) + 1 := by
  let L : ℝ := Real.log ((3 * X + 1 : ℕ) : ℝ)
  have hL : 0 ≤ L := by
    dsimp [L]
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 3 * X + 1 by omega)
  have hcard :
      ((extension4CandidatePairs X).card : ℝ) ≤
        ((weightedTriangle (Real.log 2) (Real.log 5) L).card : ℝ) := by
    exact_mod_cast extension4_candidatePairs_card_le_triangle X
  have harea :=
    weightedTriangle_card_cast_le_area_boundary
      (u := Real.log 2) (v := Real.log 5) (L := L)
      log_two_pos log_five_pos hL
  dsimp [L] at hcard harea ⊢
  exact hcard.trans harea

end PrimeGPF
