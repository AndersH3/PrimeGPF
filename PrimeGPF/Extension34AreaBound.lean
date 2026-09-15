import PrimeGPF.Extension34CandidateCount
import PrimeGPF.WeightedTriangleArea

/-!
# Extensions 3 and 4: finite sharp-area bounds

These are the finite bounds obtained before imposing the parity/coprimality
densities.  They already have the correct two-dimensional triangle factor
`1/2`; the remaining refinement is to count only the admissible primitive
lattice points.
-/
namespace PrimeGPF

open Claims

/-- Anchor 2, output 5: the candidate-pair reduction plus the weighted
triangle area estimate.  The final `+2` includes the single exceptional input
`q = 2` and the lattice boundary constant. -/
theorem extension3_fiberCount_real_le_area_boundary (X : ℕ) :
    (Claims.fiberCount .mul 2 5 X : ℝ) ≤
      (Real.log ((2 * X + 1 : ℕ) : ℝ)) ^ 2 /
          (2 * Real.log 3 * Real.log 5) +
        Real.log ((2 * X + 1 : ℕ) : ℝ) / Real.log 3 +
        3 * Real.log ((2 * X + 1 : ℕ) : ℝ) / (2 * Real.log 5) + 2 := by
  let L := Real.log ((2 * X + 1 : ℕ) : ℝ)
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hlog5 : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  have hL : 0 ≤ L := by
    dsimp [L]
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 2 * X + 1 by omega)
  have hfiber := extension3_fiberCount_le_candidatePairs_add_one X
  have hcand := extension3_candidatePairs_card_le_weightedTriangle X
  have harea := PrimeGPF.Analytic.weightedTriangle_card_cast_le_area_boundary
    hlog3 hlog5 hL
  calc
    (Claims.fiberCount .mul 2 5 X : ℝ)
        ≤ ((extension3CandidatePairs X).card : ℝ) + 1 := by
          exact_mod_cast hfiber
    _ ≤ ((PrimeGPF.Analytic.weightedTriangle
          (Real.log 3) (Real.log 5) L).card : ℝ) + 1 := by
          exact_mod_cast Nat.add_le_add_right hcand 1
    _ ≤ L ^ 2 / (2 * Real.log 3 * Real.log 5) +
          L / Real.log 3 + 3 * L / (2 * Real.log 5) + 2 := by
          linarith
    _ = (Real.log ((2 * X + 1 : ℕ) : ℝ)) ^ 2 /
          (2 * Real.log 3 * Real.log 5) +
        Real.log ((2 * X + 1 : ℕ) : ℝ) / Real.log 3 +
        3 * Real.log ((2 * X + 1 : ℕ) : ℝ) / (2 * Real.log 5) + 2 := by
          rfl

/-- Anchor 3, output 5: the corresponding full-triangle finite bound. -/
theorem extension4_fiberCount_real_le_area_boundary (X : ℕ) :
    (Claims.fiberCount .mul 3 5 X : ℝ) ≤
      (Real.log ((3 * X + 1 : ℕ) : ℝ)) ^ 2 /
          (2 * Real.log 2 * Real.log 5) +
        Real.log ((3 * X + 1 : ℕ) : ℝ) / Real.log 2 +
        3 * Real.log ((3 * X + 1 : ℕ) : ℝ) / (2 * Real.log 5) + 1 := by
  let L := Real.log ((3 * X + 1 : ℕ) : ℝ)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog5 : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  have hL : 0 ≤ L := by
    dsimp [L]
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 3 * X + 1 by omega)
  have hfiber := extension4_fiberCount_le_candidatePairs X
  have hcand := extension4_candidatePairs_card_le_weightedTriangle X
  have harea := PrimeGPF.Analytic.weightedTriangle_card_cast_le_area_boundary
    hlog2 hlog5 hL
  calc
    (Claims.fiberCount .mul 3 5 X : ℝ)
        ≤ ((extension4CandidatePairs X).card : ℝ) := by
          exact_mod_cast hfiber
    _ ≤ ((PrimeGPF.Analytic.weightedTriangle
          (Real.log 2) (Real.log 5) L).card : ℝ) := by
          exact_mod_cast hcand
    _ ≤ L ^ 2 / (2 * Real.log 2 * Real.log 5) +
          L / Real.log 2 + 3 * L / (2 * Real.log 5) + 1 := harea
    _ = (Real.log ((3 * X + 1 : ℕ) : ℝ)) ^ 2 /
          (2 * Real.log 2 * Real.log 5) +
        Real.log ((3 * X + 1 : ℕ) : ℝ) / Real.log 2 +
        3 * Real.log ((3 * X + 1 : ℕ) : ℝ) / (2 * Real.log 5) + 1 := by
          rfl

end PrimeGPF
