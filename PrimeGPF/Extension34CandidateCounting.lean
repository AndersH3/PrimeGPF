import PrimeGPF.Extension34CandidatePairs

/-!
# Extensions 3 and 4: finite candidate-pair counting

The first counting layer only uses that the candidate sets are filtered
subsets of the corresponding weighted triangles.  This isolates the finite
combinatorial bound from the later sharp lattice asymptotics.
-/
namespace PrimeGPF

open PrimeGPF.Analytic

/-- The anchor-2 candidate set is no larger than its weighted triangle. -/
theorem extension3_candidatePairs_card_le_triangle (X : ℕ) :
    (extension3CandidatePairs X).card ≤
      (weightedTriangle (Real.log 3) (Real.log 5)
        (Real.log ((2 * X + 1 : ℕ) : ℝ))).card := by
  apply Finset.card_le_card
  intro x hx
  exact Finset.mem_filter.mp hx |>.1

/-- The anchor-3 candidate set is no larger than its weighted triangle. -/
theorem extension4_candidatePairs_card_le_triangle (X : ℕ) :
    (extension4CandidatePairs X).card ≤
      (weightedTriangle (Real.log 2) (Real.log 5)
        (Real.log ((3 * X + 1 : ℕ) : ℝ))).card := by
  apply Finset.card_le_card
  intro x hx
  exact Finset.mem_filter.mp hx |>.1

end PrimeGPF
