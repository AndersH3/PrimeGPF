import PrimeGPF.Extension34CandidatePairs

/-!
# Extensions 3 and 4: fiber counts reduce to candidate-pair counts

No uniqueness theorem for exponent pairs is needed for the upper bound.  Every
prime fiber input lies in the image of the finite candidate-pair set under the
explicit formula for `q`, and the cardinality of an image is at most the
cardinality of its domain.
-/
namespace PrimeGPF

open Claims

/-- Explicit candidate-input image for the anchor-2, output-5 fiber. -/
noncomputable def extension3CandidateInputs (X : ℕ) : Finset ℕ := by
  classical
  exact (extension3CandidatePairs X).image
    (fun e => (3 ^ e.1 * 5 ^ e.2 - 1) / 2)

/-- Explicit candidate-input image for the anchor-3, output-5 fiber. -/
noncomputable def extension4CandidateInputs (X : ℕ) : Finset ℕ := by
  classical
  exact (extension4CandidatePairs X).image
    (fun e => (2 ^ e.1 * 5 ^ e.2 - 1) / 3)

/-- The anchor-2 fiber is contained in the exceptional input `2` together with
the candidate-pair image. -/
theorem extension3_fiber_subset_candidate_inputs (X : ℕ) :
    (Finset.range (X + 1)).filter
        (fun q => Nat.Prime q ∧ mul 2 q = 5) ⊆
      insert 2 (extension3CandidateInputs X) := by
  classical
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  have hqX : q ≤ X := by
    have := Finset.mem_range.mp hq'.1
    omega
  by_cases hq2 : q = 2
  · subst q
    simp
  · apply Finset.mem_insert_of_mem
    obtain ⟨α, β, hpair, hqform⟩ :=
      extension3_fiber_has_exact_candidate_pair hq'.2.1 hq'.2.2 hq2 hqX
    apply Finset.mem_image.mpr
    exact ⟨(α, β), hpair, hqform.symm⟩

/-- The anchor-3 fiber is contained in its candidate-pair image. -/
theorem extension4_fiber_subset_candidate_inputs (X : ℕ) :
    (Finset.range (X + 1)).filter
        (fun q => Nat.Prime q ∧ mul 3 q = 5) ⊆
      extension4CandidateInputs X := by
  classical
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  have hqX : q ≤ X := by
    have := Finset.mem_range.mp hq'.1
    omega
  obtain ⟨α, β, hpair, hqform⟩ :=
    extension4_fiber_has_exact_candidate_pair hq'.2.1 hq'.2.2 hqX
  apply Finset.mem_image.mpr
  exact ⟨(α, β), hpair, hqform.symm⟩

/-- Finite candidate-pair upper bound for the anchor-2, output-5 fiber. -/
theorem extension3_fiberCount_le_candidatePairs_add_one (X : ℕ) :
    Claims.fiberCount .mul 2 5 X ≤ (extension3CandidatePairs X).card + 1 := by
  classical
  have hsub := extension3_fiber_subset_candidate_inputs X
  have hcard := Finset.card_le_card hsub
  have himage :
      (extension3CandidateInputs X).card ≤ (extension3CandidatePairs X).card := by
    dsimp [extension3CandidateInputs]
    exact Finset.card_image_le
  calc
    Claims.fiberCount .mul 2 5 X =
        ((Finset.range (X + 1)).filter
          (fun q => Nat.Prime q ∧ mul 2 q = 5)).card := by
      rfl
    _ ≤ (insert 2 (extension3CandidateInputs X)).card := hcard
    _ ≤ (extension3CandidateInputs X).card + 1 :=
      Finset.card_insert_le 2 (extension3CandidateInputs X)
    _ ≤ (extension3CandidatePairs X).card + 1 := Nat.add_le_add_right himage 1

/-- Finite candidate-pair upper bound for the anchor-3, output-5 fiber. -/
theorem extension4_fiberCount_le_candidatePairs (X : ℕ) :
    Claims.fiberCount .mul 3 5 X ≤ (extension4CandidatePairs X).card := by
  classical
  have hsub := extension4_fiber_subset_candidate_inputs X
  have hcard := Finset.card_le_card hsub
  have himage :
      (extension4CandidateInputs X).card ≤ (extension4CandidatePairs X).card := by
    dsimp [extension4CandidateInputs]
    exact Finset.card_image_le
  calc
    Claims.fiberCount .mul 3 5 X =
        ((Finset.range (X + 1)).filter
          (fun q => Nat.Prime q ∧ mul 3 q = 5)).card := by
      rfl
    _ ≤ (extension4CandidateInputs X).card := hcard
    _ ≤ (extension4CandidatePairs X).card := himage

/-- Forgetting positivity/parity/coprimality only enlarges the anchor-2
candidate set, so it is bounded by the full weighted triangle. -/
theorem extension3_candidatePairs_card_le_weightedTriangle (X : ℕ) :
    (extension3CandidatePairs X).card ≤
      (PrimeGPF.Analytic.weightedTriangle
        (Real.log 3) (Real.log 5)
        (Real.log ((2 * X + 1 : ℕ) : ℝ))).card := by
  classical
  unfold extension3CandidatePairs
  exact Finset.card_filter_le _ _

/-- Analogous full-triangle bound for the anchor-3 candidate set. -/
theorem extension4_candidatePairs_card_le_weightedTriangle (X : ℕ) :
    (extension4CandidatePairs X).card ≤
      (PrimeGPF.Analytic.weightedTriangle
        (Real.log 2) (Real.log 5)
        (Real.log ((3 * X + 1 : ℕ) : ℝ))).card := by
  classical
  unfold extension4CandidatePairs
  exact Finset.card_filter_le _ _

end PrimeGPF
