import PrimeGPF.Extension34CandidateCounting
import PrimeGPF.Statements

/-!
# Extensions 3 and 4: fiber-to-candidate counting bridge

The arithmetic classification is useful for asymptotics only after it is tied
back to the project's existing finite fiber count `Claims.fiberCount`.  This
module provides that bridge without introducing a second notion of fiber.

The key idea is deliberately simple:

* map every admissible exponent pair to the prime candidate given by the
  quotient formula from the exact classification;
* show every actual fiber input belongs to that finite image;
* use `Finset.card_image_le` to forget possible collisions between different
  exponent pairs.

For anchor `2`, the exceptional input `q = 2` is handled by one extra point.
For anchor `3` there is no exceptional family.
-/
namespace PrimeGPF

/-- Prime candidate reconstructed from an Extension 3 exponent pair. -/
def extension3CandidateOutput (e : ℕ × ℕ) : ℕ :=
  (3 ^ e.1 * 5 ^ e.2 - 1) / 2

/-- Prime candidate reconstructed from an Extension 4 exponent pair. -/
def extension4CandidateOutput (e : ℕ × ℕ) : ℕ :=
  (2 ^ e.1 * 5 ^ e.2 - 1) / 3

/-- Image of the finite Extension 3 exponent-pair set under its quotient
formula.  No primality filter is needed for an upper bound. -/
noncomputable def extension3CandidateOutputs (X : ℕ) : Finset ℕ := by
  classical
  exact (extension3CandidatePairs X).image extension3CandidateOutput

/-- Image of the finite Extension 4 exponent-pair set under its quotient
formula. -/
noncomputable def extension4CandidateOutputs (X : ℕ) : Finset ℕ := by
  classical
  exact (extension4CandidatePairs X).image extension4CandidateOutput

/-- The actual finite anchor-2/output-5 fiber used by `Claims.fiberCount`. -/
noncomputable def extension3FiberInputs (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (X + 1)).filter
    (fun q => Nat.Prime q ∧ mul 2 q = 5)

/-- The actual finite anchor-3/output-5 fiber used by `Claims.fiberCount`. -/
noncomputable def extension4FiberInputs (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (X + 1)).filter
    (fun q => Nat.Prime q ∧ mul 3 q = 5)

/-- The local finite set is definitionally the multiplicative fiber count at
anchor `2`, output `5`. -/
theorem extension3FiberInputs_card_eq_fiberCount (X : ℕ) :
    (extension3FiberInputs X).card = Claims.fiberCount .mul 2 5 X := by
  simp [extension3FiberInputs, Claims.fiberCount, mul]

/-- The local finite set is definitionally the multiplicative fiber count at
anchor `3`, output `5`. -/
theorem extension4FiberInputs_card_eq_fiberCount (X : ℕ) :
    (extension4FiberInputs X).card = Claims.fiberCount .mul 3 5 X := by
  simp [extension4FiberInputs, Claims.fiberCount, mul]

/-- Every nonexceptional anchor-2 fiber input occurs in the image of the
candidate exponent pairs.  The exceptional prime `2` is inserted explicitly. -/
theorem extension3_fiberInputs_subset_insert_candidateOutputs (X : ℕ) :
    extension3FiberInputs X ⊆
      insert 2 (extension3CandidateOutputs X) := by
  intro q hq
  have hmem := Finset.mem_filter.mp hq
  have hprime : Nat.Prime q := hmem.2.1
  have hout : mul 2 q = 5 := hmem.2.2
  have hqX : q ≤ X := by
    have hrange := Finset.mem_range.mp hmem.1
    omega
  by_cases hq2 : q = 2
  · exact Finset.mem_insert.mpr (Or.inl hq2)
  · obtain ⟨α, β, hpair, hform⟩ :=
      extension3_fiber_has_exact_candidate_pair hprime hout hq2 hqX
    apply Finset.mem_insert.mpr
    right
    apply Finset.mem_image.mpr
    refine ⟨(α, β), hpair, ?_⟩
    exact hform.symm

/-- Every anchor-3 fiber input occurs in the image of the candidate exponent
pairs. -/
theorem extension4_fiberInputs_subset_candidateOutputs (X : ℕ) :
    extension4FiberInputs X ⊆ extension4CandidateOutputs X := by
  intro q hq
  have hmem := Finset.mem_filter.mp hq
  have hprime : Nat.Prime q := hmem.2.1
  have hout : mul 3 q = 5 := hmem.2.2
  have hqX : q ≤ X := by
    have hrange := Finset.mem_range.mp hmem.1
    omega
  obtain ⟨α, β, hpair, hform⟩ :=
    extension4_fiber_has_exact_candidate_pair hprime hout hqX
  apply Finset.mem_image.mpr
  refine ⟨(α, β), hpair, ?_⟩
  exact hform.symm

/-- Finite counting bound for Extension 3.  The only loss beyond candidate
pairs is the exceptional input `q = 2`. -/
theorem extension3_fiberCount_le_one_add_candidatePairs (X : ℕ) :
    Claims.fiberCount .mul 2 5 X ≤ 1 + (extension3CandidatePairs X).card := by
  have hsub := extension3_fiberInputs_subset_insert_candidateOutputs X
  have hfiber :
      (extension3FiberInputs X).card ≤
        (insert 2 (extension3CandidateOutputs X)).card :=
    Finset.card_le_card hsub
  have hinsert :
      (insert 2 (extension3CandidateOutputs X)).card ≤
        (extension3CandidateOutputs X).card + 1 := by
    by_cases h2 : 2 ∈ extension3CandidateOutputs X
    · rw [Finset.insert_eq_of_mem h2]
      omega
    · rw [Finset.card_insert_of_not_mem h2]
  have himage :
      (extension3CandidateOutputs X).card ≤
        (extension3CandidatePairs X).card := by
    exact Finset.card_image_le
  rw [← extension3FiberInputs_card_eq_fiberCount X]
  omega

/-- Finite counting bound for Extension 4.  Here there is no exceptional input,
so the fiber cardinality is bounded directly by the candidate-pair count. -/
theorem extension4_fiberCount_le_candidatePairs (X : ℕ) :
    Claims.fiberCount .mul 3 5 X ≤ (extension4CandidatePairs X).card := by
  have hsub := extension4_fiberInputs_subset_candidateOutputs X
  have hfiber :
      (extension4FiberInputs X).card ≤ (extension4CandidateOutputs X).card :=
    Finset.card_le_card hsub
  have himage :
      (extension4CandidateOutputs X).card ≤
        (extension4CandidatePairs X).card := by
    exact Finset.card_image_le
  rw [← extension4FiberInputs_card_eq_fiberCount X]
  exact hfiber.trans himage

/-- Combining the finite Extension 3 bridge with the weighted-triangle area
bound gives an explicit quadratic-logarithmic fiber estimate.  The extra
constant `1` is exactly the exceptional prime input `q = 2`. -/
theorem extension3_fiberCount_cast_le_area_boundary (X : ℕ) :
    (Claims.fiberCount .mul 2 5 X : ℝ) ≤
      1 +
      (Real.log ((2 * X + 1 : ℕ) : ℝ)) ^ 2 /
          (2 * Real.log 3 * Real.log 5) +
        Real.log ((2 * X + 1 : ℕ) : ℝ) / Real.log 3 +
        3 * Real.log ((2 * X + 1 : ℕ) : ℝ) / (2 * Real.log 5) + 1 := by
  have hfinite :
      (Claims.fiberCount .mul 2 5 X : ℝ) ≤
        1 + ((extension3CandidatePairs X).card : ℝ) := by
    exact_mod_cast extension3_fiberCount_le_one_add_candidatePairs X
  have harea := extension3_candidatePairs_card_cast_le_area_boundary X
  linarith

/-- Combining the finite Extension 4 bridge with the weighted-triangle area
bound gives the corresponding explicit quadratic-logarithmic fiber estimate. -/
theorem extension4_fiberCount_cast_le_area_boundary (X : ℕ) :
    (Claims.fiberCount .mul 3 5 X : ℝ) ≤
      (Real.log ((3 * X + 1 : ℕ) : ℝ)) ^ 2 /
          (2 * Real.log 2 * Real.log 5) +
        Real.log ((3 * X + 1 : ℕ) : ℝ) / Real.log 2 +
        3 * Real.log ((3 * X + 1 : ℕ) : ℝ) / (2 * Real.log 5) + 1 := by
  have hfinite :
      (Claims.fiberCount .mul 3 5 X : ℝ) ≤
        ((extension4CandidatePairs X).card : ℝ) := by
    exact_mod_cast extension4_fiberCount_le_candidatePairs X
  exact hfinite.trans (extension4_candidatePairs_card_cast_le_area_boundary X)

end PrimeGPF
