import PrimeGPF.Extension34FiberCounting

/-!
# Extensions 3 and 4: parity-restricted weighted triangles

The exact classifications already impose parity conditions on the exponent
vectors.  Before using Möbius inversion for coprimality, those parity
conditions alone improve the geometric lattice-point coefficient:

* Extension 3: `α` is odd, so write `α = 2m + 1`; this contributes a factor
  `1/2` to the unrestricted triangle area.
* Extension 4: both `α` and `β` are odd, so write
  `(α,β) = (2m+1,2n+1)`; this contributes a factor `1/4`.

This module formalizes those reparameterizations as inclusions into shifted
weighted triangles and then applies the existing area-plus-boundary theorem.
Coprimality is deliberately ignored here; the remaining `4/(3 ζ(2))` factor
belongs to the later Möbius layer.
-/
namespace PrimeGPF

open PrimeGPF.Analytic

/-- Shifted cutoff after writing the odd Extension-3 exponent as `2m+1`. -/
def extension3ParityCutoff (X : ℕ) : ℝ :=
  Real.log ((2 * X + 1 : ℕ) : ℝ) - Real.log 3

/-- Shifted cutoff after writing both odd Extension-4 exponents as
`2m+1, 2n+1`. -/
def extension4ParityCutoff (X : ℕ) : ℝ :=
  Real.log ((3 * X + 1 : ℕ) : ℝ) - Real.log 2 - Real.log 5

/-- Parity-reduced ambient triangle for Extension 3. -/
noncomputable def extension3ParityTriangle (X : ℕ) : Finset (ℕ × ℕ) :=
  weightedTriangle (2 * Real.log 3) (Real.log 5) (extension3ParityCutoff X)

/-- Parity-reduced ambient triangle for Extension 4. -/
noncomputable def extension4ParityTriangle (X : ℕ) : Finset (ℕ × ℕ) :=
  weightedTriangle (2 * Real.log 2) (2 * Real.log 5)
    (extension4ParityCutoff X)

/-- Re-expand a parity-reduced Extension-3 pair. -/
def extension3ParityExpand (e : ℕ × ℕ) : ℕ × ℕ :=
  (2 * e.1 + 1, e.2)

/-- Re-expand a parity-reduced Extension-4 pair. -/
def extension4ParityExpand (e : ℕ × ℕ) : ℕ × ℕ :=
  (2 * e.1 + 1, 2 * e.2 + 1)

/-- For `X ≥ 1`, the shifted Extension-3 logarithmic cutoff is nonnegative. -/
lemma extension3ParityCutoff_nonneg {X : ℕ} (hX : 1 ≤ X) :
    0 ≤ extension3ParityCutoff X := by
  have hargNat : 3 ≤ 2 * X + 1 := by omega
  have harg : (3 : ℝ) ≤ ((2 * X + 1 : ℕ) : ℝ) := by
    exact_mod_cast hargNat
  have hlog : Real.log (3 : ℝ) ≤ Real.log ((2 * X + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) harg
  dsimp [extension3ParityCutoff]
  linarith

/-- For `X ≥ 3`, the shifted Extension-4 logarithmic cutoff is nonnegative. -/
lemma extension4ParityCutoff_nonneg {X : ℕ} (hX : 3 ≤ X) :
    0 ≤ extension4ParityCutoff X := by
  have hargNat : 10 ≤ 3 * X + 1 := by omega
  have harg : (10 : ℝ) ≤ ((3 * X + 1 : ℕ) : ℝ) := by
    exact_mod_cast hargNat
  have hlog10 : Real.log (10 : ℝ) ≤ Real.log ((3 * X + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) harg
  have hlogprod : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  dsimp [extension4ParityCutoff]
  linarith

/-!
The next two proofs use the same compression pattern: divide every forced-odd
coordinate by two, prove that the compressed pair lies in the shifted weighted
triangle, and recover the original candidate with the corresponding expansion
map.  Keeping this geometric step separate makes the later cardinality bounds
nearly formal consequences of `Finset.image`.
-/

/-- Every Extension-3 candidate pair is the odd re-expansion of a point in the
shifted parity triangle. -/
theorem extension3_candidatePairs_subset_parityImage
    {X : ℕ} (hX : 1 ≤ X) :
    extension3CandidatePairs X ⊆
      (extension3ParityTriangle X).image extension3ParityExpand := by
  classical
  intro e he
  rcases e with ⟨α, β⟩
  obtain ⟨hα, hβ, hαodd, hcop, hweighted⟩ :=
    (mem_extension3CandidatePairs_iff X α β).1 he
  have hαeq : 2 * (α / 2) + 1 = α := by omega
  have hαcast :
      (α : ℝ) = 2 * (((α / 2 : ℕ) : ℝ)) + 1 := by
    exact_mod_cast hαeq.symm
  have hineq :
      (((α / 2 : ℕ) : ℝ)) * (2 * Real.log 3) +
          (β : ℝ) * Real.log 5 ≤ extension3ParityCutoff X := by
    dsimp [extension3ParityCutoff]
    calc
      (((α / 2 : ℕ) : ℝ)) * (2 * Real.log 3) +
          (β : ℝ) * Real.log 5 =
          (α : ℝ) * Real.log 3 + (β : ℝ) * Real.log 5 - Real.log 3 := by
            rw [hαcast]
            ring
      _ ≤ Real.log ((2 * X + 1 : ℕ) : ℝ) - Real.log 3 := by
        linarith
  have hsource : (α / 2, β) ∈ extension3ParityTriangle X := by
    change (α / 2, β) ∈
      weightedTriangle (2 * Real.log 3) (Real.log 5) (extension3ParityCutoff X)
    exact (mem_weightedTriangle_iff
      (mul_pos (by norm_num) log_three_pos) log_five_pos
      (extension3ParityCutoff_nonneg hX) (α / 2) β).2 hineq
  apply Finset.mem_image.mpr
  refine ⟨(α / 2, β), hsource, ?_⟩
  simp [extension3ParityExpand, hαeq]

/-- Every Extension-4 candidate pair is the odd-odd re-expansion of a point in
the shifted parity triangle. -/
theorem extension4_candidatePairs_subset_parityImage
    {X : ℕ} (hX : 3 ≤ X) :
    extension4CandidatePairs X ⊆
      (extension4ParityTriangle X).image extension4ParityExpand := by
  classical
  intro e he
  rcases e with ⟨α, β⟩
  obtain ⟨hα, hβ, hαodd, hβodd, hcop, hweighted⟩ :=
    (mem_extension4CandidatePairs_iff X α β).1 he
  have hαeq : 2 * (α / 2) + 1 = α := by omega
  have hβeq : 2 * (β / 2) + 1 = β := by omega
  have hαcast :
      (α : ℝ) = 2 * (((α / 2 : ℕ) : ℝ)) + 1 := by
    exact_mod_cast hαeq.symm
  have hβcast :
      (β : ℝ) = 2 * (((β / 2 : ℕ) : ℝ)) + 1 := by
    exact_mod_cast hβeq.symm
  have hineq :
      (((α / 2 : ℕ) : ℝ)) * (2 * Real.log 2) +
          (((β / 2 : ℕ) : ℝ)) * (2 * Real.log 5) ≤
        extension4ParityCutoff X := by
    dsimp [extension4ParityCutoff]
    calc
      (((α / 2 : ℕ) : ℝ)) * (2 * Real.log 2) +
          (((β / 2 : ℕ) : ℝ)) * (2 * Real.log 5) =
          (α : ℝ) * Real.log 2 + (β : ℝ) * Real.log 5 -
            Real.log 2 - Real.log 5 := by
              rw [hαcast, hβcast]
              ring
      _ ≤ Real.log ((3 * X + 1 : ℕ) : ℝ) - Real.log 2 - Real.log 5 := by
        linarith
  have hsource : (α / 2, β / 2) ∈ extension4ParityTriangle X := by
    change (α / 2, β / 2) ∈
      weightedTriangle (2 * Real.log 2) (2 * Real.log 5)
        (extension4ParityCutoff X)
    exact (mem_weightedTriangle_iff
      (mul_pos (by norm_num) log_two_pos)
      (mul_pos (by norm_num) log_five_pos)
      (extension4ParityCutoff_nonneg hX) (α / 2) (β / 2)).2 hineq
  apply Finset.mem_image.mpr
  refine ⟨(α / 2, β / 2), hsource, ?_⟩
  simp [extension4ParityExpand, hαeq, hβeq]

/-- Parity alone improves the Extension-3 candidate count to the shifted
triangle with doubled first weight. -/
theorem extension3_candidatePairs_card_le_parityTriangle
    {X : ℕ} (hX : 1 ≤ X) :
    (extension3CandidatePairs X).card ≤ (extension3ParityTriangle X).card := by
  calc
    (extension3CandidatePairs X).card
        ≤ ((extension3ParityTriangle X).image extension3ParityExpand).card :=
      Finset.card_le_card (extension3_candidatePairs_subset_parityImage hX)
    _ ≤ (extension3ParityTriangle X).card := Finset.card_image_le

/-- Parity alone improves the Extension-4 candidate count to the shifted
triangle with both weights doubled. -/
theorem extension4_candidatePairs_card_le_parityTriangle
    {X : ℕ} (hX : 3 ≤ X) :
    (extension4CandidatePairs X).card ≤ (extension4ParityTriangle X).card := by
  calc
    (extension4CandidatePairs X).card
        ≤ ((extension4ParityTriangle X).image extension4ParityExpand).card :=
      Finset.card_le_card (extension4_candidatePairs_subset_parityImage hX)
    _ ≤ (extension4ParityTriangle X).card := Finset.card_image_le

/-- Explicit parity-improved area bound for Extension 3.  The doubled first
weight implements the expected factor `1/2` in the geometric leading term. -/
theorem extension3_candidatePairs_card_cast_le_parity_area
    {X : ℕ} (hX : 1 ≤ X) :
    ((extension3CandidatePairs X).card : ℝ) ≤
      (extension3ParityCutoff X) ^ 2 /
          (2 * (2 * Real.log 3) * Real.log 5) +
        extension3ParityCutoff X / (2 * Real.log 3) +
        3 * extension3ParityCutoff X / (2 * Real.log 5) + 1 := by
  have hcard :
      ((extension3CandidatePairs X).card : ℝ) ≤
        ((extension3ParityTriangle X).card : ℝ) := by
    exact_mod_cast extension3_candidatePairs_card_le_parityTriangle hX
  have harea := weightedTriangle_card_cast_le_area_boundary
    (u := 2 * Real.log 3) (v := Real.log 5)
    (L := extension3ParityCutoff X)
    (mul_pos (by norm_num) log_three_pos) log_five_pos
    (extension3ParityCutoff_nonneg hX)
  change ((extension3ParityTriangle X).card : ℝ) ≤ _ at harea
  exact hcard.trans harea

/-- Explicit parity-improved area bound for Extension 4.  Doubling both weights
implements the expected factor `1/4` in the geometric leading term. -/
theorem extension4_candidatePairs_card_cast_le_parity_area
    {X : ℕ} (hX : 3 ≤ X) :
    ((extension4CandidatePairs X).card : ℝ) ≤
      (extension4ParityCutoff X) ^ 2 /
          (2 * (2 * Real.log 2) * (2 * Real.log 5)) +
        extension4ParityCutoff X / (2 * Real.log 2) +
        3 * extension4ParityCutoff X / (2 * (2 * Real.log 5)) + 1 := by
  have hcard :
      ((extension4CandidatePairs X).card : ℝ) ≤
        ((extension4ParityTriangle X).card : ℝ) := by
    exact_mod_cast extension4_candidatePairs_card_le_parityTriangle hX
  have harea := weightedTriangle_card_cast_le_area_boundary
    (u := 2 * Real.log 2) (v := 2 * Real.log 5)
    (L := extension4ParityCutoff X)
    (mul_pos (by norm_num) log_two_pos)
    (mul_pos (by norm_num) log_five_pos)
    (extension4ParityCutoff_nonneg hX)
  change ((extension4ParityTriangle X).card : ℝ) ≤ _ at harea
  exact hcard.trans harea

/-- Parity-improved finite fiber bound for Extension 3, retaining the single
exceptional input `q = 2`. -/
theorem extension3_fiberCount_cast_le_parity_area
    {X : ℕ} (hX : 1 ≤ X) :
    (Claims.fiberCount .mul 2 5 X : ℝ) ≤
      1 +
      (extension3ParityCutoff X) ^ 2 /
          (2 * (2 * Real.log 3) * Real.log 5) +
        extension3ParityCutoff X / (2 * Real.log 3) +
        3 * extension3ParityCutoff X / (2 * Real.log 5) + 1 := by
  have hfinite :
      (Claims.fiberCount .mul 2 5 X : ℝ) ≤
        1 + ((extension3CandidatePairs X).card : ℝ) := by
    exact_mod_cast extension3_fiberCount_le_one_add_candidatePairs X
  have hparity := extension3_candidatePairs_card_cast_le_parity_area hX
  linarith

/-- Parity-improved finite fiber bound for Extension 4. -/
theorem extension4_fiberCount_cast_le_parity_area
    {X : ℕ} (hX : 3 ≤ X) :
    (Claims.fiberCount .mul 3 5 X : ℝ) ≤
      (extension4ParityCutoff X) ^ 2 /
          (2 * (2 * Real.log 2) * (2 * Real.log 5)) +
        extension4ParityCutoff X / (2 * Real.log 2) +
        3 * extension4ParityCutoff X / (2 * (2 * Real.log 5)) + 1 := by
  have hfinite :
      (Claims.fiberCount .mul 3 5 X : ℝ) ≤
        ((extension4CandidatePairs X).card : ℝ) := by
    exact_mod_cast extension4_fiberCount_le_candidatePairs X
  exact hfinite.trans (extension4_candidatePairs_card_cast_le_parity_area hX)

end PrimeGPF
