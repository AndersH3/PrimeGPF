import PrimeGPF.Extension34WeightedPairs
import PrimeGPF.Extension34ResidueHelpers
import PrimeGPF.WeightedTriangle

/-!
# Extensions 3 and 4: finite candidate exponent-pair sets

The exact classifications and weighted inequalities reduce each output-5 fiber
to a finite set of exponent pairs.  This file currently provides the finite
candidate sets, their membership descriptions, and the final reduction from a
fiber element to a candidate pair.

The proof layers are deliberately separated conceptually:

`exact classification → weighted exponent inequality → finite candidate set`.

Counting and asymptotic estimates are handled in later modules.  Small residue,
logarithm, and quotient-reconstruction facts are imported from
`Extension34ResidueHelpers` so the proofs below expose the mathematical
structure rather than low-level arithmetic bookkeeping.
-/
namespace PrimeGPF

open PrimeGPF.Analytic

/-- Candidate exponent pairs for the anchor-2, output-5 fiber up to input
cutoff `X`.  Besides lying in the weighted logarithmic triangle, the pair must
be positive, primitive, and have odd first exponent. -/
noncomputable def extension3CandidatePairs (X : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact
    (weightedTriangle (Real.log 3) (Real.log 5)
      (Real.log ((2 * X + 1 : ℕ) : ℝ))).filter
      (fun e => 0 < e.1 ∧ 0 < e.2 ∧ e.1 % 2 = 1 ∧ Nat.Coprime e.1 e.2)

/-- Candidate exponent pairs for the anchor-3, output-5 fiber up to input
cutoff `X`.  Here both positive exponents must be odd and primitive. -/
noncomputable def extension4CandidatePairs (X : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact
    (weightedTriangle (Real.log 2) (Real.log 5)
      (Real.log ((3 * X + 1 : ℕ) : ℝ))).filter
      (fun e => 0 < e.1 ∧ 0 < e.2 ∧ e.1 % 2 = 1 ∧ e.2 % 2 = 1 ∧
        Nat.Coprime e.1 e.2)

/-- Membership characterization for the anchor-2 candidate set.  This is the
main interface consumed by the later counting layer. -/
theorem mem_extension3CandidatePairs_iff (X α β : ℕ) :
    (α, β) ∈ extension3CandidatePairs X ↔
      0 < α ∧ 0 < β ∧ α % 2 = 1 ∧ Nat.Coprime α β ∧
      (α : ℝ) * Real.log 3 + (β : ℝ) * Real.log 5 ≤
        Real.log ((2 * X + 1 : ℕ) : ℝ) := by
  have hcut : 0 ≤ Real.log ((2 * X + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 2 * X + 1 by omega)
  simp only [extension3CandidatePairs, Finset.mem_filter]
  rw [mem_weightedTriangle_iff log_three_pos log_five_pos hcut]
  aesop

/-- Membership characterization for the anchor-3 candidate set. -/
theorem mem_extension4CandidatePairs_iff (X α β : ℕ) :
    (α, β) ∈ extension4CandidatePairs X ↔
      0 < α ∧ 0 < β ∧ α % 2 = 1 ∧ β % 2 = 1 ∧ Nat.Coprime α β ∧
      (α : ℝ) * Real.log 2 + (β : ℝ) * Real.log 5 ≤
        Real.log ((3 * X + 1 : ℕ) : ℝ) := by
  have hcut : 0 ≤ Real.log ((3 * X + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 3 * X + 1 by omega)
  simp only [extension4CandidatePairs, Finset.mem_filter]
  rw [mem_weightedTriangle_iff log_two_pos log_five_pos hcut]
  aesop

/-- Every nonexceptional anchor-2 output-5 fiber input below `X` supplies an
exact-classification pair in the finite candidate set.

The only arithmetic reconstruction needed after the exact classification is
that `(3^α * 5^β - 1) / 2` is an exact quotient.  The generic helper
`quotient_sub_one_reconstruct` packages that step. -/
theorem extension3_fiber_has_exact_candidate_pair
    {q X : ℕ} (hq : Nat.Prime q) (hout : mul 2 q = 5)
    (hq2 : q ≠ 2) (hqX : q ≤ X) :
    ∃ α β,
      (α, β) ∈ extension3CandidatePairs X ∧
      q = (3 ^ α * 5 ^ β - 1) / 2 := by
  rcases (extension3_exact_classification hq).mp hout with hqeq | hpair
  · exact (hq2 hqeq).elim
  · obtain ⟨α, β, hα, hβ, hodd, hcop, hqform⟩ := hpair
    let N := 3 ^ α * 5 ^ β
    have h3mod : 3 ^ α % 2 = 1 := by simp [Nat.pow_mod]
    have h5mod : 5 ^ β % 2 = 1 := by simp [Nat.pow_mod]
    have hNmod : N % 2 = 1 := by
      dsimp [N]
      exact odd_product_mod_two h3mod h5mod
    have hN1 : 1 ≤ N := by
      dsimp [N]
      positivity
    have hdiv : 2 ∣ N - 1 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    have hqformN : q = (N - 1) / 2 := by
      simpa [N] using hqform
    have hfacN : 2 * q + 1 = N :=
      quotient_sub_one_reconstruct hN1 hdiv hqformN
    have hfac : 2 * q + 1 = 3 ^ α * 5 ^ β := by
      simpa [N] using hfacN
    have hweighted := extension3_exponents_weighted_le hfac hqX
    exact ⟨α, β,
      (mem_extension3CandidatePairs_iff X α β).2
        ⟨hα, hβ, hodd, hcop, hweighted⟩,
      hqform⟩

/-- Every anchor-3 output-5 fiber input below `X` supplies an
exact-classification pair in the finite candidate set.  Oddness of both
exponents makes the reconstruction numerator `1 mod 3`, so division by `3` is
exact. -/
theorem extension4_fiber_has_exact_candidate_pair
    {q X : ℕ} (hq : Nat.Prime q) (hout : mul 3 q = 5)
    (hqX : q ≤ X) :
    ∃ α β,
      (α, β) ∈ extension4CandidatePairs X ∧
      q = (2 ^ α * 5 ^ β - 1) / 3 := by
  obtain ⟨α, β, hα, hβ, hαodd, hβodd, hcop, hqform⟩ :=
    (extension4_exact_classification hq).mp hout
  let N := 2 ^ α * 5 ^ β
  have h2 : 2 ^ α % 3 = 2 := extension_two_pow_mod_three_of_odd hαodd
  have h5 : 5 ^ β % 3 = 2 := five_pow_mod_three_odd β hβodd
  have hNmod : N % 3 = 1 := by
    dsimp [N]
    norm_num [Nat.mul_mod, h2, h5]
  have hN1 : 1 ≤ N := by
    dsimp [N]
    positivity
  have hdiv : 3 ∣ N - 1 := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  have hqformN : q = (N - 1) / 3 := by
    simpa [N] using hqform
  have hfacN : 3 * q + 1 = N :=
    quotient_sub_one_reconstruct hN1 hdiv hqformN
  have hfac : 3 * q + 1 = 2 ^ α * 5 ^ β := by
    simpa [N] using hfacN
  have hweighted := extension4_exponents_weighted_le hfac hqX
  exact ⟨α, β,
    (mem_extension4CandidatePairs_iff X α β).2
      ⟨hα, hβ, hαodd, hβodd, hcop, hweighted⟩,
    hqform⟩

end PrimeGPF
