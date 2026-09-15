import PrimeGPF.Extension34WeightedPairs
import PrimeGPF.WeightedTriangle

/-!
# Extensions 3 and 4: finite candidate exponent-pair sets

The exact classifications and weighted inequalities reduce each output-5 fiber
to a finite set of exponent pairs.  This file packages those pair sets with
all parity and coprimality restrictions, leaving only their asymptotic
cardinality to the later lattice/Möbius layer.
-/
namespace PrimeGPF

open PrimeGPF.Analytic

/-- Candidate exponent pairs for the anchor-2, output-5 fiber up to input
cutoff `X`. -/
noncomputable def extension3CandidatePairs (X : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact
    (weightedTriangle (Real.log 3) (Real.log 5)
      (Real.log ((2 * X + 1 : ℕ) : ℝ))).filter
      (fun e => 0 < e.1 ∧ 0 < e.2 ∧ e.1 % 2 = 1 ∧ Nat.Coprime e.1 e.2)

/-- Candidate exponent pairs for the anchor-3, output-5 fiber up to input
cutoff `X`. -/
noncomputable def extension4CandidatePairs (X : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact
    (weightedTriangle (Real.log 2) (Real.log 5)
      (Real.log ((3 * X + 1 : ℕ) : ℝ))).filter
      (fun e => 0 < e.1 ∧ 0 < e.2 ∧ e.1 % 2 = 1 ∧ e.2 % 2 = 1 ∧
        Nat.Coprime e.1 e.2)

/-- Membership characterization for the anchor-2 candidate set. -/
theorem mem_extension3CandidatePairs_iff (X α β : ℕ) :
    (α, β) ∈ extension3CandidatePairs X ↔
      0 < α ∧ 0 < β ∧ α % 2 = 1 ∧ Nat.Coprime α β ∧
      (α : ℝ) * Real.log 3 + (β : ℝ) * Real.log 5 ≤
        Real.log ((2 * X + 1 : ℕ) : ℝ) := by
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hlog5 : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  have hcut : 0 ≤ Real.log ((2 * X + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 2 * X + 1 by omega)
  simp only [extension3CandidatePairs, Finset.mem_filter]
  rw [mem_weightedTriangle_iff hlog3 hlog5 hcut]
  aesop

/-- Membership characterization for the anchor-3 candidate set. -/
theorem mem_extension4CandidatePairs_iff (X α β : ℕ) :
    (α, β) ∈ extension4CandidatePairs X ↔
      0 < α ∧ 0 < β ∧ α % 2 = 1 ∧ β % 2 = 1 ∧ Nat.Coprime α β ∧
      (α : ℝ) * Real.log 2 + (β : ℝ) * Real.log 5 ≤
        Real.log ((3 * X + 1 : ℕ) : ℝ) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog5 : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  have hcut : 0 ≤ Real.log ((3 * X + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 3 * X + 1 by omega)
  simp only [extension4CandidatePairs, Finset.mem_filter]
  rw [mem_weightedTriangle_iff hlog2 hlog5 hcut]
  aesop

/-- Every nonexceptional anchor-2 output-5 fiber input below `X` supplies an
exact-classification pair in the finite candidate set. -/
theorem extension3_fiber_has_exact_candidate_pair
    {q X : ℕ} (hq : Nat.Prime q) (hout : mul 2 q = 5)
    (hq2 : q ≠ 2) (hqX : q ≤ X) :
    ∃ α β,
      (α, β) ∈ extension3CandidatePairs X ∧
      q = (3 ^ α * 5 ^ β - 1) / 2 := by
  rcases (extension3_exact_classification hq).mp hout with hqeq | hpair
  · exact (hq2 hqeq).elim
  · obtain ⟨α, β, hα, hβ, hodd, hcop, hqform⟩ := hpair
    have hfac : 2 * q + 1 = 3 ^ α * 5 ^ β := by
      let N := 3 ^ α * 5 ^ β
      have hdiv : 2 ∣ N - 1 := by
        apply Nat.dvd_of_mod_eq_zero
        have h3odd : 3 ^ α % 2 = 1 := by simp [Nat.pow_mod]
        have h5odd : 5 ^ β % 2 = 1 := by simp [Nat.pow_mod]
        dsimp [N]
        norm_num [Nat.mul_mod, h3odd, h5odd]
      have hqmul : q * 2 = N - 1 := by
        rw [hqform]
        exact Nat.div_mul_cancel hdiv
      have hN1 : 1 ≤ N := by
        dsimp [N]
        positivity
      dsimp [N] at hqmul hN1 ⊢
      omega
    have hweighted := extension3_exponents_weighted_le hfac hqX
    exact ⟨α, β,
      (mem_extension3CandidatePairs_iff X α β).2
        ⟨hα, hβ, hodd, hcop, hweighted⟩,
      hqform⟩

/-- Every anchor-3 output-5 fiber input below `X` supplies an
exact-classification pair in the finite candidate set. -/
theorem extension4_fiber_has_exact_candidate_pair
    {q X : ℕ} (hq : Nat.Prime q) (hout : mul 3 q = 5)
    (hqX : q ≤ X) :
    ∃ α β,
      (α, β) ∈ extension4CandidatePairs X ∧
      q = (2 ^ α * 5 ^ β - 1) / 3 := by
  obtain ⟨α, β, hα, hβ, hαodd, hβodd, hcop, hqform⟩ :=
    (extension4_exact_classification hq).mp hout
  have hfac : 3 * q + 1 = 2 ^ α * 5 ^ β := by
    let N := 2 ^ α * 5 ^ β
    have hdiv : 3 ∣ N - 1 := by
      apply Nat.dvd_of_mod_eq_zero
      have h2 : 2 ^ α % 3 = 2 := extension_two_pow_mod_three_of_odd hαodd
      have h5 : 5 ^ β % 3 = 2 := by
        simpa [Nat.pow_mod] using extension_two_pow_mod_three_of_odd hβodd
      dsimp [N]
      norm_num [Nat.mul_mod, h2, h5]
    have hqmul : q * 3 = N - 1 := by
      rw [hqform]
      exact Nat.div_mul_cancel hdiv
    have hN1 : 1 ≤ N := by
      dsimp [N]
      positivity
    dsimp [N] at hqmul hN1 ⊢
    omega
  have hweighted := extension4_exponents_weighted_le hfac hqX
  exact ⟨α, β,
    (mem_extension4CandidatePairs_iff X α β).2
      ⟨hα, hβ, hαodd, hβodd, hcop, hweighted⟩,
    hqform⟩

end PrimeGPF
