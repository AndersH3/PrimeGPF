import PrimeGPF.WeightedCounting
import PrimeGPF.PNT.Consequences
import PrimeGPF.Statements

/-!
# Prime-count normalization for extension asymptotics

This packages the already-formalized PNT into the exact `Claims.primeCount`
convention used by the extension report.
-/
namespace PrimeGPF
open Filter Finset Real Asymptotics
open scoped Topology

noncomputable def extensionPrimeSet (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (N + 1)).filter Nat.Prime

lemma extensionPrimeSet_eq_Iic (N : ℕ) :
    extensionPrimeSet N = (Finset.Iic N).filter Nat.Prime := by
  classical
  ext n
  simp [extensionPrimeSet]
  omega

lemma extensionPrimeSet_card (N : ℕ) :
    (extensionPrimeSet N).card = Claims.primeCount N := by
  simp [extensionPrimeSet, Claims.primeCount]

/-- The Chebyshev/PNT theorem restricted to natural cutoffs. -/
theorem extension_prime_weighted_limit :
    Tendsto
      (fun N : ℕ =>
        (∑ p ∈ extensionPrimeSet N, Real.log p) / (N : ℝ))
      atTop (𝓝 1) := by
  have heq := chebyshev_asymptotic.comp_tendsto
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hne : ∀ᶠ N : ℕ in atTop, ((N : ℝ) : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact_mod_cast (show N ≠ 0 by omega)
  rw [isEquivalent_iff_tendsto_one hne] at heq
  apply heq.congr'
  filter_upwards with N
  have hfloor : ⌊((N : ℝ))⌋₊ = N := by simp
  rw [Function.comp_apply, Function.comp_apply, hfloor]
  rw [extensionPrimeSet_eq_Iic]

/-- PNT in the exact normalization used throughout the extension report. -/
theorem extension_primeCount_log_limit :
    Tendsto
      (fun N : ℕ =>
        (Claims.primeCount N : ℝ) * Real.log (N : ℝ) / (N : ℝ))
      atTop (𝓝 1) := by
  let S : ℕ → Finset ℕ := extensionPrimeSet
  have hS : ∀ N n, n ∈ S N → 1 ≤ n ∧ n ≤ N := by
    intro N n hn
    have hn' : n ∈ extensionPrimeSet N := hn
    have hm := Finset.mem_filter.mp hn'
    have hr := Finset.mem_range.mp hm.1
    exact ⟨hm.2.one_lt.le, by omega⟩
  have hw : Tendsto
      (fun N => (∑ n ∈ S N, Real.log n) / (N : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
    simpa [S] using extension_prime_weighted_limit
  have hc := PrimeGPF.Analytic.counting_limit_of_weighted
    (S := S) (A := (1 : ℝ)) (by norm_num) hS hw
  simpa [S, extensionPrimeSet_card] using hc

end PrimeGPF
