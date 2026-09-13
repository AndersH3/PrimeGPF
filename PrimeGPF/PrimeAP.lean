import PrimeGPF.PrimeAPAnalytic
import PrimeGPF.WeightedCounting
import PrimeGPF.Density

namespace PrimeGPF
open Claims Filter Finset Real ArithmeticFunction
open scoped Topology

/-- The ordinary prime count in a reduced residue class, normalized by log N / N. -/
theorem apCount_log_limit {r c : ℕ} (hr : Nat.Prime r) (hc0 : 0 < c) (hcr : c < r) :
    Tendsto (fun N => (apCount r c N : ℝ) * Real.log N / N)
      atTop (𝓝 ((r.totient : ℝ)⁻¹)) := by
  classical
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  have hc : IsUnit (c : ZMod r) := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hd := (ZMod.natCast_zmod_eq_zero_iff_dvd c r).mp hz
    have := Nat.mod_eq_zero_of_dvd hd
    rw [Nat.mod_eq_of_lt hcr] at this
    omega
  let S : ℕ → Finset ℕ := fun N => (Finset.range (N + 1)).filter
    (fun n => Nat.Prime n ∧ n % r = c % r)
  have he (N : ℕ) : (∑ n ∈ S N, Real.log n) =
      Analytic.theta (vonMangoldt.residueClass (c : ZMod r)) N := by
    simp only [S, Analytic.theta, Analytic.nat_Iic_eq_range, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : Nat.Prime n
    · simp only [hp, true_and, if_true, vonMangoldt.residueClass, Set.indicator_apply,
        Set.mem_setOf_eq, ZMod.natCast_eq_natCast_iff', vonMangoldt_apply_prime hp]
    · simp [hp]
  have hweighted : Tendsto (fun N => (∑ n ∈ S N, Real.log n) / N)
      atTop (𝓝 ((r.totient : ℝ)⁻¹)) := by
    simpa only [he] using Analytic.theta_AP_limit hr.pos (c : ZMod r) hc
  have hA : (0 : ℝ) < (r.totient : ℝ)⁻¹ := by
    apply inv_pos.mpr
    exact_mod_cast Nat.totient_pos.mpr hr.pos
  have hS (N n : ℕ) (hn : n ∈ S N) : 1 ≤ n ∧ n ≤ N := by
    obtain ⟨hn, hp, _⟩ := Finset.mem_filter.mp hn
    exact ⟨hp.one_lt.le, by have := Finset.mem_range.mp hn; omega⟩
  exact Analytic.counting_limit_of_weighted hA hS hweighted

/-- PNT in arithmetic progressions in precisely the normalization used by the project. -/
theorem proof_primeAP_dependency : PrimeAPInput := by
  intro r c hr _hr2 hc0 hcr
  have hh := (apCount_log_limit hr hc0 hcr).const_mul ((r : ℝ) - 1)
  have ht : ((r.totient : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.totient_prime hr, Nat.cast_sub hr.one_lt.le, Nat.cast_one]
  have hd : (r : ℝ) - 1 ≠ 0 := by have := hr.two_le; norm_cast; omega
  have hlim : ((r : ℝ) - 1) * (r.totient : ℝ)⁻¹ = 1 := by
    rw [ht, mul_inv_cancel₀ hd]
  rw [hlim] at hh
  unfold APAsymptotic
  convert hh using 1
  ext N
  rw [div_div_eq_mul_div]
  ring

theorem proof_6_1 : t6_1 := proof_6_1_from_PNT_AP proof_primeAP_dependency
theorem proof_6_3 : t6_3 := proof_6_3_from_PNT_AP proof_primeAP_dependency

end PrimeGPF
