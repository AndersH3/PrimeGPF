import PrimeGPF.PrimeAP
import PrimeGPF.ExtensionPrimeCount

/-!
# Extension 6: ordinary prime-count normalization

The project already proves PNT in arithmetic progressions.  At modulus two,
the reduced residue class `1` contains exactly the odd primes, so total prime
count differs from that AP count by at most the single prime `2`.  This gives
the ordinary PNT normalization needed for the scale-ratio step in equation
(10).
-/
namespace PrimeGPF

open Claims Filter
open scoped Topology

/-- The total number of primes up to `N` exceeds the odd-prime count by at
most one. -/
theorem primeCount_le_apCount_two_one_add_one (N : ℕ) :
    Claims.primeCount N ≤ Claims.apCount 2 1 N + 1 := by
  classical
  let P := (Finset.range (N + 1)).filter Nat.Prime
  let A := (Finset.range (N + 1)).filter
    (fun q => Nat.Prime q ∧ q % 2 = 1)
  have hsub : P ⊆ insert 2 A := by
    intro q hqP
    have hqP' := Finset.mem_filter.mp hqP
    rcases hqP'.2.eq_two_or_odd with hq2 | hqodd
    · subst q
      simp
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_filter.mpr
      exact ⟨hqP'.1, hqP'.2, hqodd⟩
  have hc : P.card ≤ (insert 2 A).card := Finset.card_le_card hsub
  have hi : (insert 2 A).card ≤ A.card + 1 := by
    exact Finset.card_insert_le 2 A
  have hPA : P.card ≤ A.card + 1 := hc.trans hi
  simpa [Claims.primeCount, Claims.apCount, P, A] using hPA

/-- Ordinary PNT normalization for the project's prime-counting function:
`π(N) log N / N -> 1`. -/
theorem extension6_primeCount_log_limit :
    Tendsto
      (fun N : ℕ =>
        (Claims.primeCount N : ℝ) * Real.log (N : ℝ) / (N : ℝ))
      atTop (𝓝 1) := by
  have hap0 := apCount_log_limit
    (r := 2) (c := 1) (by norm_num) (by norm_num) (by norm_num)
  have hap :
      Tendsto
        (fun N : ℕ =>
          (Claims.apCount 2 1 N : ℝ) * Real.log (N : ℝ) / (N : ℝ))
        atTop (𝓝 1) := by
    simpa using hap0
  have hlog :
      Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ))
        atTop (𝓝 0) := by
    simpa using tendsto_log_pow_div_natCast_atTop 1
  have hupper :
      Tendsto
        (fun N : ℕ =>
          ((Claims.apCount 2 1 N : ℝ) + 1) *
              Real.log (N : ℝ) / (N : ℝ))
        atTop (𝓝 1) := by
    have hsum := hap.add hlog
    convert hsum using 1
    · ext N
      ring
    · norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hap hupper
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hlog0 : 0 ≤ Real.log (N : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    have hN0 : 0 ≤ (N : ℝ) := by positivity
    have hcount :
        (Claims.apCount 2 1 N : ℝ) ≤ (Claims.primeCount N : ℝ) := by
      exact_mod_cast apCount_le_primeCount 2 1 N
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcount hlog0) hN0
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hlog0 : 0 ≤ Real.log (N : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    have hN0 : 0 ≤ (N : ℝ) := by positivity
    have hcount :
        (Claims.primeCount N : ℝ) ≤ (Claims.apCount 2 1 N : ℝ) + 1 := by
      exact_mod_cast primeCount_le_apCount_two_one_add_one N
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcount hlog0) hN0

end PrimeGPF
