import PrimeGPF.ExtensionPrimeCount
import PrimeGPF.Extensions
import Mathlib

/-!
# Extension 6: prime-count scale asymptotics

This file supplies the PNT scaling step needed to pass from the finite image
bound in equation (9) to the density statement in equation (10).
-/
namespace PrimeGPF
open Filter Real
open scoped Topology

/-- The project's prime-count function is positive once the cutoff contains 2. -/
lemma claims_primeCount_pos_of_two_le {N : ℕ} (hN : 2 ≤ N) :
    0 < Claims.primeCount N := by
  classical
  unfold Claims.primeCount
  apply Finset.card_pos.mpr
  refine ⟨2, ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩

/-- Multiplication by a fixed positive natural tends to infinity. -/
lemma tendsto_nat_mul_atTop (m : ℕ) (hm : 0 < m) :
    Tendsto (fun N : ℕ => m * N) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop b] with N hN
  have hm1 : 1 ≤ m := by omega
  calc
    b ≤ N := hN
    _ = 1 * N := by simp
    _ ≤ m * N := Nat.mul_le_mul_right N hm1

/-- For fixed positive `m`, `log(mN)/log(N) → 1`. -/
theorem extension_log_mul_ratio (m : ℕ) (hm : 0 < m) :
    Tendsto
      (fun N : ℕ => Real.log ((m * N : ℕ) : ℝ) / Real.log (N : ℝ))
      atTop (𝓝 1) := by
  have hlogTop :
      Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv :
      Tendsto (fun N : ℕ => (Real.log (N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlogTop
  have hsmall :
      Tendsto
        (fun N : ℕ => Real.log (m : ℝ) * (Real.log (N : ℝ))⁻¹)
        atTop (𝓝 0) := by
    simpa using hinv.const_mul (Real.log (m : ℝ))
  have hsum :
      Tendsto
        (fun N : ℕ => 1 + Real.log (m : ℝ) * (Real.log (N : ℝ))⁻¹)
        atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hsmall
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hNne : (N : ℝ) ≠ 0 := by positivity
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hcast : ((m * N : ℕ) : ℝ) = (m : ℝ) * (N : ℝ) := by norm_num
  rw [hcast, Real.log_mul hmne hNne]
  field_simp [hlogNpos.ne']
  ring

/-- Fixed-scale PNT ratio: for every positive natural `m`,
`π(N) / π(mN) → 1/m`. -/
theorem extension_primeCount_mul_ratio (m : ℕ) (hm : 0 < m) :
    Tendsto
      (fun N : ℕ =>
        (Claims.primeCount N : ℝ) / (Claims.primeCount (m * N) : ℝ))
      atTop (𝓝 ((1 : ℝ) / m)) := by
  let A : ℕ → ℝ := fun N =>
    (Claims.primeCount N : ℝ) * Real.log (N : ℝ) / (N : ℝ)
  have hA : Tendsto A atTop (𝓝 1) := by
    simpa [A] using extension_primeCount_log_limit
  have hmulTop := tendsto_nat_mul_atTop m hm
  have hAm : Tendsto (fun N : ℕ => A (m * N)) atTop (𝓝 1) :=
    hA.comp hmulTop
  have hquot :
      Tendsto (fun N : ℕ => A N / A (m * N)) atTop (𝓝 1) := by
    simpa using hA.div hAm (by norm_num : (1 : ℝ) ≠ 0)
  have hlog := extension_log_mul_ratio m hm
  have hprod :
      Tendsto
        (fun N : ℕ =>
          (A N / A (m * N)) *
            (Real.log ((m * N : ℕ) : ℝ) / Real.log (N : ℝ)))
        atTop (𝓝 1) := by
    simpa using hquot.mul hlog
  have hscaled :
      Tendsto
        (fun N : ℕ =>
          ((A N / A (m * N)) *
            (Real.log ((m * N : ℕ) : ℝ) / Real.log (N : ℝ))) / (m : ℝ))
        atTop (𝓝 ((1 : ℝ) / m)) := by
    simpa using hprod.div_const (m : ℝ)
  apply hscaled.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hm1 : 1 ≤ m := by omega
  have hNm : 2 ≤ m * N := by
    calc
      2 ≤ N := hN
      _ = 1 * N := by simp
      _ ≤ m * N := Nat.mul_le_mul_right N hm1
  have hpN : 0 < Claims.primeCount N := claims_primeCount_pos_of_two_le hN
  have hpNm : 0 < Claims.primeCount (m * N) :=
    claims_primeCount_pos_of_two_le hNm
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hlogNm : Real.log ((m * N : ℕ) : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < m * N by omega))).ne'
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hpNR : (Claims.primeCount N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpN)
  have hpNmR : (Claims.primeCount (m * N) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpNm)
  have hlogMul : Real.log ((m : ℝ) * (N : ℝ)) ≠ 0 := by
    simpa only [Nat.cast_mul] using hlogNm
  dsimp [A]
  simp only [Nat.cast_mul]
  field_simp [hpNR, hpNmR, hlogN, hlogMul, hN0, hm0]
  ring

end PrimeGPF
