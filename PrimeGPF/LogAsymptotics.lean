import Mathlib

/-!
# Elementary logarithmic asymptotics

Small reusable limit lemmas for the extension-report asymptotics.  They are
kept independent of the prime number theorem so the sharp one-dimensional
fiber results do not need the heavier PNT dependency.
-/
namespace PrimeGPF

open Filter Real
open scoped Topology

/-- Multiplication by a fixed positive natural tends to infinity. -/
theorem fixed_nat_mul_tendsto_atTop (m : ℕ) (hm : 0 < m) :
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
theorem fixed_mul_log_ratio_tendsto_one (m : ℕ) (hm : 0 < m) :
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

/-- For fixed `c`, adding `c` does not change the leading logarithm:
`log(N+c)/log(N) → 1`. -/
theorem fixed_add_log_ratio_tendsto_one (c : ℕ) :
    Tendsto
      (fun N : ℕ => Real.log ((N + c : ℕ) : ℝ) / Real.log (N : ℝ))
      atTop (𝓝 1) := by
  have hupper := fixed_mul_log_ratio_tendsto_one (c + 1) (by omega)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    hupper
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hlogNpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hNat : N ≤ N + c := by omega
    have hReal : (N : ℝ) ≤ ((N + c : ℕ) : ℝ) := by exact_mod_cast hNat
    have hlog : Real.log (N : ℝ) ≤ Real.log ((N + c : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) hReal
    exact (le_div_iff₀ hlogNpos).2 (by simpa using hlog)
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hlogNpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hN1 : 1 ≤ N := by omega
    have hcMul : c ≤ c * N := by
      calc
        c = c * 1 := by simp
        _ ≤ c * N := Nat.mul_le_mul_left c hN1
    have hNat : N + c ≤ (c + 1) * N := by
      calc
        N + c ≤ N + c * N := Nat.add_le_add_left hcMul N
        _ = (c + 1) * N := by ring
    have hReal :
        ((N + c : ℕ) : ℝ) ≤ (((c + 1) * N : ℕ) : ℝ) := by
      exact_mod_cast hNat
    have hlog :
        Real.log ((N + c : ℕ) : ℝ) ≤
          Real.log (((c + 1) * N : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) hReal
    exact (div_le_div_iff_of_pos_right hlogNpos).2 hlog

end PrimeGPF
