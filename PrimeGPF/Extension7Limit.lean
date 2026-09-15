import PrimeGPF.Extension7Density
import Mathlib

/-!
# Extension 7: analytic density-zero conclusion

The finite collision estimate is already formalized in `Extension7Finite`.
This file supplies the remaining elementary analytic step: every fixed power
of a logarithm is little-o of the identity, hence the collision count has
natural density zero among all positive integers.
-/
namespace PrimeGPF

open Filter Topology

/-- A fixed power of the logarithm of a fixed translate of `X`, divided by
`X`, tends to zero along the natural numbers. -/
theorem log_power_nat_shift_div_self_tendsto_zero (c d : ℕ) :
    Tendsto
      (fun X : ℕ =>
        (Real.log (((X + c : ℕ) : ℝ))) ^ d / (X : ℝ))
      atTop (𝓝 0) := by
  have hshift :
      Tendsto (fun X : ℕ => (((X + c : ℕ) : ℝ))) atTop atTop := by
    simpa [Nat.cast_add] using
      (tendsto_atTop_add_const_right atTop (c : ℝ)
        tendsto_natCast_atTop_atTop)
  have hsmall :
      (fun X : ℕ => (Real.log (((X + c : ℕ) : ℝ))) ^ d) =o[atTop]
        (fun X : ℕ => (((X + c : ℕ) : ℝ))) :=
    (Real.isLittleO_pow_log_id_atTop (n := d)).comp_tendsto hshift
  have hshiftRatio :
      Tendsto
        (fun X : ℕ =>
          (Real.log (((X + c : ℕ) : ℝ))) ^ d /
            (((X + c : ℕ) : ℝ)))
        atTop (𝓝 0) :=
    hsmall.tendsto_div_nhds_zero
  have hconstDiv :
      Tendsto (fun X : ℕ => (c : ℝ) / (X : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hratioOne :
      Tendsto (fun X : ℕ => (1 : ℝ) + (c : ℝ) / (X : ℝ))
        atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hconstDiv
  have hratio :
      Tendsto (fun X : ℕ => (((X + c : ℕ) : ℝ)) / (X : ℝ))
        atTop (𝓝 1) := by
    refine hratioOne.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
    have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hX)
    rw [Nat.cast_add, add_div, div_self hX0]
  have hprod := hshiftRatio.mul hratio
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
  have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hX)
  have hshift0 : (((X + c : ℕ) : ℝ)) ≠ 0 := by
    positivity
  field_simp [hX0, hshift0]

/-- The additive-multiplicative collision set for a fixed prime anchor has
natural density zero.  This is the analytic density conclusion behind
extension 7; the sharper leading simplex constant remains separate. -/
theorem extension7_collision_density_tendsto_zero
    {a : ℕ} (ha : Nat.Prime a) :
    Tendsto
      (fun X : ℕ => (extension7CollisionCount a X : ℝ) / (X : ℝ))
      atTop (𝓝 0) := by
  let R := gpf (a ^ 2 + a - 1)
  let d := extension1AllowedPrimeCount a R
  let B : ℝ := Claims.primeCount R
  let C : ℝ := (2 / Real.log 2) ^ d

  have hB : Tendsto (fun X : ℕ => B / (X : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlog :
      Tendsto
        (fun X : ℕ =>
          (Real.log (((X + (a + 1) : ℕ) : ℝ))) ^ d / (X : ℝ))
        atTop (𝓝 0) :=
    log_power_nat_shift_div_self_tendsto_zero (a + 1) d
  have hClog :
      Tendsto
        (fun X : ℕ =>
          C * ((Real.log (((X + (a + 1) : ℕ) : ℝ))) ^ d / (X : ℝ)))
        atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hlog
  have hupper :
      Tendsto
        (fun X : ℕ =>
          B / (X : ℝ) +
            C * ((Real.log (((X + (a + 1) : ℕ) : ℝ))) ^ d / (X : ℝ)))
        atTop (𝓝 0) := by
    simpa using hB.add hClog

  refine squeeze_zero' ?_ ?_ hupper
  · exact Eventually.of_forall fun X =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
    have hXpos : 0 < (X : ℝ) := by exact_mod_cast hX
    have hfinite := extension7_collisionCount_real_le_polylog
      (a := a) (X := X) ha (by
        have ha2 := ha.two_le
        omega)
    have hdiv := div_le_div_of_nonneg_right hfinite (le_of_lt hXpos)
    dsimp [R, d, B, C] at hdiv ⊢
    calc
      (extension7CollisionCount a X : ℝ) / (X : ℝ)
          ≤ ((Claims.primeCount (gpf (a ^ 2 + a - 1)) : ℝ) +
              (2 / Real.log 2) ^
                  extension1AllowedPrimeCount a (gpf (a ^ 2 + a - 1)) *
                (Real.log (((X + a + 1 : ℕ) : ℝ))) ^
                  extension1AllowedPrimeCount a (gpf (a ^ 2 + a - 1))) /
              (X : ℝ) := hdiv
      _ = (Claims.primeCount (gpf (a ^ 2 + a - 1)) : ℝ) / (X : ℝ) +
            (2 / Real.log 2) ^
                extension1AllowedPrimeCount a (gpf (a ^ 2 + a - 1)) *
              ((Real.log (((X + (a + 1) : ℕ) : ℝ))) ^
                  extension1AllowedPrimeCount a (gpf (a ^ 2 + a - 1)) /
                (X : ℝ)) := by
            rw [add_div]
            simp only [Nat.add_assoc]
            ring

end PrimeGPF
