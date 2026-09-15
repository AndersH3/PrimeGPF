import PrimeGPF.Extension7Finite
import PrimeGPF.PrimeAP

/-!
# Extension 7: collision density zero

The finite collision estimate from `Extension7Finite` is combined with the
already-formalized polylogarithmic smooth-count bound and the now-unconditional
PNT-in-arithmetic-progressions input.
-/
namespace PrimeGPF
open Claims Filter
open scoped Topology

/-- Smooth counts are monotone in their cutoff. -/
theorem smoothCount_mono_cutoff {r x y : ℕ} (hxy : x ≤ y) :
    Claims.smoothCount r x ≤ Claims.smoothCount r y := by
  classical
  unfold Claims.smoothCount
  apply Finset.card_le_card
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  refine ⟨?_, hn'.2⟩
  have hnx := Finset.mem_range.mp hn'.1
  apply Finset.mem_range.mpr
  omega

/-- For fixed anchor, the shifted linear cutoff is eventually below the
quadratic cutoff already handled in `Density.lean`. -/
theorem eventually_shift_le_succ_sq (a : ℕ) :
    ∀ᶠ n : ℕ in atTop, n + a + 1 ≤ (n + 1) * (n + 1) := by
  filter_upwards [eventually_ge_atTop a] with n hn
  nlinarith

/-- Equation (13): additive--multiplicative collision inputs have relative
prime density zero. -/
theorem extension7_collision_density_zero {a : ℕ} (ha : Nat.Prime a) :
    Tendsto
      (fun X : ℕ =>
        (extension7CollisionCount a X : ℝ) /
          (Claims.primeCount X : ℝ))
      atTop (nhds 0) := by
  let R := gpf (a ^ 2 + a - 1)
  let C : ℝ := Claims.primeCount R
  let H : PrimeAPInput := proof_primeAP_dependency

  have hconst0 :
      Tendsto
        (fun X : ℕ => C / (Claims.primeCount X : ℝ))
        atTop (nhds 0) := by
    have hbase := H.tendsto_log_pow_div_primeCount 0
    have hmul := Tendsto.const_mul C hbase
    simpa [C] using hmul

  have hsmooth0 :
      Tendsto
        (fun X : ℕ =>
          (Claims.smoothCount R ((X + 1) * (X + 1)) : ℝ) /
            (Claims.primeCount X : ℝ))
        atTop (nhds 0) := by
    exact H.tendsto_smoothCount_succ_sq_div_primeCount R

  have hmajor :
      Tendsto
        (fun X : ℕ =>
          C / (Claims.primeCount X : ℝ) +
          (Claims.smoothCount R ((X + 1) * (X + 1)) : ℝ) /
            (Claims.primeCount X : ℝ))
        atTop (nhds 0) := by
    simpa using hconst0.add hsmooth0

  apply squeeze_zero'
  · exact Eventually.of_forall (fun X => by positivity)
  · filter_upwards [eventually_shift_le_succ_sq a] with X hshift
    have hfinite := extension7_collisionCount_le_primeCount_add_smoothCount ha
    have hsmono :
        Claims.smoothCount R (X + a + 1) ≤
          Claims.smoothCount R ((X + 1) * (X + 1)) := by
      exact smoothCount_mono_cutoff hshift
    have hnum :
        extension7CollisionCount a X ≤
          Claims.primeCount R +
            Claims.smoothCount R ((X + 1) * (X + 1)) := by
      dsimp [R] at hfinite ⊢
      exact hfinite.trans (Nat.add_le_add_left hsmono _)
    have hnumR :
        (extension7CollisionCount a X : ℝ) ≤
          (Claims.primeCount R : ℝ) +
            (Claims.smoothCount R ((X + 1) * (X + 1)) : ℝ) := by
      exact_mod_cast hnum
    have hden : 0 ≤ (Claims.primeCount X : ℝ) := by positivity
    calc
      (extension7CollisionCount a X : ℝ) /
          (Claims.primeCount X : ℝ)
        ≤ ((Claims.primeCount R : ℝ) +
            (Claims.smoothCount R ((X + 1) * (X + 1)) : ℝ)) /
            (Claims.primeCount X : ℝ) :=
          div_le_div_of_nonneg_right hnumR hden
      _ = C / (Claims.primeCount X : ℝ) +
          (Claims.smoothCount R ((X + 1) * (X + 1)) : ℝ) /
            (Claims.primeCount X : ℝ) := by
          dsimp [C]
          ring
  · exact hmajor

end PrimeGPF
