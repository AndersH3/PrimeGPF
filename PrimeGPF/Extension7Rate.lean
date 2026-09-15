import PrimeGPF.Extension7Finite
import PrimeGPF.ExtensionPrimeCount
import Mathlib

/-!
# Extension 7: prime-relative collision rate

The sharp leading simplex coefficient in equation (12) requires the separate
lattice-counting theorem.  The rate in equation (13), however, already follows
from the correctly dimensioned polylogarithmic bound proved in
`Extension7Finite` together with the prime number theorem.
-/
namespace PrimeGPF

open Filter Asymptotics
open scoped Topology

/-- Equation (13): for a fixed prime anchor, the additive--multiplicative
collision proportion among primes is
`O((log X)^(d_a+1) / X)`, where `d_a` is the exact restricted-support
dimension from the report. -/
theorem extension7_collision_prime_ratio_isBigO
    {a : ℕ} (ha : Nat.Prime a) :
    (fun X : ℕ =>
      (extension7CollisionCount a X : ℝ) /
        (Claims.primeCount X : ℝ)) =O[atTop]
    (fun X : ℕ =>
      (Real.log (X : ℝ)) ^
          (extension1AllowedPrimeCount a (gpf (a ^ 2 + a - 1)) + 1) /
        (X : ℝ)) := by
  let R : ℕ := gpf (a ^ 2 + a - 1)
  let d : ℕ := extension1AllowedPrimeCount a R
  let B : ℝ := Claims.primeCount R
  let K : ℝ := (2 / Real.log 2) ^ d
  let C : ℝ := 2 * (B + K * (2 : ℝ) ^ d)

  have hpntEventually :
      ∀ᶠ X : ℕ in atTop,
        (1 / 2 : ℝ) ≤
          (Claims.primeCount X : ℝ) * Real.log (X : ℝ) / (X : ℝ) := by
    have h := extension_primeCount_log_limit.eventually
      (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
    exact h.mono fun X hX => hX.le

  have hlogTop :
      Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogEventually :
      ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (X : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop (1 : ℝ))

  apply IsBigO.of_bound C
  filter_upwards
    [hpntEventually, hlogEventually, eventually_ge_atTop (a + 2)]
      with X hpnt hlog1 hXa

  have hX2 : 2 ≤ X := by omega
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hlogpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))

  have hpcNat : 0 < Claims.primeCount X := by
    classical
    unfold Claims.primeCount
    apply Finset.card_pos.mpr
    refine ⟨2, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩
  have hpc : 0 < (Claims.primeCount X : ℝ) := by exact_mod_cast hpcNat

  have hshiftNat : X + a + 1 ≤ X * X := by
    nlinarith
  have hshiftReal0 :
      ((X + a + 1 : ℕ) : ℝ) ≤ ((X * X : ℕ) : ℝ) := by
    exact_mod_cast hshiftNat
  have hshiftReal :
      ((X + a + 1 : ℕ) : ℝ) ≤ (X : ℝ) ^ 2 := by
    simpa [Nat.cast_mul, pow_two] using hshiftReal0
  have hshiftPos : 0 < ((X + a + 1 : ℕ) : ℝ) := by positivity
  have hlogShift :
      Real.log ((X + a + 1 : ℕ) : ℝ) ≤
        2 * Real.log (X : ℝ) := by
    calc
      Real.log ((X + a + 1 : ℕ) : ℝ)
          ≤ Real.log ((X : ℝ) ^ 2) :=
        Real.log_le_log hshiftPos hshiftReal
      _ = 2 * Real.log (X : ℝ) := by
        rw [Real.log_pow]
        norm_num
  have hlogShift0 : 0 ≤ Real.log ((X + a + 1 : ℕ) : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ X + a + 1 by omega))
  have hpowShift :
      (Real.log ((X + a + 1 : ℕ) : ℝ)) ^ d ≤
        ((2 : ℝ) * Real.log (X : ℝ)) ^ d :=
    pow_le_pow_left₀ hlogShift0 hlogShift d

  have hfinite := extension7_collisionCount_real_le_polylog
    (a := a) (X := X) ha (by omega)
  have hfinite' :
      (extension7CollisionCount a X : ℝ) ≤
        B + K * (Real.log ((X + a + 1 : ℕ) : ℝ)) ^ d := by
    simpa [R, d, B, K, Nat.add_assoc] using hfinite

  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  have hpowShift' :
      K * (Real.log ((X + a + 1 : ℕ) : ℝ)) ^ d ≤
        K * ((2 : ℝ) * Real.log (X : ℝ)) ^ d :=
    mul_le_mul_of_nonneg_left hpowShift hK0
  have hlogpow1 : 1 ≤ (Real.log (X : ℝ)) ^ d := by
    simpa using (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hlog1 d)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hBmul : B ≤ B * (Real.log (X : ℝ)) ^ d := by
    calc
      B = B * 1 := by ring
      _ ≤ B * (Real.log (X : ℝ)) ^ d :=
        mul_le_mul_of_nonneg_left hlogpow1 hB0

  have hnum :
      (extension7CollisionCount a X : ℝ) ≤
        (B + K * (2 : ℝ) ^ d) * (Real.log (X : ℝ)) ^ d := by
    calc
      (extension7CollisionCount a X : ℝ)
          ≤ B + K * (Real.log ((X + a + 1 : ℕ) : ℝ)) ^ d := hfinite'
      _ ≤ B + K * ((2 : ℝ) * Real.log (X : ℝ)) ^ d :=
        add_le_add_left hpowShift' B
      _ = B + K * ((2 : ℝ) ^ d * (Real.log (X : ℝ)) ^ d) := by
        rw [mul_pow]
      _ ≤ B * (Real.log (X : ℝ)) ^ d +
            K * ((2 : ℝ) ^ d * (Real.log (X : ℝ)) ^ d) :=
        add_le_add_right hBmul _
      _ = (B + K * (2 : ℝ) ^ d) *
            (Real.log (X : ℝ)) ^ d := by ring

  have hpntMul :
      (X : ℝ) ≤
        2 * (Claims.primeCount X : ℝ) * Real.log (X : ℝ) := by
    have hhalf := (le_div_iff₀ hXpos).mp hpnt
    nlinarith

  have hratio :
      (extension7CollisionCount a X : ℝ) /
          (Claims.primeCount X : ℝ) ≤
        (2 * (extension7CollisionCount a X : ℝ) *
            Real.log (X : ℝ)) / (X : ℝ) := by
    apply (div_le_div_iff₀ hpc hXpos).2
    have hmul := mul_le_mul_of_nonneg_left hpntMul
      (show 0 ≤ (extension7CollisionCount a X : ℝ) by positivity)
    calc
      (extension7CollisionCount a X : ℝ) * (X : ℝ)
          ≤ (extension7CollisionCount a X : ℝ) *
              (2 * (Claims.primeCount X : ℝ) * Real.log (X : ℝ)) := hmul
      _ = (2 * (extension7CollisionCount a X : ℝ) * Real.log (X : ℝ)) *
              (Claims.primeCount X : ℝ) := by ring

  have hnumLog :
      2 * (extension7CollisionCount a X : ℝ) * Real.log (X : ℝ) ≤
        2 * (B + K * (2 : ℝ) ^ d) *
          (Real.log (X : ℝ)) ^ (d + 1) := by
    have hmul := mul_le_mul_of_nonneg_right hnum hlogpos.le
    have hmul2 := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 2)
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hmul2

  have hpoint :
      (extension7CollisionCount a X : ℝ) /
          (Claims.primeCount X : ℝ) ≤
        C * ((Real.log (X : ℝ)) ^ (d + 1) / (X : ℝ)) := by
    calc
      (extension7CollisionCount a X : ℝ) /
            (Claims.primeCount X : ℝ)
          ≤ (2 * (extension7CollisionCount a X : ℝ) *
              Real.log (X : ℝ)) / (X : ℝ) := hratio
      _ ≤ (2 * (B + K * (2 : ℝ) ^ d) *
              (Real.log (X : ℝ)) ^ (d + 1)) / (X : ℝ) :=
        div_le_div_of_nonneg_right hnumLog hXpos.le
      _ = C * ((Real.log (X : ℝ)) ^ (d + 1) / (X : ℝ)) := by
        dsimp [C]
        ring

  have hleft0 :
      0 ≤ (extension7CollisionCount a X : ℝ) /
        (Claims.primeCount X : ℝ) := by positivity
  have hright0 :
      0 ≤ (Real.log (X : ℝ)) ^ (d + 1) / (X : ℝ) := by positivity
  dsimp [R, d] at hpoint ⊢
  simpa only [Real.norm_eq_abs, abs_of_nonneg hleft0,
    abs_of_nonneg hright0] using hpoint

end PrimeGPF
