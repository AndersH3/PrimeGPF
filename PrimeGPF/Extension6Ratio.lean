import PrimeGPF.Extension6Cutoff

/-!
# Extension 6: asymptotic image ratio

This file closes the passage from the finite image bound (equation (9)) to the
upper-density statement (equation (10)).  We first prove a robust filter form:
for every positive epsilon, the normalized image cardinality is eventually at
most `2^{-k} + epsilon`, and then package it as the literal limsup inequality
stated in the report.
-/
namespace PrimeGPF

open Filter
open scoped Topology

/-- The project's prime-counting function tends to infinity. -/
theorem claims_primeCount_tendsto_atTop :
    Tendsto Claims.primeCount atTop atTop := by
  have h := Nat.tensto_primeCounting
  apply h.congr'
  filter_upwards [] with N
  exact (claims_primeCount_eq_primeCounting N).symm

/-- The reciprocal of the real-valued prime count tends to zero. -/
theorem claims_primeCount_recip_tendsto_zero :
    Tendsto (fun X : ℕ => (1 : ℝ) / (Claims.primeCount X : ℝ))
      atTop (𝓝 0) := by
  have hreal :
      Tendsto (fun X : ℕ => (Claims.primeCount X : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp claims_primeCount_tendsto_atTop
  simpa [one_div] using tendsto_inv_atTop_zero.comp hreal

/-- Equation (10), in epsilon/eventual form.  For every fixed iterate depth
`k`, the proportion of prime outputs up to `X` lying in the `k`-fold
exponential image is eventually at most `2^{-k} + ε`. -/
theorem extension6_image_ratio_eventually_le
    {a k : ℕ} (ha : Nat.Prime a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      ((iteratedExpValuesUpTo a k X).card : ℝ) /
          (Claims.primeCount X : ℝ) ≤
        (1 : ℝ) / (2 ^ k : ℕ) + ε := by
  let m : ℕ := 2 ^ k
  let C : ℕ → ℕ := extension6Cutoff m
  have hm : 0 < m := by
    dsimp [m]
    positivity
  have hCtop : Tendsto C atTop atTop := by
    simpa [C] using extension6Cutoff_tendsto_atTop m hm
  have hratio :
      Tendsto
        (fun X : ℕ =>
          (Claims.primeCount (C X) : ℝ) /
            (Claims.primeCount (m * C X) : ℝ))
        atTop (𝓝 ((1 : ℝ) / m)) := by
    simpa [C] using (extension_primeCount_mul_ratio m hm).comp hCtop
  have hinv := claims_primeCount_recip_tendsto_zero
  have hupperLimit :
      Tendsto
        (fun X : ℕ =>
          (Claims.primeCount (C X) : ℝ) /
              (Claims.primeCount (m * C X) : ℝ) +
            (1 : ℝ) / (Claims.primeCount X : ℝ))
        atTop (𝓝 ((1 : ℝ) / m)) := by
    simpa using hratio.add hinv
  have hlt : (1 : ℝ) / m < (1 : ℝ) / m + ε :=
    lt_add_of_pos_right _ hε
  have heventUpper :
      ∀ᶠ X : ℕ in atTop,
        (Claims.primeCount (C X) : ℝ) /
              (Claims.primeCount (m * C X) : ℝ) +
            (1 : ℝ) / (Claims.primeCount X : ℝ) <
          (1 : ℝ) / m + ε :=
    hupperLimit.eventually (Iio_mem_nhds hlt)
  filter_upwards
    [heventUpper, hCtop.eventually (eventually_ge_atTop (2 : ℕ)),
      eventually_ge_atTop (2 : ℕ)] with X hUpper hC2 hX2
  have hmC2 : 2 ≤ m * C X := by
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm)
    calc
      2 ≤ C X := hC2
      _ = 1 * C X := by simp
      _ ≤ m * C X := Nat.mul_le_mul_right (C X) hm1
  have hpcX : 0 < Claims.primeCount X := claims_primeCount_pos_of_two_le hX2
  have hpcmC : 0 < Claims.primeCount (m * C X) :=
    claims_primeCount_pos_of_two_le hmC2
  have hmulLe : m * C X ≤ X := by
    simpa [C] using extension6Cutoff_mul_le m X hm
  have hpcmonoNat : Claims.primeCount (m * C X) ≤ Claims.primeCount X := by
    rw [claims_primeCount_eq_primeCounting, claims_primeCount_eq_primeCounting]
    exact Nat.monotone_primeCounting hmulLe
  have hpcmono :
      (Claims.primeCount (m * C X) : ℝ) ≤ (Claims.primeCount X : ℝ) := by
    exact_mod_cast hpcmonoNat
  have hratioLe :
      (Claims.primeCount (C X) : ℝ) / (Claims.primeCount X : ℝ) ≤
        (Claims.primeCount (C X) : ℝ) /
          (Claims.primeCount (m * C X) : ℝ) := by
    apply (div_le_div_iff₀ (by exact_mod_cast hpcX) (by exact_mod_cast hpcmC)).2
    exact mul_le_mul_of_nonneg_left hpcmono (Nat.cast_nonneg _)
  have hfiniteNat := extension6_image_card_bound (a := a) (k := k) (X := X) ha
  have hextra : (if a = 2 then 1 else 0) ≤ 1 := by
    split <;> omega
  have hfiniteNat' :
      (iteratedExpValuesUpTo a k X).card ≤
        Claims.primeCount (C X) + 1 := by
    have h := hfiniteNat.trans
      (Nat.add_le_add_left hextra
        (Claims.primeCount ((X + 1) / 2 ^ k - 1)))
    simpa [C, m] using h
  have hfinite :
      ((iteratedExpValuesUpTo a k X).card : ℝ) ≤
        (Claims.primeCount (C X) : ℝ) + 1 := by
    exact_mod_cast hfiniteNat'
  have hdiv :
      ((iteratedExpValuesUpTo a k X).card : ℝ) /
          (Claims.primeCount X : ℝ) ≤
        ((Claims.primeCount (C X) : ℝ) + 1) /
          (Claims.primeCount X : ℝ) :=
    div_le_div_of_nonneg_right hfinite (by exact_mod_cast hpcX.le)
  calc
    ((iteratedExpValuesUpTo a k X).card : ℝ) /
          (Claims.primeCount X : ℝ)
        ≤ ((Claims.primeCount (C X) : ℝ) + 1) /
            (Claims.primeCount X : ℝ) := hdiv
    _ = (Claims.primeCount (C X) : ℝ) /
            (Claims.primeCount X : ℝ) +
          (1 : ℝ) / (Claims.primeCount X : ℝ) := by rw [add_div]
    _ ≤ (Claims.primeCount (C X) : ℝ) /
            (Claims.primeCount (m * C X) : ℝ) +
          (1 : ℝ) / (Claims.primeCount X : ℝ) := by
            exact add_le_add_right hratioLe _
    _ < (1 : ℝ) / m + ε := hUpper
    _ = (1 : ℝ) / (2 ^ k : ℕ) + ε := by rfl

/-- Equation (10) exactly as a limsup bound. -/
theorem extension6_image_ratio_limsup_le
    {a k : ℕ} (ha : Nat.Prime a) :
    limsup
      (fun X : ℕ =>
        ((iteratedExpValuesUpTo a k X).card : ℝ) /
          (Claims.primeCount X : ℝ))
      atTop ≤ (1 : ℝ) / (2 ^ k : ℕ) := by
  let u : ℕ → ℝ := fun X =>
    ((iteratedExpValuesUpTo a k X).card : ℝ) /
      (Claims.primeCount X : ℝ)
  have hcob : IsCoboundedUnder (· ≤ ·) atTop u := by
    exact isCoboundedUnder_le_of_le atTop (fun X => by
      dsimp [u]
      positivity)
  have hbound : IsBoundedUnder (· ≤ ·) atTop u := by
    apply isBoundedUnder_of_eventually_le
    simpa [u] using
      (extension6_image_ratio_eventually_le (a := a) (k := k) ha
        (ε := (1 : ℝ)) (by norm_num))
  rw [limsup_le_iff' hcob hbound]
  intro y hy
  have hε : 0 < y - (1 : ℝ) / (2 ^ k : ℕ) := sub_pos.mpr hy
  have hev :=
    extension6_image_ratio_eventually_le (a := a) (k := k) ha hε
  filter_upwards [hev] with X hX
  dsimp [u]
  calc
    ((iteratedExpValuesUpTo a k X).card : ℝ) /
          (Claims.primeCount X : ℝ)
        ≤ (1 : ℝ) / (2 ^ k : ℕ) +
            (y - (1 : ℝ) / (2 ^ k : ℕ)) := hX
    _ = y := by ring

end PrimeGPF
