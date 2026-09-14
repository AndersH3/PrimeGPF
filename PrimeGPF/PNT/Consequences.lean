import PrimeGPF.PNT.Wiener
import PrimeGPF.PNT.Mathlib.Analysis.SpecialFunctions.Log.Basic
import PrimeGPF.PNT.Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

set_option lang.lemmaCmd true

open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory

lemma Set.Ico_subset_Ico_of_Icc_subset_Icc {a b c d : ℝ} (h : Set.Icc a b ⊆ Set.Icc c d) :
    Set.Ico a b ⊆ Set.Ico c d := by
  intro z hz
  have hz' := Set.Ico_subset_Icc_self.trans h hz
  have hcd : c ≤ d := by
    contrapose! hz'
    rw [Icc_eq_empty_of_lt hz']
    exact not_mem_empty _
  simp only [mem_Ico, mem_Icc] at *
  refine ⟨hz'.1, hz'.2.eq_or_lt.resolve_left ?_⟩
  rintro rfl
  apply hz.2.not_le
  have := h <| right_mem_Icc.mpr (hz.1.trans hz.2.le)
  simp only [mem_Icc] at this
  exact this.2

-- @[simps]
-- def ArithmeticFunction.primeCounting : ArithmeticFunction ℝ where
--   toFun x := Nat.primeCounting ⌊x⌋₊
--   map_zero' := by simp [Nat.primeCounting_zero]

-- AkraBazzi.lean
lemma deriv_smoothingFn' {x : ℝ} (hx_pos : 0 < x) (hx : x ≠ 1) : deriv (fun x => (log x)⁻¹) x = -x⁻¹ / (log x ^ 2) := by
  have : log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx_pos hx
  rw [deriv_inv''] <;> aesop

lemma deriv_smoothingFn {x : ℝ} (hx : 1 < x) : deriv (fun x => (log x)⁻¹) x = -x⁻¹ / (log x ^ 2) :=
  deriv_smoothingFn' (by positivity) (ne_of_gt hx)

noncomputable def th (x : ℝ) := ∑ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime, Real.log p

lemma th_def' (x : ℝ) :
    th x = ∑ n ∈ Icc 0 ⌊x⌋₊, Set.indicator (setOf Nat.Prime) (fun n => log n) n := by
  unfold th
  rw [sum_filter]
  refine sum_congr rfl fun n _ => ?_
  simp [Set.indicator_apply]

lemma th_eq_zero_of_lt_two {x : ℝ} (hx : x < 2) : th x = 0 := by
  unfold th
  convert sum_empty
  ext y
  simp only [mem_filter, mem_Iic, not_mem_empty, iff_false, not_and]
  intro hy
  have : y < 2 := by
    cases lt_or_le x 0 with
    | inl hx' =>
      have := Nat.floor_of_nonpos hx'.le
      rw [this, nonpos_iff_eq_zero] at hy
      rw [hy]
      norm_num
    | inr hx' =>
      rw [← Nat.cast_lt_ofNat (α := ℝ)]
      apply lt_of_le_of_lt ?_ hx
      refine (le_floor_iff hx').mp hy
  contrapose! this
  exact this.two_le

theorem extracted_2 (x : ℝ) (z : ℝ) (hz_pos : 0 < z) (hz : z ≠ 1) :
    ContinuousWithinAt (fun x ↦ (x * log x ^ 2)⁻¹) (Set.Icc (3 / 2) x) z := by
  apply ContinuousWithinAt.inv₀
  · apply continuousWithinAt_id.mul <| (continuousWithinAt_id.log ?_).pow _
    simp [hz_pos.ne']
  · apply mul_ne_zero
    · exact hz_pos.ne'
    · apply pow_ne_zero _ <| log_ne_zero_of_pos_of_ne_one hz_pos hz


theorem extracted_1 (x : ℝ) (hx : 2 ≤ x) :
    IntegrableOn
      (fun t ↦ (∑ p ∈ filter Nat.Prime (Iic ⌊t⌋₊), log ↑p) / (t * log t ^ 2))
      (Set.Icc 2 x) volume := by
  have hx0 : 0 ≤ x := zero_le_two.trans hx
  have hx2 : (2 : ℝ) ≤ ⌊x⌋₊ := by
    rwa [← Nat.cast_ofNat, Nat.cast_le, Nat.le_floor_iff hx0, Nat.cast_ofNat]
  have h (n : ℕ) (hn : 2 ≤ n) :
      IntegrableOn (fun t ↦ (∑ p ∈ filter Nat.Prime (Icc 0 ⌊t⌋₊), log ↑p) / (t * log t ^ 2))
        (Set.Ico (n) (n + 1)) volume := by
    have hn2 : (2 : ℝ) ≤ n := by norm_cast
    have hn32 : (3 / 2 : ℝ) ≤ n := le_trans (by norm_num) hn2
    simp_rw [div_eq_mul_inv]
    apply IntegrableOn.mul_continuousOn_of_subset ?_ ?_
      measurableSet_Ico isCompact_Icc Set.Ico_subset_Icc_self
    · apply Integrable.congr (integrable_const (∑ p ∈ filter Nat.Prime (Icc 0 n), log p))
      simp only [measurableSet_Ico, ae_restrict_eq]
      rw [eventuallyEq_inf_principal_iff]
      apply Eventually.of_forall
      intro z hz
      simp [Nat.floor_eq_on_Ico _ _ hz]
    · intro z hz
      apply ContinuousWithinAt.mono (extracted_2 _ _ _ _) (Set.Icc_subset_Icc_left hn32) <;>
      · simp only [Set.mem_Icc] at hz; linarith
  rw [Iic_eq_Icc, bot_eq_zero]
  have : Set.Icc 2 x = Set.Ico (2 : ℝ) ⌊x⌋₊ ∪ Set.Icc (⌊x⌋₊ : ℝ) x :=
    Set.Ico_union_Icc_eq_Icc hx2 (floor_le hx0) |>.symm
  rw [this]
  apply IntegrableOn.union
  swap
  · apply IntegrableOn.mono_set (t := Set.Ico (⌊x⌋₊ : ℝ) (⌊x⌋₊ + 1))
    · apply h
      exact_mod_cast hx2
    · apply Set.Icc_subset_Ico_right
      exact lt_floor_add_one x
  have : Set.Ico (2 : ℝ) ⌊x⌋₊ = ⋃ i ∈ Ico 2 ⌊x⌋₊, Set.Ico (i : ℝ) (i + 1) := by
    ext y
    simp only [Set.mem_Ico, mem_Ico, Set.mem_iUnion, Nat.lt_add_one_iff, exists_and_left,
      exists_prop]
    constructor
    · rintro ⟨h1, h2⟩
      use ⌊y⌋₊
      have : 0 ≤ y := zero_le_two.trans h1
      simp [Nat.floor_le, Nat.floor_lt, this, lt_floor_add_one, h2, le_floor, h1, le_of_lt]
    · rintro ⟨n', h⟩
      have : (2 : ℝ) ≤ n' := by
        rw [← Nat.cast_ofNat, Nat.cast_le]
        exact h.2.1.1
      refine ⟨this.trans h.1, h.2.2.trans_le ?_⟩
      rw [← Nat.cast_add_one, Nat.cast_le, Nat.add_one_le_iff]
      exact h.2.1.2
  rw [this]
  apply MeasureTheory.integrableOn_finset_iUnion.mpr
  intro n hn
  simp only [mem_Ico] at hn
  apply h _ hn.1

lemma th43_b (x : ℝ) (hx : 2 ≤ x) :
    Nat.primeCounting ⌊x⌋₊ =
      th x / log x + ∫ t in Set.Icc 2 x, th t / (t * (Real.log t) ^ 2) := by
  trans th x / log x + ∫ t in Set.Icc (3 / 2) x, th t / (t * (Real.log t) ^ 2)
  swap
  · congr 1
    have : Set.Icc (3/2) x = Set.Ico (3/2) 2 ∪ Set.Icc 2 x := by
      symm
      apply Set.Ico_union_Icc_eq_Icc ?_ hx
      norm_num
    rw [this, setIntegral_union]
    · simp only [add_eq_right]
      apply integral_eq_zero_of_ae
      simp only [measurableSet_Ico, ae_restrict_eq]
      refine eventuallyEq_inf_principal_iff.mpr ?_
      apply Eventually.of_forall
      intro y hy
      simp only [Set.mem_Ico] at hy
      have := th_eq_zero_of_lt_two hy.2
      simp_all
    · rw [Set.disjoint_iff, Set.subset_empty_iff]
      ext y
      simp (config := {contextual := true})
    · exact measurableSet_Icc
    · rw [integrableOn_congr_fun (g := 0)]
      exact integrableOn_zero
      · intro y hy
        simp only [Set.mem_Ico] at hy
        have := th_eq_zero_of_lt_two hy.2
        simp_all
      · exact measurableSet_Ico
    · unfold th
      apply extracted_1 _ hx
  let a : ℕ → ℝ := Set.indicator (setOf Nat.Prime) (fun n => log n)
  have h3 (n : ℕ) : (log n)⁻¹ * a n = if n.Prime then 1 else 0 := by
    simp only [ite_mul, zero_mul, a]
    simp [Set.indicator_apply]
    split_ifs with h
    · rw [mul_comm]
      refine mul_inv_cancel₀ ?_
      refine log_ne_zero_of_pos_of_ne_one ?_ ?_ <;> norm_cast
      exacts [h.pos, h.ne_one]
    · rfl
  have h9 : 3/2 ≤ x := by linarith
  have h2 := sum_mul_eq_sub_sub_integral_mul (f := fun x ↦ (log x)⁻¹) (c := a) (by norm_num) h9
  have h4 : ⌊(3/2 : ℝ)⌋₊ = 1 := by rw [@floor_div_ofNat]; rw [Nat.floor_ofNat]
  have h5 : Icc 0 1 = {0, 1} := by ext; simp; omega
  have h6 (N : ℕ) : (filter Nat.Prime (Ioc 1 N)).card = Nat.primeCounting N := by
    have : filter Nat.Prime (Ioc 1 N) = filter Nat.Prime (range (N + 1)) := by
      ext n
      simp only [mem_filter, mem_Ioc, mem_range, and_congr_left_iff]
      intro hn
      simp [lt_succ, hn.one_lt]
    rw [this]
    simp [primeCounting, primeCounting', count_eq_card_filter_range]
  have h7 : a 1 = 0 := by
    simp [a]
  have h8 (f : ℝ → ℝ) :
    ∫ (u : ℝ) in Set.Ioc (3 / 2) x, deriv (fun x ↦ (log x)⁻¹) u * f u =
    ∫ (u : ℝ) in Set.Icc (3 / 2) x, f u * -(u * log u ^ 2)⁻¹ := by
    rw [← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_ae measurableSet_Icc
    refine Eventually.of_forall (fun u hu => ?_)
    have hu' : 1 < u := by
      simp only [Set.mem_Icc] at hu
      linarith
    rw [deriv_smoothingFn hu']
    ring

  simp [h3, h4, h5, h6, h7, h8, integral_neg] at h2
  rw [h2]
  simp [a, ← th_def', div_eq_mul_inv, mul_comm]
  · intro z hz1 hz2
    refine (differentiableAt_id'.log ?_).inv (log_ne_zero_of_pos_of_ne_one ?_ ?_) <;> linarith
  · have : ∀ y ∈ Set.Icc (3 / 2) x, deriv (fun x ↦ (log x)⁻¹) y = -(y * log y ^ 2)⁻¹:= by
      intro y hy
      simp only [Set.mem_Icc] at hy
      rw [deriv_smoothingFn, mul_inv, ← div_eq_mul_inv, neg_div]
      linarith
    apply ContinuousOn.integrableOn_Icc
    intro z hz
    apply ContinuousWithinAt.congr (f := fun x => - (x * log x ^ 2)⁻¹)
    · apply ContinuousWithinAt.neg
      simp only [Set.mem_Icc] at hz
      apply extracted_2 <;> linarith
    · apply this
    · apply this z hz

/-%%
\begin{lemma}[finsum_range_eq_sum_range]\label{finsum_range_eq_sum_range}\lean{finsum_range_eq_sum_range}\leanok For any arithmetic function $f$ and real number $x$, one has
$$ \sum_{n \leq x} f(n) = \sum_{n \leq ⌊x⌋_+} f(n)$$
and
$$ \sum_{n < x} f(n) = \sum_{n < ⌈x⌉_+} f(n).$$
\end{lemma}
%%-/
lemma finsum_range_eq_sum_range {R: Type*} [AddCommMonoid R] {f : ArithmeticFunction R} (x : ℝ) :
    ∑ᶠ (n : ℕ) (_: n < x), f n = ∑ n ∈ range ⌈x⌉₊, f n := by
  apply finsum_cond_eq_sum_of_cond_iff f
  intros
  simp only [mem_range]
  exact Iff.symm Nat.lt_ceil

lemma finsum_range_eq_sum_range' {R: Type*} [AddCommMonoid R] {f : ArithmeticFunction R} (x : ℝ) :
    ∑ᶠ (n : ℕ) (_: n ≤ x), f n = ∑ n ∈ Iic ⌊x⌋₊, f n := by
  apply finsum_cond_eq_sum_of_cond_iff f
  intro n h
  simp only [mem_Iic]
  exact Iff.symm <| Nat.le_floor_iff'
    fun (hc : n = 0) ↦ (h : f n ≠ 0) <| (congrArg f hc).trans ArithmeticFunction.map_zero

/-%%
\begin{proof}\leanok Straightforward. \end{proof}
%%-/

lemma log2_pos : 0 < log 2 := by
  rw [Real.log_pos_iff zero_le_two]
  exact one_lt_two

/-- Auxiliary lemma I for `chebyshev_asymptotic`: Expressing the sum over Λ up to N as a double sum over primes and exponents. -/
lemma sum_von_mangoldt_as_double_sum (x : ℝ) (hx: 0 ≤ x) :
  ∑ n ∈ Iic ⌊x⌋₊, Λ n =
    ∑ k ∈ Icc 1 ⌊ log x / log 2⌋₊,
      ∑ p ∈ filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), log p := calc
    _ = ∑ n ∈ Iic ⌊x⌋₊, ∑ k ∈ Icc 1 ⌊ log x / log 2⌋₊, ∑ p ∈ filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), if n = p^k then log p else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [mem_Iic, Nat.le_floor_iff hx] at hn
      rw [ArithmeticFunction.vonMangoldt_apply]
      by_cases h : IsPrimePow n
      . simp [h]
        rw [isPrimePow_def] at h
        obtain ⟨ p, k, ⟨ h1, h2, h3 ⟩ ⟩ := h
        rw [<- h3]
        replace h1 := h1.nat_prime
        calc
          _ = log p := by
            congr
            apply Nat.Prime.pow_minFac h1 (Nat.ne_zero_of_lt h2)
          _ = ∑ k' ∈ Icc 1 ⌊ log x / log 2⌋₊, if k' = k then log p else 0 := by
            simp
            have h : k ≤ ⌊x.log / log 2⌋₊ := by
              have h5 : 2^k ≤ n := by
                rw [<-h3]
                apply Nat.pow_le_pow_left (Prime.two_le h1)
              have h6 : 1 ≤ x := by
                apply LE.le.trans _ hn
                simp only [one_le_cast]
                exact LE.le.trans Nat.one_le_two_pow h5
              have h7 : 0 < x := by linarith
              rw [Nat.le_floor_iff, le_div_iff₀ log2_pos, le_log_iff_exp_le h7, mul_comm, exp_mul, exp_log zero_lt_two]
              . apply LE.le.trans _ hn
                norm_cast
              apply div_nonneg (Real.log_nonneg h6) (le_of_lt log2_pos)
            have : 1 ≤ k ∧ k ≤ ⌊x.log / log 2⌋₊ := ⟨ h2, h ⟩
            simp [this]
          _ = ∑ k' ∈ Icc 1 ⌊ log x / log 2⌋₊,
      ∑ p' ∈ filter Nat.Prime (Iic ⌊ x^((k':ℝ)⁻¹) ⌋₊), if k'=k ∧ p'=p then log p else 0 := by
            apply Finset.sum_congr rfl
            intro k' _
            by_cases h : k' = k
            . have : p ≤ ⌊x ^ (k:ℝ)⁻¹⌋₊ := by
                rw [Nat.le_floor_iff]
                . rw [le_rpow_inv_iff_of_pos (cast_nonneg p) hx (cast_pos.mpr h2)]
                  apply LE.le.trans _ hn
                  rw [<-h3]
                  norm_num
                positivity
              simp [h, h1, this]
            simp [h]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro k' _
            apply Finset.sum_congr rfl
            intro p' hp'
            by_cases h : p ^ k = p' ^ k'
            . simp at hp'
              have : (k' = k ∧ p' = p) := by
                have := eq_of_prime_pow_eq h1.prime hp'.2.prime h2 h
                rw [<-this, pow_right_inj₀] at h
                . exact ⟨ h.symm, this.symm ⟩
                . exact Prime.pos h1
                exact Nat.Prime.ne_one h1
              simp [h, this]
            have :¬ (k' = k ∧ p' = p) := by
              contrapose! h
              rw [h.1, h.2]
            simp [h, this]
      simp [h]
      symm
      apply Finset.sum_eq_zero
      intro k hk
      apply Finset.sum_eq_zero
      intro p hp
      simp at hp ⊢
      intro hn'
      contrapose! h; clear h
      rw [isPrimePow_def]
      use p, k
      refine ⟨ Nat.Prime.prime hp.2, ⟨ ?_, hn'.symm ⟩ ⟩
      simp at hk
      exact hk.1
    _ = ∑ k ∈ Icc 1 ⌊ log x / log 2⌋₊, ∑ p ∈ filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), ∑ n ∈ Iic ⌊x⌋₊, if n = p^k then log p else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro p hp
      simp at hk hp ⊢
      intro hpk
      rw [Nat.floor_lt hx] at hpk
      rw [Nat.le_floor_iff (rpow_nonneg hx (k:ℝ)⁻¹), Real.le_rpow_inv_iff_of_pos (cast_nonneg p) hx (cast_pos.mpr hk.1)] at hp
      simp at hpk hp
      linarith [hp.1]

/-- Auxiliary lemma II for `chebyshev_asymptotic`: Controlling the error. -/
lemma sum_von_mangoldt_sub_sum_primes_le (x : ℝ) (hx: 2 ≤ x) :
  |∑ n ∈ Iic ⌊x⌋₊, Λ n - ∑ p ∈ filter Nat.Prime (Iic ⌊ x⌋₊), log p| ≤ (x.log / log 2) * ((x ^ (2:ℝ)⁻¹ + 1) * x.log) := by
  have hx_one : 1 ≤ x := one_le_two.trans hx
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_two hx
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  have hlogx_nonneg : 0 ≤ log x := log_nonneg hx_one

  calc
    _ = |∑ k ∈ Icc 2 ⌊ log x / log 2⌋₊,
      ∑ p ∈ filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), log p + ∑ p ∈ filter Nat.Prime (Iic ⌊ x^((1:ℝ)⁻¹) ⌋₊), log p - ∑ p ∈ filter Nat.Prime (Iic ⌊ x⌋₊), log p| := by
      rw [sum_von_mangoldt_as_double_sum x hx_nonneg]
      congr
      have h : 1 ∈ Icc 1 ⌊ log x / log 2⌋₊ := by
        simp only [mem_Icc, le_refl, one_le_floor_iff, true_and]
        rwa [le_div_iff₀ log2_pos, one_mul, le_log_iff_exp_le hx_pos, exp_log zero_lt_two]
      set s := Icc 2 ⌊ log x / log 2⌋₊
      convert (Finset.sum_erase_add _ _ h).symm
      . ext n
        simp only [mem_Icc, Icc_erase_left, mem_Ioc, and_congr_left_iff, s]
        intro _
        rfl
      exact Eq.symm cast_one
    _ = |∑ k ∈ Icc 2 ⌊ log x / log 2⌋₊,
      ∑ p ∈ filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), log p| := by
        congr
        convert add_sub_cancel_right _ (∑ p ∈ filter Nat.Prime (Iic ⌊ x⌋₊), log p)
        simp only [inv_one, rpow_one]
    _ ≤ ∑ k ∈ Icc 2 ⌊ log x / log 2⌋₊,
      |∑ p ∈ filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), log p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Icc 2 ⌊ log x / log 2⌋₊,
      ∑ p ∈ filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), |log p| := by
        apply sum_le_sum
        intro k _
        exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Icc 2 ⌊ log x / log 2⌋₊,
      ∑ _p ∈ filter Nat.Prime (Iic ⌊ x^((k:ℝ)⁻¹) ⌋₊), log x := by
        apply sum_le_sum
        intro k hk
        apply sum_le_sum
        intro p hp
        simp at hk hp
        have hp' : 1 ≤ p := Nat.Prime.one_le hp.2
        have hp'': p ≠ 0 := Nat.ne_zero_of_lt hp'
        replace hp := (Nat.le_floor_iff' hp'').mp hp.1
        rw [abs_of_nonneg, log_le_log_iff _ hx_pos]
        . apply hp.trans
          calc
            _ ≤ x^(1:ℝ) := by
              apply rpow_le_rpow_of_exponent_le hx_one
              apply inv_le_one_of_one_le₀
              simp only [one_le_cast]
              exact one_le_two.trans hk.1
            _ = _ := by
              simp only [rpow_one]
        . simpa only [cast_pos]
        apply log_nonneg
        simp only [one_le_cast, hp']
    _ ≤ ∑ k ∈ Icc 2 ⌊ log x / log 2⌋₊,
      (x^((2:ℝ)⁻¹)+1) * log x := by
        apply sum_le_sum
        intro k hk
        simp only [sum_const, nsmul_eq_mul]
        gcongr
        rw [<- Nat.le_floor_iff]
        . apply (Finset.card_filter_le _ _).trans
          rw [card_Iic, Nat.floor_add_one]
          . apply Nat.add_le_add _ NeZero.one_le
            apply floor_le_floor
            apply rpow_le_rpow_of_exponent_le hx_one
            simp at hk
            rw [inv_le_inv₀ _ zero_lt_two]
            . exact ofNat_le_cast.mpr hk.1
            simp only [cast_pos]
            exact lt_of_lt_of_le zero_lt_two hk.1
          exact rpow_nonneg hx_nonneg 2⁻¹
        exact add_nonneg (rpow_nonneg hx_nonneg (2:ℝ)⁻¹) zero_le_one
    _ ≤ _ := by
      simp only [sum_const, card_Icc, reduceSubDiff, nsmul_eq_mul]
      gcongr
      apply LE.le.trans _ (Nat.floor_le _)
      simp only [cast_le, tsub_le_iff_right, le_add_iff_nonneg_right, _root_.zero_le]
      exact div_nonneg hlogx_nonneg (le_of_lt log2_pos)



/-- If u ~ v and w-u = o(v) then w ~ v. -/
theorem Asymptotics.IsEquivalent.add_isLittleO' {α : Type*} {β : Type*} [NormedAddCommGroup β] {u : α → β} {v : α → β} {w : α → β} {l : Filter α} (huv : Asymptotics.IsEquivalent l u v) (hwu : (w-u) =o[l] v) :
Asymptotics.IsEquivalent l w v := by
  rw [<- add_sub_cancel u w]
  exact add_isLittleO huv hwu

/-- If u ~ v and u-w = o(v) then w ~ v. -/
theorem Asymptotics.IsEquivalent.add_isLittleO'' {α : Type*} {β : Type*} [NormedAddCommGroup β] {u : α → β} {v : α → β} {w : α → β} {l : Filter α} (huv : Asymptotics.IsEquivalent l u v) (hwu : (u-w) =o[l] v) :
Asymptotics.IsEquivalent l w v := by
  rw [<- sub_sub_self u w]
  exact sub_isLittleO huv hwu

theorem WeakPNT' : Tendsto (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) atTop (nhds 1) := by
  have : (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) = (fun N ↦ (∑ n ∈ range N, Λ n)/N + Λ N / N) := by
    ext N
    have : N ∈ Iic N := mem_Iic.mpr (le_refl _)
    rw [<-Finset.sum_erase_add _ _ this, <-Nat.Iio_eq_range, Iic_erase]
    exact add_div _ _ _

  rw [this, ← add_zero 1]
  apply Tendsto.add WeakPNT
  convert squeeze_zero (f := fun N ↦ Λ N / N) (g := fun N ↦ log N / N) (t₀ := atTop) ?_ ?_ ?_
  . intro N
    simp
    exact div_nonneg vonMangoldt_nonneg (cast_nonneg N)
  . intro N
    simp
    exact div_le_div_of_nonneg_right vonMangoldt_le_log (cast_nonneg N)
  have := Real.tendsto_pow_log_div_pow_atTop 1 1 Real.zero_lt_one
  simp at this
  exact Tendsto.comp this tendsto_natCast_atTop_atTop

/-- An alternate form of the Weak PNT. -/
theorem WeakPNT'' : (fun x ↦ ∑ n ∈ (Iic ⌊x⌋₊), Λ n) ~[atTop] (fun x ↦ x) := by
    apply IsEquivalent.trans (v := fun x ↦ (⌊x⌋₊:ℝ))
    . rw [isEquivalent_iff_tendsto_one]
      . convert Tendsto.comp WeakPNT' tendsto_nat_floor_atTop
        infer_instance
      rw [eventually_iff]
      simp only [ne_eq, cast_eq_zero, floor_eq_zero, not_lt, mem_atTop_sets, ge_iff_le,
        Set.mem_setOf_eq]
      use 1
      simp only [imp_self, implies_true]
    apply IsLittleO.isEquivalent
    rw [<-isLittleO_neg_left]
    apply IsLittleO.of_bound
    intro ε hε
    simp
    use ε⁻¹
    intro b hb
    have hb' : 0 ≤ b := le_of_lt (lt_of_lt_of_le (inv_pos_of_pos hε) hb)
    rw [abs_of_nonneg, abs_of_nonneg hb']
    . apply LE.le.trans _ ((inv_le_iff_one_le_mul₀' hε).mp hb)
      linarith [Nat.lt_floor_add_one b]
    rw [sub_nonneg]
    exact floor_le hb'

/-%%
\begin{theorem}[chebyshev_asymptotic]\label{chebyshev_asymptotic}\lean{chebyshev_asymptotic}\leanok  One has
  $$ \sum_{p \leq x} \log p = x + o(x).$$
\end{theorem}
%%-/
theorem chebyshev_asymptotic :
    (fun x ↦ ∑ p ∈ (filter Nat.Prime (Iic ⌊x⌋₊)), log p) ~[atTop] (fun x ↦ x) := by
  apply WeakPNT''.add_isLittleO''
  apply IsBigO.trans_isLittleO (g := fun x ↦ (x.log / log 2) * ((x ^ (2:ℝ)⁻¹ + 1) * x.log))
  . rw [isBigO_iff']
    use 1
    simp only [gt_iff_lt, zero_lt_one, Pi.sub_apply, norm_eq_abs, norm_div, one_mul,
      eventually_atTop, ge_iff_le, true_and]
    use 2
    intro x hx
    exact (sum_von_mangoldt_sub_sum_primes_le x hx).trans (le_abs_self _)
  apply Asymptotics.isLittleO_of_tendsto
  . intro x hx
    simp [hx]
  suffices h : Tendsto (fun x:ℝ ↦ ((x.log^2 / x ^ (2:ℝ)⁻¹) / log 2 + (x.log^2 / x) / log 2)) atTop (nhds 0) by
    apply Filter.Tendsto.congr' _ h
    simp [EventuallyEq]
    use 2
    intro x hx
    field_simp
    ring_nf
    rw [<-Real.rpow_mul_natCast]
    . simp
      ring
    linarith
  have h1 : (0:ℝ) = 0 + 0 := left_eq_add.mpr rfl
  have h2 : (0:ℝ) = 0 / log 2 := (zero_div _).symm
  rw [h1]
  apply Tendsto.add
  . rw [h2]
    apply Tendsto.div_const
    convert Real.tendsto_pow_log_div_pow_atTop (2:ℝ)⁻¹ 2 (by positivity) with x
    exact (rpow_two x.log).symm
  rw [h2]
  apply Tendsto.div_const
  convert Real.tendsto_pow_log_div_pow_atTop 1 2 (by positivity) with x
  . exact (rpow_two x.log).symm
  exact (rpow_one x).symm
