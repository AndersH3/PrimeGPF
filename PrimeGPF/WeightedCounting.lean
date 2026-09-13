import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
import PrimeGPF.PNT.Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace PrimeGPF.Analytic
open Filter Finset Real
open scoped Topology

/-- A log-weighted count bounds the ordinary count from below. -/
theorem weighted_count_lower {S : Finset ℕ} {N : ℕ}
    (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N) :
    (∑ n ∈ S, Real.log n) ≤ (S.card : ℝ) * Real.log N := by
  calc
    _ ≤ ∑ _n ∈ S, Real.log N := by
      apply Finset.sum_le_sum
      intro n hn
      exact Real.log_le_log (by exact_mod_cast (hS n hn).1) (by exact_mod_cast (hS n hn).2)
    _ = _ := by simp

/-- Split at N^delta; the small integers have negligible cardinality. -/
theorem weighted_count_upper {S : Finset ℕ} {N : ℕ} (hN : 1 ≤ N)
    (hS : ∀ n ∈ S, 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    (S.card : ℝ) * (δ * Real.log N) ≤
      ((N : ℝ) ^ δ + 1) * (δ * Real.log N) + ∑ n ∈ S, Real.log n := by
  classical
  let low := S.filter (fun n : ℕ => (n : ℝ) ≤ (N : ℝ) ^ δ)
  let high := S.filter (fun n : ℕ => ¬ (n : ℝ) ≤ (N : ℝ) ^ δ)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hcard : (S.card : ℝ) = low.card + high.card := by
    exact_mod_cast (Finset.filter_card_add_filter_neg_card_eq_card
      (fun n : ℕ => (n : ℝ) ≤ (N : ℝ) ^ δ) S).symm
  have hlow : (low.card : ℝ) ≤ (N : ℝ) ^ δ + 1 := by
    have hsub : low ⊆ Finset.range (⌊(N : ℝ) ^ δ⌋₊ + 1) := by
      intro n hn
      have hn' := (Finset.mem_filter.mp hn).2
      have : n ≤ ⌊(N : ℝ) ^ δ⌋₊ := (Nat.le_floor_iff (by positivity)).mpr hn'
      exact Finset.mem_range.mpr (by omega)
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_range] at hc
    calc
      (low.card : ℝ) ≤ (⌊(N : ℝ) ^ δ⌋₊ : ℝ) + 1 := by exact_mod_cast hc
      _ ≤ _ := add_le_add_right (Nat.floor_le (by positivity)) 1
  have hhigh : (high.card : ℝ) * (δ * Real.log N) ≤ ∑ n ∈ S, Real.log n := by
    calc
      _ = ∑ _n ∈ high, δ * Real.log N := by simp
      _ ≤ ∑ n ∈ high, Real.log n := by
        apply Finset.sum_le_sum
        intro n hn
        have hn' := lt_of_not_ge (Finset.mem_filter.mp hn).2
        rw [← Real.log_rpow hNpos]
        exact Real.log_le_log (Real.rpow_pos_of_pos hNpos δ) hn'.le
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun n hn _ => Real.log_nonneg (by exact_mod_cast hS n hn))
  rw [hcard, add_mul]
  exact add_le_add (mul_le_mul_of_nonneg_right hlow (mul_nonneg hδ.le hlog)) hhigh

theorem small_cutoff_limit {δ : ℝ} (hδ : δ < 1) :
    Tendsto (fun N : ℕ => ((N : ℝ) ^ δ + 1) * Real.log N / N)
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ (1 - δ)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_pow_atTop (1 - δ) 1 (by linarith)
  have h2 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_pow_atTop 1 1 (by norm_num : (0 : ℝ) < 1)
  have hh := (h1.add h2).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  apply Tendsto.congr' _ (by simpa using hh)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hid : (N : ℝ) ^ (1 - δ) * (N : ℝ) ^ δ = N := by
    rw [← Real.rpow_add hn]
    simp
  dsimp
  field_simp
  nlinarith [hid]

/-- Convert a log-weighted asymptotic to an ordinary counting asymptotic. -/
theorem counting_limit_of_weighted {S : ℕ → Finset ℕ} {A : ℝ} (hA : 0 < A)
    (hS : ∀ N n, n ∈ S N → 1 ≤ n ∧ n ≤ N)
    (h : Tendsto (fun N => (∑ n ∈ S N, Real.log n) / N) atTop (𝓝 A)) :
    Tendsto (fun N => ((S N).card : ℝ) * Real.log N / N) atTop (𝓝 A) := by
  apply tendsto_order.2
  constructor
  · intro l hl
    filter_upwards [h.eventually (lt_mem_nhds hl)] with N hN
    exact hN.trans_le (div_le_div_of_nonneg_right (weighted_count_lower (hS N))
      (Nat.cast_nonneg N))
  · intro u hu
    have hu0 : 0 < u := hA.trans hu
    have hau : A / u < 1 := (div_lt_one hu0).mpr hu
    obtain ⟨δ, hδlow, hδhigh⟩ := exists_between hau
    have hδ0 : 0 < δ := (div_pos hA hu0).trans hδlow
    have hlim : A / δ < u := by
      apply (div_lt_iff₀ hδ0).mpr
      have := (div_lt_iff₀ hu0).mp hδlow
      nlinarith
    have hh : Tendsto (fun N : ℕ =>
        ((N : ℝ) ^ δ + 1) * Real.log N / N +
          ((∑ n ∈ S N, Real.log n) / N) / δ) atTop (𝓝 (A / δ)) := by
      simpa using (small_cutoff_limit hδhigh).add (h.div_const δ)
    filter_upwards [hh.eventually (gt_mem_nhds hlim), eventually_ge_atTop (1 : ℕ)] with N hNu hN
    apply lt_of_le_of_lt _ hNu
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hb := weighted_count_upper hN (fun n hn => (hS N n hn).1) hδ0
    apply (le_div_iff₀ hn).mpr
    have := (div_le_div_of_nonneg_right hb hδ0.le)
    field_simp at this ⊢
    nlinarith

end PrimeGPF.Analytic
