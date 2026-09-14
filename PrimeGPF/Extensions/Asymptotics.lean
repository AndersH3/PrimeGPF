import PrimeGPF.Extensions.Dynamics
import PrimeGPF.PrimeAP
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace PrimeGPF.Extensions
open Claims Filter
open scoped Topology

theorem primeCount_mono {X Y : ℕ} (h : X ≤ Y) : primeCount X ≤ primeCount Y := by
  classical
  change (primesTo X).card ≤ (primesTo Y).card
  apply Finset.card_le_card
  intro q hq
  obtain ⟨hp, hq⟩ := mem_primesTo.mp hq
  exact mem_primesTo.mpr ⟨hp, hq.trans h⟩

theorem primeCount_pos {X : ℕ} (hX : 2 ≤ X) : 0 < primeCount X := by
  change 0 < (primesTo X).card
  exact Finset.card_pos.mpr ⟨2, mem_primesTo.mpr ⟨Nat.prime_two, hX⟩⟩

theorem primeCount_le_odd_AP_add_one (X : ℕ) : primeCount X ≤ apCount 2 1 X + 1 := by
  classical
  let S := (Finset.range (X + 1)).filter (fun q => Nat.Prime q ∧ q % 2 = 1 % 2)
  have hs : primesTo X ⊆ insert 2 S := by
    intro q hq
    obtain ⟨hp, hq⟩ := mem_primesTo.mp hq
    rcases hp.eq_two_or_odd with h2 | ho
    · simp [h2]
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp, by simpa using ho⟩
  calc
    primeCount X = (primesTo X).card := rfl
    _ ≤ (insert 2 S).card := Finset.card_le_card hs
    _ ≤ S.card + 1 := Finset.card_insert_le _ _
    _ = _ := rfl

/-- Ordinary PNT, obtained from the already proved modulus-2 AP asymptotic. -/
theorem primeCount_log_limit :
    Tendsto (fun X : ℕ => (primeCount X : ℝ) * Real.log X / X) atTop (𝓝 1) := by
  have hAP : Tendsto (fun X : ℕ => (apCount 2 1 X : ℝ) * Real.log X / X)
      atTop (𝓝 1) := by
    simpa using apCount_log_limit Nat.prime_two (by norm_num : 0 < (1 : ℕ))
      (by norm_num : (1 : ℕ) < 2)
  have hlog : Tendsto (fun X : ℕ => Real.log X / X) atTop (𝓝 0) := by
    simpa using tendsto_log_pow_div_natCast_atTop 1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hAP (by simpa using hAP.add hlog)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    have hl : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast apCount_le_primeCount 2 1 X) hl)
      (Nat.cast_nonneg X)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    have hl : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
    have hc : (primeCount X : ℝ) ≤ (apCount 2 1 X : ℝ) + 1 := by
      exact_mod_cast primeCount_le_odd_AP_add_one X
    have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc hl)
      (Nat.cast_nonneg X)
    convert hh using 1 <;> ring

theorem cutoff_ratio_limit {c : ℕ} (hc : 0 < c) :
    Tendsto (fun X : ℕ => ((X / c : ℕ) : ℝ) / X) atTop (𝓝 ((c : ℝ)⁻¹)) := by
  have hm := tendsto_mod_div_atTop_nhds_zero_nat (m := c) hc
  have hh := (tendsto_const_nhds.sub hm).div_const (c : ℝ)
  have hh' : Tendsto (fun X : ℕ => (1 - ((X % c : ℕ) : ℝ) / X) / c)
      atTop (𝓝 ((c : ℝ)⁻¹)) := by simpa using hh
  apply Tendsto.congr' _ hh'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
  have hx : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have he : (X : ℝ) = (c : ℝ) * (X / c : ℕ) + (X % c : ℕ) := by
    exact_mod_cast (Nat.div_add_mod X c).symm
  dsimp
  field_simp
  nlinarith

theorem cutoff_log_ratio_limit {c : ℕ} (hc : 0 < c) :
    Tendsto (fun X : ℕ => Real.log ((X / c : ℕ) : ℝ) / Real.log X) atTop (𝓝 1) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hratio := cutoff_ratio_limit hc
  have hlog := (Real.continuousAt_log (inv_ne_zero (ne_of_gt hcR))).tendsto.comp hratio
  have hh := hlog.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hh' := hh.add (tendsto_const_nhds (x := (1 : ℝ)))
  apply Tendsto.congr' _ (by simpa using hh')
  filter_upwards [eventually_ge_atTop (max c 2)] with X hX
  have hX2 : 2 ≤ X := le_trans (le_max_right _ _) hX
  have hXc : c ≤ X := le_trans (le_max_left _ _) hX
  have hx : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hf : (0 : ℝ) < (X / c : ℕ) := by exact_mod_cast Nat.div_pos hXc hc
  have hl : Real.log (X : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hX2)).ne'
  dsimp
  rw [Real.log_div hf.ne' hx.ne']
  field_simp
  ring

/-- PNT scaling at an integer cutoff. -/
theorem primeCount_scaled_limit {c : ℕ} (hc : 0 < c) :
    Tendsto (fun X : ℕ => (primeCount (X / c) : ℝ) / primeCount X)
      atTop (𝓝 ((c : ℝ)⁻¹)) := by
  have hcut := Nat.tendsto_div_const_atTop hc.ne'
  have hnum := primeCount_log_limit.comp hcut
  have hpnt := hnum.div primeCount_log_limit (by norm_num : (1 : ℝ) ≠ 0)
  have hlog := (cutoff_log_ratio_limit hc).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hh := (hpnt.mul (cutoff_ratio_limit hc)).mul hlog
  apply Tendsto.congr' _ (by simpa using hh)
  filter_upwards [eventually_ge_atTop (2 * c)] with X hX
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hX2 : 2 ≤ X := by omega
  have hf2 : 2 ≤ X / c := (Nat.le_div_iff_mul_le hc).mpr hX
  have hx : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
  have hf : ((X / c : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show X / c ≠ 0 by omega)
  have hlx : Real.log (X : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hX2)).ne'
  have hlf : Real.log ((X / c : ℕ) : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hf2)).ne'
  have hpx : (primeCount X : ℝ) ≠ 0 := by exact_mod_cast (primeCount_pos hX2).ne'
  dsimp
  field_simp
  <;> ring

/-- Extension 6: prime-relative upper density at most 2^(-k), in the
equivalent eventual-epsilon formulation (avoiding a limsup convention). -/
theorem image_prime_upper_density {a : ℕ} (ha : Nat.Prime a) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      (imageTo a k X).card / (primeCount X : ℝ) ≤ ((2 : ℝ) ^ k)⁻¹ + ε := by
  have hp : 0 < (2 : ℕ) ^ k := by positivity
  have hlim := primeCount_scaled_limit hp
  have hone : Tendsto (fun X : ℕ => 1 / (primeCount X : ℝ)) atTop (𝓝 0) := by
    simpa using proof_primeAP_dependency.tendsto_log_pow_div_primeCount 0
  have hh := hlim.add hone
  have hε' : ((↑((2 : ℕ) ^ k) : ℝ))⁻¹ < ((2 : ℝ) ^ k)⁻¹ + ε := by
    norm_cast
    linarith
  filter_upwards [hh.eventually (gt_mem_nhds (by simpa using hε'))] with X hX
  have hcut : (X + 1) / 2 ^ k - 1 ≤ X / 2 ^ k := by
    have h := Nat.div_le_div_right (show X + 1 ≤ X + 2 ^ k by omega)
    rw [Nat.add_div_right X hp] at h
    omega
  have hc := image_count_bound ha k X
  have hm := primeCount_mono hcut
  have hb : (imageTo a k X).card ≤ primeCount (X / 2 ^ k) + 1 := by
    split_ifs at hc <;> omega
  have hbR : ((imageTo a k X).card : ℝ) ≤ (primeCount (X / 2 ^ k) : ℝ) + 1 := by
    exact_mod_cast hb
  have hd := div_le_div_of_nonneg_right hbR (Nat.cast_nonneg (primeCount X))
  rw [add_div] at hd
  exact hd.trans hX.le

/-- Extension 5: the number of orbit visits has density zero relative to primes. -/
theorem orbit_prime_density_zero {a q : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q)
    (hex : (a, q) ≠ (2, 3)) :
    Tendsto (fun X : ℕ => (Set.ncard {n | expIter a q n ≤ X} : ℝ) / primeCount X)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun X : ℕ => Real.log X / (primeCount X : ℝ)) atTop (𝓝 0) := by
    simpa using proof_primeAP_dependency.tendsto_log_pow_div_primeCount 1
  have hone : Tendsto (fun X : ℕ => 1 / (primeCount X : ℝ)) atTop (𝓝 0) := by
    simpa using proof_primeAP_dependency.tendsto_log_pow_div_primeCount 0
  have hh := (hlog.div_const (Real.log 2)).add hone
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ (by simpa using hh)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
  have hq2 := hq.two_le
  have hcut : (X + 1) / (q + 1) ≤ X := by
    apply Nat.div_le_of_le_mul
    nlinarith
  have hb := (expIter_visit_count ha hq hex X).trans
    (Nat.add_le_add_right (Nat.log_mono_right hcut) 1)
  have hbR : (Set.ncard {n | expIter a q n ≤ X} : ℝ) ≤ (Nat.log 2 X : ℝ) + 1 := by
    exact_mod_cast hb
  have hl := Real.natLog_le_logb X 2
  have hu : (Set.ncard {n | expIter a q n ≤ X} : ℝ) ≤ Real.log X / Real.log 2 + 1 := by
    simpa only [Real.logb, Nat.cast_ofNat] using hbR.trans (add_le_add_right hl 1)
  have hd := div_le_div_of_nonneg_right hu (Nat.cast_nonneg (primeCount X))
  convert hd using 1 <;> ring

end PrimeGPF.Extensions
