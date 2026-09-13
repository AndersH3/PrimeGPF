import PrimeGPF.PNT.Consequences

namespace PrimeGPF.Analytic
open ArithmeticFunction Filter Finset Real Asymptotics
open scoped Topology

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

theorem nat_Iic_eq_range (N : ℕ) : Finset.Iic N = Finset.range (N + 1) := by
  ext n
  simp only [Finset.mem_Iic, Finset.mem_range]
  omega

noncomputable def psi (f : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.Iic N, f n
noncomputable def theta (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Iic N).filter Nat.Prime, f n

/-- The proved Chebyshev-hypothesis version of Wiener-Ikehara suffices for APs. -/
theorem mangoldt_AP_limit {q : ℕ} (hq : 0 < q) (a : ZMod q) (ha : IsUnit a) :
    Tendsto (fun N => cumsum (vonMangoldt.residueClass a) N / N)
      atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  let f := vonMangoldt.residueClass a
  have hpos : ∀ n, 0 ≤ f n := vonMangoldt.residueClass_nonneg a
  have hle : ∀ n, f n ≤ vonMangoldt n := vonMangoldt.residueClass_le a
  have hs (sigma : ℝ) (hsigma : 1 < sigma) : Summable (nterm f sigma) := by
    have hs0 : Summable (nterm (fun n => (vonMangoldt n : ℝ)) sigma) := by
      simpa only [← nterm_eq_norm_term] using
        (@ArithmeticFunction.LSeriesSummable_vonMangoldt sigma hsigma).norm
    apply Summable.of_nonneg_of_le _ _ hs0
    · intro n
      unfold nterm
      split_ifs <;> positivity
    · intro n
      unfold nterm
      split_ifs
      · rfl
      · simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos n),
          abs_of_nonneg vonMangoldt_nonneg]
        exact div_le_div_of_nonneg_right (hle n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hc : cheby f := by
    obtain ⟨C, hC⟩ := vonMangoldt_cheby
    refine ⟨C, fun N => le_trans ?_ (hC N)⟩
    unfold cumsum
    apply Finset.sum_le_sum
    intro n hn
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos n),
      abs_of_nonneg vonMangoldt_nonneg] using hle n
  apply WienerIkeharaTheorem' hpos hs hc
    (vonMangoldt.continuousOn_LFunctionResidueClassAux a)
  simpa using vonMangoldt.eqOn_LFunctionResidueClassAux ha

/-- Changing from a strict cutoff to an inclusive one costs only f(N)/N. -/
theorem psi_limit_of_cumsum {f : ℕ → ℝ} {A : ℝ}
    (hf : ∀ n, 0 ≤ f n ∧ f n ≤ Real.log n)
    (h : Tendsto (fun N => cumsum f N / N) atTop (𝓝 A)) :
    Tendsto (fun N => psi f N / N) atTop (𝓝 A) := by
  have hsmall : Tendsto (fun N : ℕ => f N / N) atTop (𝓝 0) := by
    have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ) / N) atTop (𝓝 0) := by
      have hh := Real.tendsto_pow_log_div_pow_atTop 1 1 (by norm_num : (0 : ℝ) < 1)
      simpa using hh.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog
    · exact Eventually.of_forall fun n => div_nonneg (hf n).1 (Nat.cast_nonneg n)
    · exact Eventually.of_forall fun n => div_le_div_of_nonneg_right (hf n).2 (Nat.cast_nonneg n)
  have he (N : ℕ) : psi f N / N = cumsum f N / N + f N / N := by
    simp only [psi, nat_Iic_eq_range, Finset.sum_range_succ, cumsum, add_div]
  simpa only [he, add_zero] using h.add hsmall

/-- The total contribution of nonprime prime powers is negligible. -/
theorem total_prime_power_error :
    Tendsto (fun N : ℕ => (psi (fun n => vonMangoldt n) N -
      theta (fun n => vonMangoldt n) N) / N) atTop (𝓝 0) := by
  have hpsi : Tendsto (fun N : ℕ => psi (fun n => vonMangoldt n) N / N) atTop (𝓝 1) :=
    psi_limit_of_cumsum (fun n => ⟨vonMangoldt_nonneg, vonMangoldt_le_log⟩) WeakPNT
  have hθ : Tendsto (fun N : ℕ => theta (fun n => vonMangoldt n) N / N) atTop (𝓝 1) := by
    have he := (isEquivalent_iff_tendsto_one (eventually_ne_atTop (0 : ℝ))).mp chebyshev_asymptotic
    have hh := he.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    change Tendsto (fun N : ℕ =>
      (∑ p ∈ (Finset.Iic ⌊(N : ℝ)⌋₊).filter Nat.Prime, Real.log p) / N)
      atTop (𝓝 1) at hh
    simp only [Nat.floor_natCast] at hh
    convert hh using 1
    ext N
    unfold theta
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    exact vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2
  simpa only [← sub_div, sub_self] using hpsi.sub hθ

/-- Removing nonprime powers is uniform under restriction to a residue class. -/
theorem theta_AP_limit {q : ℕ} (hq : 0 < q) (a : ZMod q) (ha : IsUnit a) :
    Tendsto (fun N => theta (vonMangoldt.residueClass a) N / N)
      atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  let f := vonMangoldt.residueClass a
  have hf : ∀ n, 0 ≤ f n ∧ f n ≤ vonMangoldt n := fun n =>
    ⟨vonMangoldt.residueClass_nonneg a n, vonMangoldt.residueClass_le a n⟩
  have hψ := psi_limit_of_cumsum
    (fun n => ⟨(hf n).1, le_trans (hf n).2 vonMangoldt_le_log⟩) (mangoldt_AP_limit hq a ha)
  have herror (N : ℕ) : 0 ≤ psi f N - theta f N ∧
      psi f N - theta f N ≤ psi (fun n => vonMangoldt n) N - theta (fun n => vonMangoldt n) N := by
    simp only [psi, theta, Finset.sum_filter, ← Finset.sum_sub_distrib]
    constructor
    · apply Finset.sum_nonneg
      intro n hn
      split_ifs <;> simp_all [hf]
    · apply Finset.sum_le_sum
      intro n hn
      split_ifs <;> simp_all [hf]
  have hzero : Tendsto (fun N : ℕ => (psi f N - theta f N) / N) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds total_prime_power_error
    · exact Eventually.of_forall fun n => div_nonneg (herror n).1 (Nat.cast_nonneg n)
    · exact Eventually.of_forall fun n => div_le_div_of_nonneg_right (herror n).2 (Nat.cast_nonneg n)
  have he (N : ℕ) : theta f N / N = psi f N / N - (psi f N - theta f N) / N := by ring
  simpa only [← he, sub_zero] using hψ.sub hzero

end PrimeGPF.Analytic
