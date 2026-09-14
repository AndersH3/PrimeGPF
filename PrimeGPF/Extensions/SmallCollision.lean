import PrimeGPF.Extensions.Collisions

namespace PrimeGPF.Extensions

/-- A small-support factorization used in the output-5 classification. -/
theorem two_five_support (n : ℕ) (hn : 0 < n)
    (hs : ∀ r, Nat.Prime r → r ∣ n → r = 2 ∨ r = 5) :
    ∃ α β : ℕ, n = 2 ^ α * 5 ^ β := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn1 : n = 1
    · exact ⟨0, 0, by simp [hn1]⟩
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hn1
    obtain ⟨t, ht⟩ := hrd
    have htpos : 0 < t := by
      by_contra hh
      have ht0 : t = 0 := by omega
      simp [ht0] at ht
      omega
    have htn : t < n := by have := hr.two_le; nlinarith
    obtain ⟨α, β, he⟩ := ih t htn htpos (by
      intro s hs' hd
      apply hs s hs'
      rw [ht]
      exact dvd_mul_of_dvd_right hd r)
    rcases hs r hr ⟨t, ht⟩ with hr2 | hr5
    · refine ⟨α + 1, β, ?_⟩
      rw [ht, hr2, he, pow_succ]
      ring
    · refine ⟨α, β + 1, ?_⟩
      rw [ht, hr5, he, pow_succ]
      ring

theorem gpf_five_not_three_support {n : ℕ} (hn : 1 < n)
    (hg : gpf n = 5) (h3 : ¬ 3 ∣ n) :
    ∃ α β : ℕ, n = 2 ^ α * 5 ^ β := by
  apply two_five_support n (by omega)
  intro r hr hd
  have hb := (gpf_spec hn).2.2 r hr hd
  rw [hg] at hb
  have hr2 := hr.two_le
  interval_cases r <;> norm_num at hr ⊢
  exact False.elim (h3 hd)

theorem prime_square_add_one_not_three {p : ℕ} : ¬ 3 ∣ p ^ 2 + 1 := by
  intro hd
  have he := Nat.mod_eq_zero_of_dvd hd
  have hb := Nat.mod_lt p (by norm_num : 0 < 3)
  interval_cases h : p % 3 <;> norm_num [Nat.add_mod, Nat.pow_mod, h] at he

/-- Stronger than extension 9: already the additive/exponential double collision
in the second-input-2 column has exactly the two stated solutions. -/
theorem add_exp_two_iff {p : ℕ} (hp : Nat.Prime p) :
    add p 2 = exp p 2 ↔ p = 2 ∨ p = 7 := by
  constructor
  · intro he
    by_cases hp2 : p = 2
    · exact Or.inl hp2
    have ha5 := (proof_9_2 p hp).2.1 he
    have he5 : exp p 2 = 5 := he.symm.trans ha5
    have hp3 : p ≠ 3 := by
      intro h
      subst p
      norm_num [add, output, kernel, gpf, scan] at ha5
    have hpodd := hp.eq_two_or_odd.resolve_left hp2
    have hpge : 3 ≤ p := by have := hp.two_le; omega
    have hn : 1 < p ^ 2 + 1 := by nlinarith
    obtain ⟨α, k, hN⟩ := gpf_five_not_three_support hn he5 prime_square_add_one_not_three
    have hN2 : (p ^ 2 + 1) % 2 = 0 := by
      simp [Nat.add_mod, Nat.pow_mod, hpodd]
    have hN4 : (p ^ 2 + 1) % 4 = 2 := by
      have hb := Nat.mod_lt p (by norm_num : 0 < 4)
      interval_cases h : p % 4 <;> norm_num [Nat.add_mod, Nat.pow_mod, h] <;> omega
    have hα0 : α ≠ 0 := by
      intro h
      have hh := congrArg (fun n : ℕ => n % 2) hN
      norm_num [h, Nat.mul_mod, Nat.pow_mod] at hh
      omega
    have hαle : α < 2 := by
      by_contra h
      have hd : 4 ∣ p ^ 2 + 1 := by
        rw [hN]
        exact dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega : 2 ≤ α)) _
      have := Nat.mod_eq_zero_of_dvd hd
      omega
    have hα : α = 1 := by omega
    rw [hα, pow_one] at hN
    have hk0 : k ≠ 0 := by
      intro h
      simp [h] at hN
      nlinarith
    have hpmod3 : p % 3 ≠ 0 := by
      intro hh
      have hd := Nat.dvd_of_mod_eq_zero hh
      have hh' := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd
      exact hp3 hh'.symm
    have hkeven : k % 2 = 0 := by
      by_contra h
      have hkodd : k = 2 * (k / 2) + 1 := by omega
      have hh := congrArg (fun n : ℕ => n % 3) hN
      rw [hkodd, pow_add, pow_mul] at hh
      norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at hh
      have hb := Nat.mod_lt p (by norm_num : 0 < 3)
      interval_cases hm : p % 3 <;> norm_num [hm] at hh <;> omega
    have hk2 : 2 ≤ k := by omega
    have hkform : k = 2 * (k / 2) := by omega
    have h58 : 5 ^ k % 8 = 1 := by
      rw [hkform, pow_mul]
      norm_num [Nat.pow_mod]
    have hp16 : p ^ 2 % 16 = 1 := by omega
    have hp8 : (p + 3) % 8 ≠ 0 := by
      have hb := Nat.mod_lt p (by norm_num : 0 < 16)
      interval_cases hm : p % 16 <;> norm_num [Nat.pow_mod, hm] at hp16 <;> omega
    have h25 : 25 ∣ p ^ 2 + 1 := by
      rw [hN]
      exact dvd_mul_of_dvd_right (pow_dvd_pow 5 hk2) 2
    have h3 : ¬ 3 ∣ p + 3 := by
      intro hd
      have hm := Nat.mod_eq_zero_of_dvd hd
      omega
    have ha5' : gpf (p + 3) = 5 := by
      simpa only [add, output, kernel, Nat.add_assoc] using ha5
    obtain ⟨u, v, hA⟩ := gpf_five_not_three_support (by omega) ha5' h3
    have hv0 : v ≠ 0 := by
      intro hv
      have h5d : 5 ∣ p + 3 := by
        have hh := (gpf_spec (show 1 < p + 3 by omega)).2.1
        rw [ha5'] at hh
        exact hh
      rw [hA, hv, pow_zero, mul_one] at h5d
      have := Nat.prime_five.dvd_of_dvd_pow h5d
      norm_num at this
    have hvle : v < 2 := by
      by_contra hv
      have hd : 25 ∣ p + 3 := by
        rw [hA]
        exact dvd_mul_of_dvd_right (pow_dvd_pow 5 (by omega : 2 ≤ v)) _
      have hm := Nat.mod_eq_zero_of_dvd hd
      have hp25 : p % 25 = 22 := by omega
      have hs := Nat.mod_eq_zero_of_dvd h25
      norm_num [Nat.add_mod, Nat.pow_mod, hp25] at hs
    have hv : v = 1 := by omega
    rw [hv, pow_one] at hA
    have hu0 : u ≠ 0 := by
      intro hu
      simp [hu] at hA
      omega
    have hule : u < 3 := by
      by_contra hu
      have hd : 8 ∣ p + 3 := by
        rw [hA]
        exact dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega : 3 ≤ u)) 5
      exact hp8 (Nat.mod_eq_zero_of_dvd hd)
    have hu : u = 1 ∨ u = 2 := by omega
    rcases hu with hu | hu
    · norm_num [hu] at hA
      exact Or.inr (by omega)
    · norm_num [hu] at hA
      have hp17 : p = 17 := by omega
      subst p
      norm_num at h25
  · rintro (rfl | rfl) <;> norm_num [add, exp, output, kernel, gpf, scan]

/-- Extension 9: exact triple collisions with second input 2. -/
theorem triple_two_iff {p : ℕ} (hp : Nat.Prime p) :
    (add p 2 = mul p 2 ∧ add p 2 = exp p 2) ↔ p = 2 ∨ p = 7 := by
  constructor
  · intro h
    exact (add_exp_two_iff hp).mp h.2
  · rintro (rfl | rfl) <;> norm_num [add, mul, exp, output, kernel, gpf, scan]

end PrimeGPF.Extensions
