import PrimeGPF.Arithmetic

namespace PrimeGPF
open Claims

/-- Odd numbers whose greatest prime divisor is three are pure powers of three. -/
theorem odd_gpf_three_iff {n : ℕ} (hn : 1 < n) (ho : n % 2 = 1) :
    gpf n = 3 ↔ ∃ k, 0 < k ∧ n = 3 ^ k := by
  constructor
  · intro he
    obtain ⟨k, hk⟩ := power_of_prime_support 3 n Nat.prime_three (by omega) (by
      intro s hs hd
      have hl := (gpf_spec hn).2.2 s hs hd
      have hs2 := hs.two_le
      have hcases : s = 2 ∨ s = 3 := by omega
      rcases hcases with rfl | h3
      · have hh := Nat.mod_eq_zero_of_dvd hd; omega
      · exact h3)
    refine ⟨k, ?_, hk⟩
    by_contra h
    have : k = 0 := by omega
    simp_all
  · rintro ⟨k, hk, rfl⟩; exact gpf_prime_power Nat.prime_three hk

theorem exponent_three_ge_two {n k : ℕ} (hn : 3 < n) (he : n = 3 ^ k) : 2 ≤ k := by
  by_contra h
  have hk : k = 0 ∨ k = 1 := by omega
  rcases hk with rfl | rfl <;> norm_num at he <;> omega

theorem exponent_two_ge_three {n k : ℕ} (hn : 4 < n) (he : n = 2 ^ k) : 3 ≤ k := by
  by_contra h
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk with rfl | rfl | rfl <;> norm_num at he <;> omega

theorem add_two_small {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    add p q = 2 ↔ ∃ m, 3 ≤ m ∧
      ((p = 2 ∧ q + 3 = 2 ^ m) ∨ (q = 2 ∧ p + 3 = 2 ^ m)) := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  constructor
  · intro he
    obtain ⟨m, _, hm⟩ := (gpf_eq_two_iff (kernel_gt_one .add hp hq)).mp he
    change p + q + 1 = 2 ^ m at hm
    refine ⟨m, exponent_two_ge_three (by omega) hm, ?_⟩
    by_cases hp' : p = 2
    · left; exact ⟨hp', by omega⟩
    · have hq' : q = 2 := by
        by_contra hh
        exact odd_add_closed p q hp hq hp' hh he
      right; exact ⟨hq', by omega⟩
  · rintro ⟨m, hm, h⟩
    apply (gpf_eq_two_iff (kernel_gt_one .add hp hq)).mpr
    refine ⟨m, by omega, ?_⟩
    change p + q + 1 = 2 ^ m
    rcases h with ⟨hp', he⟩ | ⟨hq', he⟩ <;> omega

theorem mul_two_odd_opposite {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (he : mul p q = 2) : p ≠ 2 ∧ q ≠ 2 ∧ p % 4 ≠ q % 4 := by
  have hd : 2 ∣ p * q + 1 := by simpa [he] using (output_spec .mul hp hq).2.1
  have hh := Nat.mod_eq_zero_of_dvd hd
  have hp2 : p ≠ 2 := by
    intro h; subst p
    norm_num [Nat.add_mod, Nat.mul_mod] at hh
  have hq2 : q ≠ 2 := by
    intro h; subst q
    norm_num [Nat.add_mod, Nat.mul_mod] at hh
  exact ⟨hp2, hq2, (proof_5_6 p q hp hq hp2 hq2).2 he⟩

theorem odd_add_three {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    add p q = 3 ↔ ∃ m, 2 ≤ m ∧ p + q + 1 = 3 ^ m := by
  have ho := hp.eq_two_or_odd.resolve_left hp2
  have ho' := hq.eq_two_or_odd.resolve_left hq2
  have hn := kernel_gt_one .add hp hq
  have hodd : (p + q + 1) % 2 = 1 := by simp [Nat.add_mod, ho, ho']
  have hp' := hp.two_le
  have hq' := hq.two_le
  constructor
  · intro he
    obtain ⟨m, _, hm⟩ := (odd_gpf_three_iff hn hodd).mp he
    change p + q + 1 = 3 ^ m at hm
    exact ⟨m, exponent_three_ge_two (n := p + q + 1) (by omega) hm, hm⟩
  · rintro ⟨m, hm, he⟩
    exact (odd_gpf_three_iff hn hodd).mpr ⟨m, by omega, he⟩

theorem add_three_mod_six {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp3 : 3 < p) (hq3 : 3 < q) (he : add p q = 3) : p % 6 = 1 ∧ q % 6 = 1 := by
  have ho := hp.eq_two_or_odd.resolve_left (by omega : p ≠ 2)
  have ho' := hq.eq_two_or_odd.resolve_left (by omega : q ≠ 2)
  have hpmod : p % 3 ≠ 0 := by
    intro hh
    have hd := Nat.dvd_of_mod_eq_zero hh
    have heq := (hp.dvd_iff_eq (by decide : 3 ≠ 1)).mp hd
    omega
  have hqmod : q % 3 ≠ 0 := by
    intro hh
    have hd := Nat.dvd_of_mod_eq_zero hh
    have heq := (hq.dvd_iff_eq (by decide : 3 ≠ 1)).mp hd
    omega
  have hd : 3 ∣ p + q + 1 := by simpa [he] using (output_spec .add hp hq).2.1
  have hh : (p + q + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
  rw [Nat.add_mod (p + q) 1 3, Nat.add_mod p q 3] at hh
  have hp_cases : p % 3 = 1 ∨ p % 3 = 2 := by omega
  have hq_cases : q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases hp_cases with hp_one | hp_two <;>
    rcases hq_cases with hq_one | hq_two <;> omega

theorem two_mul_three {q : ℕ} (hq : Nat.Prime q) :
    mul 2 q = 3 ↔ ∃ m, 2 ≤ m ∧ 2 * q + 1 = 3 ^ m := by
  have hn := kernel_gt_one .mul Nat.prime_two hq
  have hodd : (2 * q + 1) % 2 = 1 := by simp [Nat.add_mod, Nat.mul_mod]
  have hq2 := hq.two_le
  constructor
  · intro he
    obtain ⟨m, _, hm⟩ := (odd_gpf_three_iff hn hodd).mp he
    change 2 * q + 1 = 3 ^ m at hm
    exact ⟨m, exponent_three_ge_two (n := 2 * q + 1) (by omega) hm, hm⟩
  · rintro ⟨m, hm, he⟩
    exact (odd_gpf_three_iff hn hodd).mpr ⟨m, by omega, he⟩

theorem proof_4_3 : t4_3 := by
  exact ⟨fun _ _ hp hq => add_two_small hp hq,
    fun _ _ hp hq => mul_two_iff hp hq,
    fun _ _ hp hq he => mul_two_odd_opposite hp hq he,
    fun _ _ hp hq hp2 hq2 => odd_add_three hp hq hp2 hq2,
    fun _ _ hp hq hp3 hq3 he => add_three_mod_six hp hq hp3 hq3 he,
    fun _ hq => two_mul_three hq⟩

end PrimeGPF
