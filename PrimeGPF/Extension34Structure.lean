import PrimeGPF.Extension34Residues

/-!
# Extensions 3 and 4: exponent-vector structure

This file proves the easy support/positivity/parity layer of the two exact
output-5 multiplicative fiber classifications.  The coprimality/primitivity
step is kept separate.
-/
namespace PrimeGPF

/-- A positive integer supported on two fixed primes is a product of powers
of those primes. -/
theorem extension_product_of_two_prime_support
    (a b n : ℕ) (ha : Nat.Prime a) (hb : Nat.Prime b) (hn : 0 < n)
    (h : ∀ s, Nat.Prime s → s ∣ n → s = a ∨ s = b) :
    ∃ α β, n = a ^ α * b ^ β := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : n = 1
    · exact ⟨0, 0, by simp [he]⟩
    obtain ⟨s, hs, hd⟩ := Nat.exists_prime_and_dvd he
    rcases h s hs hd with hsa | hsb
    · subst s
      obtain ⟨t, ht⟩ := hd
      have htpos : 0 < t := by
        by_contra hh
        have ht0 : t = 0 := by omega
        rw [ht0, Nat.mul_zero] at ht
        omega
      have htn : t < n := by
        have := ha.two_le
        nlinarith
      obtain ⟨α, β, hfac⟩ := ih t htn htpos (by
        intro s hs hd
        apply h s hs
        apply dvd_trans hd
        rw [ht]
        exact dvd_mul_left t a)
      exact ⟨α + 1, β, by rw [ht, hfac, pow_succ]; ring⟩
    · subst s
      obtain ⟨t, ht⟩ := hd
      have htpos : 0 < t := by
        by_contra hh
        have ht0 : t = 0 := by omega
        rw [ht0, Nat.mul_zero] at ht
        omega
      have htn : t < n := by
        have := hb.two_le
        nlinarith
      obtain ⟨α, β, hfac⟩ := ih t htn htpos (by
        intro s hs hd
        apply h s hs
        apply dvd_trans hd
        rw [ht]
        exact dvd_mul_left t b)
      exact ⟨α, β + 1, by rw [ht, hfac, pow_succ]; ring⟩

/-- Powers of two with odd exponent are 2 modulo 3. -/
theorem extension_two_pow_mod_three_of_odd {k : ℕ} (hk : k % 2 = 1) :
    2 ^ k % 3 = 2 := by
  have hdec := Nat.mod_add_div k 2
  have hkform : k = 2 * (k / 2) + 1 := by omega
  rw [hkform, pow_add]
  have heven : 2 ^ (2 * (k / 2)) % 3 = 1 :=
    two_pow_mod_three_of_even (by simp)
  norm_num [Nat.mul_mod, heven]

/-- The nonexceptional anchor-2 output-5 kernel has exactly the support and
parity shape used in equation (3), before the gcd condition is imposed. -/
theorem extension3_exponent_structure
    {q : ℕ} (hq : Nat.Prime q) (hout : mul 2 q = 5) (hq2 : q ≠ 2) :
    ∃ α β : ℕ,
      0 < α ∧ 0 < β ∧ α % 2 = 1 ∧
      2 * q + 1 = 3 ^ α * 5 ^ β := by
  have hodd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left hq2
  have hn : 1 < 2 * q + 1 := by
    have := hq.two_le
    omega
  have hg : gpf (2 * q + 1) = 5 := by
    simpa [mul, output, kernel] using hout
  have h5div : 5 ∣ 2 * q + 1 := by
    have hd := (gpf_spec hn).2.1
    simpa [hg] using hd
  have hsupp : ∀ s, Nat.Prime s → s ∣ 2 * q + 1 → s = 3 ∨ s = 5 := by
    intro s hs hd
    rcases prime_dvd_of_gpf_five' hn hg hs hd with h2 | h3 | h5
    · subst s
      have hz := Nat.mod_eq_zero_of_dvd hd
      norm_num [Nat.add_mod, Nat.mul_mod, hodd] at hz
    · exact Or.inl h3
    · exact Or.inr h5
  obtain ⟨α, β, hfac⟩ :=
    extension_product_of_two_prime_support 3 5 (2 * q + 1)
      Nat.prime_three Nat.prime_five (by omega) hsupp
  have hNmod4 : (2 * q + 1) % 4 = 3 := by
    have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by omega
    rcases hq4 with h1 | h3
    · norm_num [Nat.add_mod, Nat.mul_mod, h1]
    · norm_num [Nat.add_mod, Nat.mul_mod, h3]
  have hβpos : 0 < β := by
    by_contra hβ
    have hβ0 : β = 0 := by omega
    rw [hfac, hβ0, pow_zero, Nat.mul_one] at h5div
    have hh := Nat.prime_five.dvd_of_dvd_pow h5div
    norm_num at hh
  have hαpos : 0 < α := by
    by_contra hα
    have hα0 : α = 0 := by omega
    rw [hfac, hα0, pow_zero, one_mul] at hNmod4
    have hpow : 5 ^ β % 4 = 1 := by simp [Nat.pow_mod]
    omega
  have hαodd : α % 2 = 1 := by
    have hαlt := Nat.mod_lt α (by omega : 0 < 2)
    by_contra hne
    have hαeven : α % 2 = 0 := by omega
    have hdec := Nat.mod_add_div α 2
    have hαform : α = 2 * (α / 2) := by omega
    have h3pow : 3 ^ α % 4 = 1 := by
      rw [hαform, pow_mul]
      norm_num [Nat.pow_mod]
    have h5pow : 5 ^ β % 4 = 1 := by simp [Nat.pow_mod]
    rw [hfac] at hNmod4
    norm_num [Nat.mul_mod, h3pow, h5pow] at hNmod4
  exact ⟨α, β, hαpos, hβpos, hαodd, hfac⟩

/-- The anchor-3 output-5 kernel has support `{2,5}`, both exponents are
positive, and the exponents have the same parity.  The separate primitivity
step will rule out the even-even case. -/
theorem extension4_exponent_structure
    {q : ℕ} (hq : Nat.Prime q) (hout : mul 3 q = 5) :
    ∃ α β : ℕ,
      0 < α ∧ 0 < β ∧ α % 2 = β % 2 ∧
      3 * q + 1 = 2 ^ α * 5 ^ β := by
  have hq2 : q ≠ 2 := by
    intro h
    subst q
    norm_num [mul, output, kernel, gpf, scan] at hout
  have hodd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left hq2
  have hn : 1 < 3 * q + 1 := by
    have := hq.two_le
    omega
  have hg : gpf (3 * q + 1) = 5 := by
    simpa [mul, output, kernel] using hout
  have h5div : 5 ∣ 3 * q + 1 := by
    have hd := (gpf_spec hn).2.1
    simpa [hg] using hd
  have hNmod3 : (3 * q + 1) % 3 = 1 := by
    simp [Nat.add_mod, Nat.mul_mod]
  have hsupp : ∀ s, Nat.Prime s → s ∣ 3 * q + 1 → s = 2 ∨ s = 5 := by
    intro s hs hd
    rcases prime_dvd_of_gpf_five' hn hg hs hd with h2 | h3 | h5
    · exact Or.inl h2
    · subst s
      have hz := Nat.mod_eq_zero_of_dvd hd
      omega
    · exact Or.inr h5
  obtain ⟨α, β, hfac⟩ :=
    extension_product_of_two_prime_support 2 5 (3 * q + 1)
      Nat.prime_two Nat.prime_five (by omega) hsupp
  have hNmod2 : (3 * q + 1) % 2 = 0 := by
    norm_num [Nat.add_mod, Nat.mul_mod, hodd]
  have hαpos : 0 < α := by
    by_contra hα
    have hα0 : α = 0 := by omega
    rw [hfac, hα0, pow_zero, one_mul] at hNmod2
    have hpow : 5 ^ β % 2 = 1 := by simp [Nat.pow_mod]
    omega
  have hβpos : 0 < β := by
    by_contra hβ
    have hβ0 : β = 0 := by omega
    rw [hfac, hβ0, pow_zero, Nat.mul_one] at h5div
    have hh := Nat.prime_five.dvd_of_dvd_pow h5div
    norm_num at hh
  have hparity : α % 2 = β % 2 := by
    have hαlt := Nat.mod_lt α (by omega : 0 < 2)
    have hβlt := Nat.mod_lt β (by omega : 0 < 2)
    by_contra hne
    have hcases :
        (α % 2 = 0 ∧ β % 2 = 1) ∨
        (α % 2 = 1 ∧ β % 2 = 0) := by
      omega
    rw [hfac] at hNmod3
    rcases hcases with hcase | hcase
    · have h2pow := two_pow_mod_three_of_even hcase.1
      have h5pow := five_pow_mod_three_of_odd hcase.2
      norm_num [Nat.mul_mod, h2pow, h5pow] at hNmod3
    · have h2pow := extension_two_pow_mod_three_of_odd hcase.1
      have h5pow := five_pow_mod_three_of_even hcase.2
      norm_num [Nat.mul_mod, h2pow, h5pow] at hNmod3
  exact ⟨α, β, hαpos, hβpos, hparity, hfac⟩

end PrimeGPF
