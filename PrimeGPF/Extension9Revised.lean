import PrimeGPF.Extensions

/-!
# Extension 9: revised triple-collision proof

A deliberately modular proof of the exact classification

`add p 2 = mul p 2 = exp p 2  ↔  p = 2 ∨ p = 7`.

The helper lemmas isolate the small modular computations so that the main
argument does not depend on large `omega` contexts containing powers.
-/
namespace PrimeGPF

set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

/-- A prime at most five is 2, 3, or 5. -/
theorem prime_le_five_cases {s : ℕ} (hs : Nat.Prime s) (hle : s ≤ 5) :
    s = 2 ∨ s = 3 ∨ s = 5 := by
  rcases hs.eq_two_or_odd with h2 | hodd
  · exact Or.inl h2
  · right
    have hs2 := hs.two_le
    omega

/-- If the GPF is five, every prime divisor is 2, 3, or 5. -/
theorem prime_dvd_of_gpf_five' {n s : ℕ} (hn : 1 < n)
    (hg : gpf n = 5) (hs : Nat.Prime s) (hd : s ∣ n) :
    s = 2 ∨ s = 3 ∨ s = 5 := by
  have hle := (gpf_spec hn).2.2 s hs hd
  rw [hg] at hle
  exact prime_le_five_cases hs hle

/-- A positive integer whose only prime divisor is 5 is a power of 5. -/
theorem power_of_five_support {n : ℕ} (hn : 0 < n)
    (h : ∀ s, Nat.Prime s → s ∣ n → s = 5) :
    ∃ k, n = 5 ^ k :=
  power_of_prime_support 5 n Nat.prime_five hn h

/-- Powers of 5 with even exponent are 1 modulo 3. -/
theorem five_pow_mod_three_of_even {k : ℕ} (hk : k % 2 = 0) :
    5 ^ k % 3 = 1 := by
  have hdec := Nat.mod_add_div k 2
  have hkform : k = 2 * (k / 2) := by omega
  rw [hkform, pow_mul]
  norm_num [Nat.pow_mod]

/-- Powers of 5 with odd exponent are 2 modulo 3. -/
theorem five_pow_mod_three_of_odd {k : ℕ} (hk : k % 2 = 1) :
    5 ^ k % 3 = 2 := by
  have hdec := Nat.mod_add_div k 2
  have hkform : k = 2 * (k / 2) + 1 := by omega
  rw [hkform, pow_add]
  have heven : 5 ^ (2 * (k / 2)) % 3 = 1 :=
    five_pow_mod_three_of_even (by
      have : (2 * (k / 2)) % 2 = 0 := by simp
      exact this)
  norm_num [Nat.mul_mod, heven]

/-- Powers of 5 with even exponent are 1 modulo 8. -/
theorem five_pow_mod_eight_of_even {k : ℕ} (hk : k % 2 = 0) :
    5 ^ k % 8 = 1 := by
  have hdec := Nat.mod_add_div k 2
  have hkform : k = 2 * (k / 2) := by omega
  rw [hkform, pow_mul]
  norm_num [Nat.pow_mod]

/-- Powers of 2 with even exponent are 1 modulo 3. -/
theorem two_pow_mod_three_of_even {k : ℕ} (hk : k % 2 = 0) :
    2 ^ k % 3 = 1 := by
  have hdec := Nat.mod_add_div k 2
  have hkform : k = 2 * (k / 2) := by omega
  rw [hkform, pow_mul]
  norm_num [Nat.pow_mod]

/-- A positive natural with prime support contained in `{2,5}` is a product
of powers of 2 and 5. -/
theorem product_of_two_five_support {n : ℕ} (hn : 0 < n)
    (h : ∀ s, Nat.Prime s → s ∣ n → s = 2 ∨ s = 5) :
    ∃ α β, n = 2 ^ α * 5 ^ β := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : n = 1
    · exact ⟨0, 0, by simp [he]⟩
    obtain ⟨s, hs, hd⟩ := Nat.exists_prime_and_dvd he
    rcases h s hs hd with h2 | h5
    · subst s
      obtain ⟨t, ht⟩ := hd
      have htpos : 0 < t := by
        by_contra hh
        have ht0 : t = 0 := by omega
        rw [ht0, Nat.mul_zero] at ht
        omega
      have htn : t < n := by nlinarith
      obtain ⟨α, β, hfac⟩ := ih t htn htpos (by
        intro s hs hd
        apply h s hs
        apply dvd_trans hd
        rw [ht]
        exact dvd_mul_left t 2)
      exact ⟨α + 1, β, by rw [ht, hfac, pow_succ]; ring⟩
    · subst s
      obtain ⟨t, ht⟩ := hd
      have htpos : 0 < t := by
        by_contra hh
        have ht0 : t = 0 := by omega
        rw [ht0, Nat.mul_zero] at ht
        omega
      have htn : t < n := by nlinarith
      obtain ⟨α, β, hfac⟩ := ih t htn htpos (by
        intro s hs hd
        apply h s hs
        apply dvd_trans hd
        rw [ht]
        exact dvd_mul_left t 5)
      exact ⟨α, β + 1, by rw [ht, hfac, pow_succ]; ring⟩

/-- Complete classification of triple collisions with second input 2. -/
theorem extension9_triple_second_two_revised {p : ℕ} (hp : Nat.Prime p) :
    (add p 2 = mul p 2 ∧ add p 2 = exp p 2) ↔ p = 2 ∨ p = 7 := by
  constructor
  · rintro ⟨ham, hae⟩
    by_cases hp2 : p = 2
    · exact Or.inl hp2
    · right
      have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
      have hp2le := hp.two_le
      have h5 : add p 2 = 5 := (proof_9_2 p hp).1 ham
      have hm5 : mul p 2 = 5 := ham.symm.trans h5
      have he5 : exp p 2 = 5 := hae.symm.trans h5

      /- The multiplicative kernel forces p = 1 (mod 3). -/
      have hgMul : gpf (2 * p + 1) = 5 := by
        simpa [mul, output, kernel, Nat.mul_comm] using hm5
      have hnMul : 1 < 2 * p + 1 := by omega
      have h3mul : 3 ∣ 2 * p + 1 := by
        by_contra h3
        have hsupp : ∀ s, Nat.Prime s → s ∣ 2 * p + 1 → s = 5 := by
          intro s hs hd
          rcases prime_dvd_of_gpf_five' hnMul hgMul hs hd with h2 | h3s | h5s
          · subst s
            have hz := Nat.mod_eq_zero_of_dvd hd
            omega
          · subst s
            exact (h3 hd).elim
          · exact h5s
        obtain ⟨k, hk⟩ := power_of_five_support (by omega) hsupp
        have hpmod4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
        have hNmod4 : (2 * p + 1) % 4 = 3 := by
          rcases hpmod4 with hp1 | hp3
          · norm_num [Nat.add_mod, Nat.mul_mod, hp1]
          · norm_num [Nat.add_mod, Nat.mul_mod, hp3]
        rw [hk] at hNmod4
        have hpowmod : 5 ^ k % 4 = 1 := by simp [Nat.pow_mod]
        omega
      have hmulmod3 := Nat.mod_eq_zero_of_dvd h3mul
      have hpmod3 : p % 3 = 1 := by
        have hpmodlt := Nat.mod_lt p (by omega : 0 < 3)
        norm_num [Nat.add_mod, Nat.mul_mod] at hmulmod3
        omega

      /- The square kernel is exactly twice a power of five. -/
      have hgExp : gpf (p ^ 2 + 1) = 5 := by
        simpa [exp, output, kernel] using he5
      have hnExp : 1 < p ^ 2 + 1 := by nlinarith
      have hpmod4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
      have hExpMod4 : (p ^ 2 + 1) % 4 = 2 := by
        rcases hpmod4 with hp1 | hp3
        · norm_num [pow_two, Nat.add_mod, Nat.mul_mod, hp1]
        · norm_num [pow_two, Nat.add_mod, Nat.mul_mod, hp3]
      have hExpMod2 : (p ^ 2 + 1) % 2 = 0 := by
        norm_num [pow_two, Nat.add_mod, Nat.mul_mod, hodd]
      have h2Exp : 2 ∣ p ^ 2 + 1 := Nat.dvd_of_mod_eq_zero hExpMod2
      let t := (p ^ 2 + 1) / 2
      have hExpEq : 2 * t = p ^ 2 + 1 := by
        dsimp [t]
        exact Nat.mul_div_cancel' h2Exp
      have htpos : 0 < t := by
        by_contra ht
        have ht0 : t = 0 := by omega
        rw [ht0, Nat.mul_zero] at hExpEq
        have hpos : 0 < p ^ 2 + 1 := by positivity
        omega
      have hExpMod3 : (p ^ 2 + 1) % 3 = 2 := by
        norm_num [pow_two, Nat.add_mod, Nat.mul_mod, hpmod3]
      have hsuppT : ∀ s, Nat.Prime s → s ∣ t → s = 5 := by
        intro s hs hd
        have htdiv : t ∣ p ^ 2 + 1 := by
          rw [← hExpEq]
          exact dvd_mul_left t 2
        have hsd : s ∣ p ^ 2 + 1 := dvd_trans hd htdiv
        rcases prime_dvd_of_gpf_five' hnExp hgExp hs hsd with h2 | h3 | h5s
        · subst s
          obtain ⟨u, hu⟩ := hd
          have h4 : 4 ∣ p ^ 2 + 1 := by
            refine ⟨u, ?_⟩
            rw [← hExpEq, hu]
            ring
          have hz := Nat.mod_eq_zero_of_dvd h4
          omega
        · subst s
          have hz := Nat.mod_eq_zero_of_dvd hsd
          omega
        · exact h5s
      obtain ⟨k, htk⟩ := power_of_five_support htpos hsuppT
      have hExpPow : p ^ 2 + 1 = 2 * 5 ^ k := by
        calc
          p ^ 2 + 1 = 2 * t := hExpEq.symm
          _ = 2 * 5 ^ k := by rw [htk]
      have hkpos : 0 < k := by
        by_contra hk
        have hk0 : k = 0 := by omega
        rw [hk0, pow_zero, Nat.mul_one] at hExpPow
        have hpsq : 4 ≤ p ^ 2 := by nlinarith
        omega
      have hkmod2 : k % 2 = 0 := by
        by_contra hk0
        have hklt := Nat.mod_lt k (by omega : 0 < 2)
        have hk1 : k % 2 = 1 := by omega
        have hpow3 := five_pow_mod_three_of_odd hk1
        rw [hExpPow] at hExpMod3
        norm_num [Nat.mul_mod, hpow3] at hExpMod3
      have hk2 : 2 ≤ k := by omega
      have h25Exp : 25 ∣ p ^ 2 + 1 := by
        have h25pow : 5 ^ 2 ∣ 5 ^ k := pow_dvd_pow 5 hk2
        have hm : 2 * 5 ^ 2 ∣ 2 * 5 ^ k := Nat.mul_dvd_mul_left 2 h25pow
        have h25dvd : 25 ∣ 2 * 5 ^ 2 := by norm_num
        rw [hExpPow]
        exact dvd_trans h25dvd hm

      /- The additive kernel is 2^α 5^β. -/
      have hgAdd : gpf (p + 3) = 5 := by
        simpa [add, output, kernel] using h5
      have hnAdd : 1 < p + 3 := by omega
      have hAddMod3 : (p + 3) % 3 = 1 := by
        norm_num [Nat.add_mod, hpmod3]
      have hsuppAdd : ∀ s, Nat.Prime s → s ∣ p + 3 → s = 2 ∨ s = 5 := by
        intro s hs hd
        rcases prime_dvd_of_gpf_five' hnAdd hgAdd hs hd with h2 | h3 | h5s
        · exact Or.inl h2
        · subst s
          have hz := Nat.mod_eq_zero_of_dvd hd
          omega
        · exact Or.inr h5s
      obtain ⟨α, β, hAddFac⟩ :=
        product_of_two_five_support (by omega) hsuppAdd
      have hAddEven : (p + 3) % 2 = 0 := by
        norm_num [Nat.add_mod, hodd]
      have hαpos : 0 < α := by
        by_contra hα
        have hα0 : α = 0 := by omega
        rw [hα0, pow_zero, one_mul] at hAddFac
        rw [hAddFac] at hAddEven
        have hoddpow : 5 ^ β % 2 = 1 := by simp [Nat.pow_mod]
        rw [hoddpow] at hAddEven
        norm_num at hAddEven
      have h5Add : 5 ∣ p + 3 := by
        have hd := (output_spec .add hp Nat.prime_two).2.1
        simpa [h5] using hd
      have hβpos : 0 < β := by
        by_contra hβ
        have hβ0 : β = 0 := by omega
        rw [hAddFac, hβ0, pow_zero, Nat.mul_one] at h5Add
        have hh := Nat.prime_five.dvd_of_dvd_pow h5Add
        norm_num at hh
      have hβ1 : β = 1 := by
        by_contra hβne
        have hβ2 : 2 ≤ β := by omega
        have h25pow : 5 ^ 2 ∣ 5 ^ β := pow_dvd_pow 5 hβ2
        have h25Add : 25 ∣ p + 3 := by
          rw [hAddFac]
          simpa [pow_two] using dvd_mul_of_dvd_right h25pow (2 ^ α)
        have hAdd25 := Nat.mod_eq_zero_of_dvd h25Add
        have hExp25 := Nat.mod_eq_zero_of_dvd h25Exp
        have hp25lt := Nat.mod_lt p (by omega : 0 < 25)
        have hp25 : p % 25 = 22 := by
          norm_num [Nat.add_mod] at hAdd25
          omega
        norm_num [pow_two, Nat.add_mod, Nat.mul_mod, hp25] at hExp25
      have hαmod2 : α % 2 = 1 := by
        have hαlt := Nat.mod_lt α (by omega : 0 < 2)
        by_contra hαne
        have hα0 : α % 2 = 0 := by omega
        have hpow3 := two_pow_mod_three_of_even hα0
        rw [hAddFac, hβ1, pow_one] at hAddMod3
        norm_num [Nat.mul_mod, hpow3] at hAddMod3

      /- Even k gives p^2 = 1 (mod 16). -/
      have h5mod8 := five_pow_mod_eight_of_even hkmod2
      have h5dec := Nat.mod_add_div (5 ^ k) 8
      have h5form : 5 ^ k = 1 + 8 * (5 ^ k / 8) := by omega
      have hdouble : 2 * 5 ^ k = 2 + 16 * (5 ^ k / 8) := by
        omega
      have hExpMod16 : (p ^ 2 + 1) % 16 = 2 := by
        rw [hExpPow, hdouble]
        simp [Nat.add_mod, Nat.mul_mod]
      have hpSqMod16 : p ^ 2 % 16 = 1 := by
        rw [Nat.add_mod] at hExpMod16
        have hlt := Nat.mod_lt (p ^ 2) (by omega : 0 < 16)
        omega

      have hαlt3 : α < 3 := by
        apply lt_of_not_ge
        intro hα3'
        have h8pow : 2 ^ 3 ∣ 2 ^ α := pow_dvd_pow 2 hα3'
        have h8Add : 8 ∣ p + 3 := by
          rw [hAddFac, hβ1, pow_one]
          simpa using dvd_mul_of_dvd_left h8pow 5
        have hAdd8 := Nat.mod_eq_zero_of_dvd h8Add
        have hp8lt := Nat.mod_lt p (by omega : 0 < 8)
        have hp8 : p % 8 = 5 := by
          norm_num [Nat.add_mod] at hAdd8
          omega
        have hp16lt := Nat.mod_lt p (by omega : 0 < 16)
        have hp16cases : p % 16 = 5 ∨ p % 16 = 13 := by omega
        rcases hp16cases with hp16 | hp16
        · norm_num [pow_two, Nat.mul_mod, hp16] at hpSqMod16
        · norm_num [pow_two, Nat.mul_mod, hp16] at hpSqMod16
      have hα1 : α = 1 := by omega
      rw [hα1, hβ1, pow_one, pow_one] at hAddFac
      norm_num at hAddFac
      omega
  · rintro (rfl | rfl) <;>
      norm_num [add, mul, exp, output, kernel, gpf, scan]

end PrimeGPF
