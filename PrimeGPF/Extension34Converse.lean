import PrimeGPF.Extension34Structure

/-!
# Extensions 3 and 4: easy converse at the kernel level

Once the kernel is explicitly a product of powers of the indicated primes and
a factor 5 is present, its greatest prime factor is 5.  This is the easy
converse direction of the exact classifications.
-/
namespace PrimeGPF

/-- A positive `3^α * 5^β` with `β > 0` has greatest prime factor 5. -/
theorem gpf_three_pow_mul_five_pow
    {α β : ℕ} (hβ : 0 < β) :
    gpf (3 ^ α * 5 ^ β) = 5 := by
  have hn : 1 < 3 ^ α * 5 ^ β := by
    have h5 : 5 ≤ 5 ^ β := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : β ≠ 0)
      rw [pow_succ]
      have hk : 1 ≤ 5 ^ k := one_le_pow₀ (by norm_num)
      nlinarith
    have h3 : 1 ≤ 3 ^ α := one_le_pow₀ (by norm_num)
    nlinarith
  apply gpf_eq_of_spec hn
  refine ⟨Nat.prime_five, ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : β ≠ 0)
    rw [pow_succ]
    exact dvd_mul_of_dvd_right (dvd_mul_left 5 (5 ^ k)) (3 ^ α)
  · intro s hs hd
    rcases hs.dvd_mul.mp hd with h3 | h5
    · have hs3 : s ∣ 3 := hs.dvd_of_dvd_pow h3
      have hse : s = 3 :=
        ((Nat.prime_three.dvd_iff_eq hs.ne_one).mp hs3).symm
      omega
    · have hs5 : s ∣ 5 := hs.dvd_of_dvd_pow h5
      have hse : s = 5 :=
        ((Nat.prime_five.dvd_iff_eq hs.ne_one).mp hs5).symm
      omega

/-- A positive `2^α * 5^β` with `β > 0` has greatest prime factor 5. -/
theorem gpf_two_pow_mul_five_pow
    {α β : ℕ} (hβ : 0 < β) :
    gpf (2 ^ α * 5 ^ β) = 5 := by
  have hn : 1 < 2 ^ α * 5 ^ β := by
    have h5 : 5 ≤ 5 ^ β := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : β ≠ 0)
      rw [pow_succ]
      have hk : 1 ≤ 5 ^ k := one_le_pow₀ (by norm_num)
      nlinarith
    have h2 : 1 ≤ 2 ^ α := one_le_pow₀ (by norm_num)
    nlinarith
  apply gpf_eq_of_spec hn
  refine ⟨Nat.prime_five, ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : β ≠ 0)
    rw [pow_succ]
    exact dvd_mul_of_dvd_right (dvd_mul_left 5 (5 ^ k)) (2 ^ α)
  · intro s hs hd
    rcases hs.dvd_mul.mp hd with h2 | h5
    · have hs2 : s ∣ 2 := hs.dvd_of_dvd_pow h2
      have hse : s = 2 :=
        ((Nat.prime_two.dvd_iff_eq hs.ne_one).mp hs2).symm
      omega
    · have hs5 : s ∣ 5 := hs.dvd_of_dvd_pow h5
      have hse : s = 5 :=
        ((Nat.prime_five.dvd_iff_eq hs.ne_one).mp hs5).symm
      omega

/-- Kernel-factorization converse for extension 3. -/
theorem extension3_kernel_factorization_implies_output_five
    {q α β : ℕ} (hq : Nat.Prime q) (hβ : 0 < β)
    (hfac : 2 * q + 1 = 3 ^ α * 5 ^ β) :
    mul 2 q = 5 := by
  change gpf (2 * q + 1) = 5
  rw [hfac]
  exact gpf_three_pow_mul_five_pow hβ

/-- Kernel-factorization converse for extension 4. -/
theorem extension4_kernel_factorization_implies_output_five
    {q α β : ℕ} (hq : Nat.Prime q) (hβ : 0 < β)
    (hfac : 3 * q + 1 = 2 ^ α * 5 ^ β) :
    mul 3 q = 5 := by
  change gpf (3 * q + 1) = 5
  rw [hfac]
  exact gpf_two_pow_mul_five_pow hβ

end PrimeGPF
