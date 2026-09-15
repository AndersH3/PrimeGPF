import PrimeGPF.Extension34Structure

/-!
# Extensions 3 and 4: easy converse at the kernel level

Once the kernel is explicitly a product `p^α * 5^β`, with `p` prime and
`p < 5`, a positive exponent of `5` forces the greatest prime factor to be
exactly `5`.  The generic lemma below captures that argument once; the
Extension 3/4 statements are then immediate specializations to `p = 3` and
`p = 2`.

This is the easy converse direction of the exact classifications.  No parity,
coprimality, or counting argument is needed here.
-/
namespace PrimeGPF

/-- If `p` is a prime below `5` and `β > 0`, then `p^α * 5^β` has greatest
prime factor `5`.

The proof uses only the defining specification of `gpf`: `5` divides the
product, and every prime divisor must divide either `p^α` or `5^β`, hence is
`p` or `5`. -/
theorem gpf_prime_pow_mul_five_pow
    {p α β : ℕ} (hp : Nat.Prime p) (hp5 : p < 5) (hβ : 0 < β) :
    gpf (p ^ α * 5 ^ β) = 5 := by
  have hn : 1 < p ^ α * 5 ^ β := by
    have h5 : 5 ≤ 5 ^ β := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : β ≠ 0)
      rw [pow_succ]
      have hk : 1 ≤ 5 ^ k := one_le_pow₀ (by norm_num)
      nlinarith
    have hpbase : 1 ≤ p := by omega
    have hp1 : 1 ≤ p ^ α := one_le_pow₀ hpbase
    nlinarith
  apply gpf_eq_of_spec hn
  refine ⟨Nat.prime_five, ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : β ≠ 0)
    rw [pow_succ]
    exact dvd_mul_of_dvd_right (dvd_mul_left 5 (5 ^ k)) (p ^ α)
  · intro s hs hd
    rcases hs.dvd_mul.mp hd with hpPow | h5Pow
    · have hspDiv : s ∣ p := hs.dvd_of_dvd_pow hpPow
      have hsp : s = p :=
        ((hp.dvd_iff_eq hs.ne_one).mp hspDiv).symm
      omega
    · have hs5Div : s ∣ 5 := hs.dvd_of_dvd_pow h5Pow
      have hs5 : s = 5 :=
        ((Nat.prime_five.dvd_iff_eq hs.ne_one).mp hs5Div).symm
      omega

/-- Specialization of `gpf_prime_pow_mul_five_pow` to the `{3,5}` support
appearing in Extension 3. -/
theorem gpf_three_pow_mul_five_pow
    {α β : ℕ} (hβ : 0 < β) :
    gpf (3 ^ α * 5 ^ β) = 5 := by
  exact gpf_prime_pow_mul_five_pow Nat.prime_three (by norm_num) hβ

/-- Specialization of `gpf_prime_pow_mul_five_pow` to the `{2,5}` support
appearing in Extension 4. -/
theorem gpf_two_pow_mul_five_pow
    {α β : ℕ} (hβ : 0 < β) :
    gpf (2 ^ α * 5 ^ β) = 5 := by
  exact gpf_prime_pow_mul_five_pow Nat.prime_two (by norm_num) hβ

/-- Kernel-factorization converse for Extension 3.  The primality hypothesis on
`q` is kept in the public API because this theorem is consumed by the exact
prime-fiber classification, although the kernel-level implication itself does
not need it. -/
theorem extension3_kernel_factorization_implies_output_five
    {q α β : ℕ} (_hq : Nat.Prime q) (hβ : 0 < β)
    (hfac : 2 * q + 1 = 3 ^ α * 5 ^ β) :
    mul 2 q = 5 := by
  change gpf (2 * q + 1) = 5
  rw [hfac]
  exact gpf_three_pow_mul_five_pow hβ

/-- Kernel-factorization converse for Extension 4. -/
theorem extension4_kernel_factorization_implies_output_five
    {q α β : ℕ} (_hq : Nat.Prime q) (hβ : 0 < β)
    (hfac : 3 * q + 1 = 2 ^ α * 5 ^ β) :
    mul 3 q = 5 := by
  change gpf (3 * q + 1) = 5
  rw [hfac]
  exact gpf_two_pow_mul_five_pow hβ

end PrimeGPF
