import PrimeGPF.Extension2Core

/-!
# Extension 2: support restriction

This is the elementary support statement used before the primitive-exponent
counting argument: every prime factor of the multiplicative kernel is at most
the output prime and is different from the anchor.
-/
namespace PrimeGPF

/-- A prime divisor of `a*q+1` in a fixed multiplicative fiber is at most the
output prime and cannot be the anchor prime `a`. -/
theorem extension2_mul_kernel_support_exclusion
    {a r q s : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q)
    (hout : mul a q = r) (hs : Nat.Prime s)
    (hsd : s ∣ a * q + 1) :
    s ≤ r ∧ s ≠ a := by
  have hsle : s ≤ r := by
    have hmax := (output_spec .mul ha hq).2.2 s hs
    simpa [kernel, hout] using hmax hsd
  refine ⟨hsle, ?_⟩
  intro hsa
  subst s
  have hz := Nat.mod_eq_zero_of_dvd hsd
  have ha2 := ha.two_le
  norm_num [Nat.add_mod, Nat.mul_mod] at hz

/-- Pointwise formulation of the support restriction appearing in extension 2. -/
theorem extension2_mul_kernel_restricted_support
    {a r q : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q)
    (hout : mul a q = r) :
    ∀ s, Nat.Prime s → s ∣ a * q + 1 → s ≤ r ∧ s ≠ a := by
  intro s hs hsd
  exact extension2_mul_kernel_support_exclusion ha hq hout hs hsd

end PrimeGPF
