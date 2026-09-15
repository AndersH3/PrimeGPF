import PrimeGPF.Extension1Core
import PrimeGPF.Extension7Core

/-!
# Restricted support for extensions 1 and 7

These lemmas formalize the elementary exclusion argument used in the report:
for a sufficiently large fiber/collision input, no prime divisor of the
additive kernel can also divide `a+1`.
-/
namespace PrimeGPF

/--
Shared contradiction step:
if a prime divisor `s` of `a+q+1` also divides `a+1`, then it divides `q`.
For prime `q`, the only possible nontrivial case is `s=q`, which is
excluded by an upper bound on `s`.

Keeping this separate avoids duplicating the same modular argument in
Extensions 1 and 7.
-/
theorem prime_divisor_shift_exclusion
    {a q s R : ℕ} (hq : Nat.Prime q) (hs : Nat.Prime s)
    (hsle : s ≤ R) (hRq : R < q)
    (hsd : s ∣ a + q + 1) :
    ¬ s ∣ a + 1 := by
  intro hsa
  have hk' : s ∣ (a + 1) + q := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsd
  have hbase : (a + 1) % s = 0 := Nat.mod_eq_zero_of_dvd hsa
  have htot : ((a + 1) + q) % s = 0 := Nat.mod_eq_zero_of_dvd hk'
  rw [Nat.add_mod, hbase, zero_add, Nat.mod_mod] at htot
  have hsq : s ∣ q := Nat.dvd_of_mod_eq_zero htot
  rcases (Nat.dvd_prime hq).mp hsq with hs1 | hsqeq
  · exact hs.ne_one hs1
  · have : q ≤ R := by simpa [hsqeq] using hsle
    omega

/-- In a fixed additive fiber, once `q > r`, a prime divisor of the additive
kernel cannot divide the shifted anchor `a+1`.

The primality of `r` is retained in the public signature because this lemma is
used as part of a prime-fiber API, although the support-exclusion argument
itself only needs the equality `add a q = r` and the inequality `r < q`. -/
theorem extension1_large_input_support_exclusion
    {a r q s : ℕ} (ha : Nat.Prime a) (_hr : Nat.Prime r)
    (hq : Nat.Prime q) (hout : add a q = r) (hrq : r < q)
    (hs : Nat.Prime s) (hsd : s ∣ a + q + 1) :
    s ≤ r ∧ ¬ s ∣ a + 1 := by
  have hsle : s ≤ r := by
    have hmax := (output_spec .add ha hq).2.2 s hs
    simpa [kernel, hout] using hmax hsd
  exact ⟨hsle, prime_divisor_shift_exclusion hq hs hsle hrq hsd⟩

/-- Hence every prime divisor in the large-input additive fiber lies in the
report's restricted support `{l prime | l ≤ r ∧ l ∤ a+1}`. -/
theorem extension1_large_input_restricted_support
    {a r q : ℕ} (ha : Nat.Prime a) (hr : Nat.Prime r)
    (hq : Nat.Prime q) (hout : add a q = r) (hrq : r < q) :
    ∀ s, Nat.Prime s → s ∣ a + q + 1 →
      s ≤ r ∧ ¬ s ∣ a + 1 := by
  intro s hs hsd
  exact extension1_large_input_support_exclusion ha hr hq hout hrq hs hsd

/-- For an additive--multiplicative collision, once `q > R_a`, no prime
factor of the additive kernel can divide `a+1`. -/
theorem extension7_large_collision_support_exclusion
    {a q s : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q)
    (hcoll : add a q = mul a q)
    (hRq : gpf (a ^ 2 + a - 1) < q)
    (hs : Nat.Prime s) (hsd : s ∣ a + q + 1) :
    s ≤ gpf (a ^ 2 + a - 1) ∧ ¬ s ∣ a + 1 := by
  have hsleR : s ≤ gpf (a ^ 2 + a - 1) :=
    (extension7_collision_add_kernel_smooth ha hq hcoll).2 s hs hsd
  exact ⟨hsleR,
    prime_divisor_shift_exclusion hq hs hsleR hRq hsd⟩

end PrimeGPF
