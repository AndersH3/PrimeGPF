import PrimeGPF.Extensions

/-!
# Extension 2: elementary fixed-fiber core

The sharp `1 / zeta(d)` asymptotic in extension 2 requires the later
primitive-exponent counting layer.  The exceptional statement `a = r` is
purely elementary: the multiplicative fiber is empty.
-/
namespace PrimeGPF
open Claims

/-- A prime anchor can never be the output of its own multiplicative
translation: `M(a,q) ≠ a` for every prime input `q`. -/
theorem extension2_mul_output_ne_anchor
    {a q : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q) :
    mul a q ≠ a := by
  intro hout
  have hk : a ∣ a * q + 1 := by
    have h := (output_spec .mul ha hq).2.1
    simpa [hout] using h
  have hkernel : (a * q + 1) % a = 0 := Nat.mod_eq_zero_of_dvd hk
  have hprod : (a * q) % a = 0 := by simp
  rw [Nat.add_mod, hprod, zero_add, Nat.mod_mod] at hkernel
  have ha2 : 2 ≤ a := ha.two_le
  have hone : 1 % a = 1 := Nat.mod_eq_of_lt (by omega)
  omega

/-- Consequently, when the fixed multiplicative output equals the prime
anchor, every truncated fiber count is zero. -/
theorem extension2_equal_anchor_fiberCount_eq_zero
    {a x : ℕ} (ha : Nat.Prime a) :
    Claims.fiberCount .mul a a x = 0 := by
  classical
  unfold Claims.fiberCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro q hq
  have hq' := (Finset.mem_filter.mp hq).2
  exact extension2_mul_output_ne_anchor ha hq'.1 hq'.2

end PrimeGPF
