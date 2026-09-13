import PrimeGPF.Quadratic
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! Dirichlet's theorem discharges all three unbounded-section claims.
These scripts are not compiler-verified. -/
namespace PrimeGPF
open Claims

/-- A nonzero residue modulo a prime has a prime representative. -/
theorem prime_representative {r : ℕ} (hr : Nat.Prime r)
    (a : ZMod r) (ha : a ≠ 0) : ∃ p, Nat.Prime p ∧ (p : ZMod r) = a := by
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  obtain ⟨p, _, hp, he⟩ := Nat.forall_exists_prime_gt_and_eq_mod (isUnit_iff_ne_zero.mpr ha) 0
  exact ⟨p, hp, he⟩

theorem additive_section_unbounded (p : ℕ) (hp : Nat.Prime p) (B : ℕ) :
    ∃ q, Nat.Prime q ∧ B < add p q := by
  obtain ⟨r, hrbound, hr⟩ := Nat.exists_infinite_primes (max B (p + 1) + 1)
  have hBmax := le_max_left B (p + 1)
  have hpmax := le_max_right B (p + 1)
  have hBr : B < r := by omega
  have hpr : p + 1 < r := by omega
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  have hnonzero : (-((p + 1 : ℕ) : ZMod r)) ≠ 0 := by
    apply neg_ne_zero.mpr
    intro hz
    have hd := (cast_zero_iff_dvd (p + 1) r).mp hz
    have := Nat.le_of_dvd (by omega : 0 < p + 1) hd
    omega
  obtain ⟨q, hq, hqmod⟩ := prime_representative hr (-((p + 1 : ℕ) : ZMod r)) hnonzero
  have hd : r ∣ p + q + 1 := by
    apply (cast_zero_iff_dvd (p + q + 1) r).mp
    push_cast
    rw [hqmod]
    push_cast
    ring
  exact ⟨q, hq, lt_of_lt_of_le hBr ((output_spec .add hp hq).2.2 r hr hd)⟩

theorem multiplicative_section_unbounded (p : ℕ) (hp : Nat.Prime p) (B : ℕ) :
    ∃ q, Nat.Prime q ∧ B < mul p q := by
  obtain ⟨r, hrbound, hr⟩ := Nat.exists_infinite_primes (max B p + 1)
  have hBmax := le_max_left B p
  have hpmax := le_max_right B p
  have hBr : B < r := by omega
  have hpr : p < r := by omega
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  have hp0 : (p : ZMod r) ≠ 0 := by
    intro hz
    have hd := (cast_zero_iff_dvd p r).mp hz
    have := Nat.le_of_dvd hp.pos hd
    omega
  obtain ⟨q, hq, hqmod⟩ := prime_representative hr (-(p : ZMod r)⁻¹)
    (neg_ne_zero.mpr (inv_ne_zero hp0))
  have hd : r ∣ p * q + 1 := by
    apply (cast_zero_iff_dvd (p * q + 1) r).mp
    push_cast
    rw [hqmod, mul_neg, mul_inv_cancel₀ hp0]
    ring
  exact ⟨q, hq, lt_of_lt_of_le hBr ((output_spec .mul hp hq).2.2 r hr hd)⟩

theorem exponential_base_unbounded (q : ℕ) (hq : Nat.Prime q) (B : ℕ) :
    ∃ p, Nat.Prime p ∧ B < exp p q := by
  by_cases hq2 : q = 2
  · subst q
    obtain ⟨r, hBr, hr, hrmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod
      (show IsUnit (1 : ZMod 4) from isUnit_one) B
    have hr4 : r % 4 = 1 := by
      simpa using (cast_eq_iff_mod r 1 4).mp hrmod
    letI : Fact (Nat.Prime r) := ⟨hr⟩
    have hs : IsSquare (-1 : ZMod r) :=
      ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
    obtain ⟨a, ha⟩ := hs
    have ha0 : a ≠ 0 := by intro hz; simp [hz] at ha
    obtain ⟨p, hp, hpmod⟩ := prime_representative hr a ha0
    have hd : r ∣ p ^ 2 + 1 := by
      apply (cast_zero_iff_dvd (p ^ 2 + 1) r).mp
      push_cast
      rw [hpmod, pow_two, ← ha]
      ring
    exact ⟨p, hp, lt_of_lt_of_le hBr ((output_spec .exp hp Nat.prime_two).2.2 r hr hd)⟩
  · obtain ⟨r, hrbound, hr⟩ := Nat.exists_infinite_primes (B + 1)
    letI : Fact (Nat.Prime r) := ⟨hr⟩
    obtain ⟨p, hp, hpmod⟩ := prime_representative hr (-1) (neg_ne_zero.mpr one_ne_zero)
    have hqo : Odd q := Nat.odd_iff.mpr (hq.eq_two_or_odd.resolve_left hq2)
    have hd : r ∣ p ^ q + 1 := by
      apply (cast_zero_iff_dvd (p ^ q + 1) r).mp
      push_cast
      rw [hpmod, hqo.neg_one_pow]
      ring
    exact ⟨p, hp, lt_of_lt_of_le (by omega) ((output_spec .exp hp hq).2.2 r hr hd)⟩

theorem proof_6_4 : t6_4 :=
  ⟨additive_section_unbounded, multiplicative_section_unbounded,
    exponential_base_unbounded⟩

end PrimeGPF
