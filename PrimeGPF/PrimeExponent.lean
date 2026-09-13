import PrimeGPF.Conditional
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace PrimeGPF
open Claims

theorem oddCofactor_step_ge_two {p : ℕ} (hp : 2 ≤ p) (n : ℕ) :
    2 ≤ (p - 1) * p ^ (2 * n + 1) := by
  have hsub : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  have hpow : p ≤ p ^ (2 * n + 1) := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < p) (show 1 ≤ 2 * n + 1 by omega)
  nlinarith

theorem oddCofactor_ge_exp {p : ℕ} (hp : 2 ≤ p) (n : ℕ) :
    2 * n + 1 ≤ oddCofactor p n := by
  induction n with
  | zero => simp [oddCofactor]
  | succ n ih =>
    have := oddCofactor_step_ge_two hp n
    simp only [oddCofactor]
    omega

theorem oddCofactor_gt_exp {p n : ℕ} (hp : 2 ≤ p) (hn : 0 < n)
    (hex : (p, 2 * n + 1) ≠ (2, 3)) : 2 * n + 1 < oddCofactor p n := by
  have hsub : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hbase := oddCofactor_ge_exp hp j
  have hinc : 2 < (p - 1) * p ^ (2 * j + 1) := by
    by_cases hj : j = 0
    · subst j
      have hp3 : 3 ≤ p := by
        by_contra hh
        have hp2 : p = 2 := by omega
        exact hex (by simp [hp2])
      simp only [Nat.mul_zero, zero_add, pow_one]
      nlinarith
    · have hpow : 8 ≤ p ^ (2 * j + 1) := by
        calc
          8 = 2 ^ 3 := by norm_num
          _ ≤ p ^ 3 := Nat.pow_le_pow_left hp _
          _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
      nlinarith
  simp only [oddCofactor]
  omega

theorem oddCofactor_odd_all {p : ℕ} (hp : 1 ≤ p) (n : ℕ) :
    oddCofactor p n % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one p with he | ho
  · induction n with
    | zero => simp [oddCofactor]
    | succ n ih =>
      simp [oddCofactor, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, he, ih]
  · exact oddCofactor_odd hp ho n

/-- The cofactor is congruent to its odd exponent at any divisor of p+1. -/
theorem oddCofactor_cast {p r : ℕ} (hp : 1 ≤ p)
    (h : (p : ZMod r) = -1) (n : ℕ) :
    (oddCofactor p n : ZMod r) = (2 * n + 1 : ℕ) := by
  have hsub : ((p - 1 : ℕ) : ZMod r) = (p : ZMod r) - 1 := by
    apply eq_sub_iff_add_eq.mpr
    have he := congrArg (fun x : ℕ => (x : ZMod r)) (Nat.sub_add_cancel hp)
    simpa only [Nat.cast_add, Nat.cast_one] using he
  induction n with
  | zero => simp [oddCofactor]
  | succ n ih =>
    simp only [oddCofactor, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, ih, hsub, h]
    rw [pow_add, pow_mul]
    norm_num
    push_cast
    ring

/-- A prime factor of the cofactor outside p+1 exists, except at (2,3).
The only valuation input is mathlib's lifting-the-exponent lemma. -/
theorem prime_divisor_cofactor {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hq2 : q ≠ 2) (hex : (p,q) ≠ (2,3)) :
    ∃ r, Nat.Prime r ∧ r ∣ p ^ q + 1 ∧ ¬ r ∣ p + 1 ∧ r ≠ 2 := by
  have hqo : Odd q := Nat.odd_iff.mpr (hq.eq_two_or_odd.resolve_left hq2)
  obtain ⟨n, hqn⟩ := hqo
  have hqn' : q = 2 * n + 1 := hqn
  have hn : 0 < n := by have := hq.two_le; omega
  let N := oddCofactor p n
  have hNpos : 0 < N := oddCofactor_pos p n
  have hNgt : q < N := by
    rw [hqn']
    exact oddCofactor_gt_exp hp.two_le hn (by rwa [← hqn'])
  have hid : (p + 1) * N = p ^ q + 1 := by
    rw [hqn']
    exact oddCofactor_identity (by have := hp.two_le; omega) n
  have hNd : N ∣ p ^ q + 1 := hid ▸ dvd_mul_left N (p + 1)
  have hNodd : N % 2 = 1 := oddCofactor_odd_all (by have := hp.two_le; omega) n
  by_contra hh
  have hsupport : ∀ r, Nat.Prime r → r ∣ N → r = q := by
    intro r hr hrN
    have hr2 : r ≠ 2 := by
      intro he
      subst r
      have := Nat.mod_eq_zero_of_dvd hrN
      omega
    have hrp : r ∣ p + 1 := by
      by_contra hrp
      exact hh ⟨r, hr, dvd_trans hrN hNd, hrp, hr2⟩
    have hz : (p : ZMod r) = -1 := by
      have he := (cast_zero_iff_dvd (p + 1) r).mpr hrp
      push_cast at he
      exact eq_neg_of_add_eq_zero_left he
    have hc := oddCofactor_cast (by have := hp.two_le; omega) hz n
    have hzero : (N : ZMod r) = 0 := (cast_zero_iff_dvd N r).mpr hrN
    have hrq : r ∣ q := by
      apply (cast_zero_iff_dvd q r).mp
      rw [hqn', ← hc]
      exact hzero
    exact (Nat.dvd_prime hq).mp hrq |>.resolve_left hr.ne_one
  obtain ⟨k, hk⟩ := power_of_prime_support q N hq hNpos hsupport
  have hkpos : 0 < k := by
    by_contra hn
    have hk0 : k = 0 := by omega
    simp [hk0] at hk
    have := hq.two_le
    omega
  have hqN : q ∣ N := by rw [hk]; exact dvd_pow_self q (by omega)
  have hqp : q ∣ p + 1 := by
    by_contra hqp
    exact hh ⟨q, hq, dvd_trans hqN hNd, hqp, hq2⟩
  have hqnp : ¬q ∣ p := by
    intro hd
    have := Nat.dvd_sub hqp hd
    simp at this
    exact hq.ne_one this
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hv := padicValNat.pow_add_pow (p := q) (x := p) (y := 1)
    (Nat.odd_iff.mpr (hq.eq_two_or_odd.resolve_left hq2)) hqp hqnp
    (show Odd q from Nat.odd_iff.mpr (hq.eq_two_or_odd.resolve_left hq2))
  simp only [one_pow, padicValNat.self hq.one_lt] at hv
  rw [← hid, padicValNat.mul (by omega) hNpos.ne', hk, padicValNat.prime_pow] at hv
  have hk1 : k = 1 := by omega
  rw [hk1, pow_one] at hk
  omega

/-- The specialized Zsigmondy input, proved directly for the required prime exponents. -/
theorem proof_zsigmondy_dependency : ZsigmondyInput := by
  intro p q hp hq hq2 hex
  obtain ⟨r, hr, hd, hrp, hr2⟩ := prime_divisor_cofactor hp hq hq2 hex
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  have hz : (p : ZMod r) ^ q = -1 := by
    have he := (cast_zero_iff_dvd (p ^ q + 1) r).mpr hd
    push_cast at he
    exact eq_neg_of_add_eq_zero_left he
  have hne : (-1 : ZMod r) ≠ 1 := by
    letI : Fact (2 < r) := ⟨by have := hr.two_le; omega⟩
    exact ZMod.neg_one_ne_one
  have hsq : (p : ZMod r) ^ 2 ≠ 1 := by
    intro he
    rcases sq_eq_one_iff.mp he with he | he
    · rw [he, one_pow] at hz
      exact hne hz.symm
    · apply hrp
      apply (cast_zero_iff_dvd (p + 1) r).mp
      simp [he]
  have ho : orderOf (p : ZMod r) = 2 * q := by
    apply orderOf_eq_of_pow_and_pow_div_prime (by have := hq.two_le; omega)
    · rw [Nat.mul_comm 2 q, pow_mul, hz]
      ring
    · intro s hs hsd
      rcases hs.dvd_mul.mp hsd with hs2 | hsq'
      · have hs2' : s = 2 := (Nat.dvd_prime Nat.prime_two).mp hs2 |>.resolve_left hs.ne_one
        subst s
        simpa using (show (p : ZMod r) ^ q ≠ 1 by rw [hz]; exact hne)
      · have hsq'' : s = q := (Nat.dvd_prime hq).mp hsq' |>.resolve_left hs.ne_one
        subst s
        simpa [Nat.mul_div_cancel, hq.pos] using hsq
  exact ⟨r, (primitiveDivisor_iff_orderOf (by have := hq.two_le; omega)).mpr ⟨hr, ho⟩, hd⟩

theorem proof_8_3 : t8_3 := proof_8_3_from_zsigmondy proof_zsigmondy_dependency
theorem proof_8_4 : t8_4 := proof_8_4_from_zsigmondy proof_zsigmondy_dependency
theorem proof_8_5 : t8_5 := proof_8_5_from_zsigmondy proof_zsigmondy_dependency
theorem proof_9_3 : t9_3 := proof_9_3_from_zsigmondy proof_zsigmondy_dependency
end PrimeGPF
