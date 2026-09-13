import PrimeGPF.Arithmetic
import PrimeGPF.Dynamics

/-! Bridges between the draft's modular predicates and finite-field orders.
New proof scripts, not compiler-verified. -/
namespace PrimeGPF
open Claims

theorem cast_eq_iff_mod (a b r : ℕ) :
    (a : ZMod r) = (b : ZMod r) ↔ a % r = b % r :=
  ZMod.natCast_eq_natCast_iff' a b r

theorem cast_zero_iff_dvd (a r : ℕ) : (a : ZMod r) = 0 ↔ r ∣ a :=
  ZMod.natCast_zmod_eq_zero_iff_dvd a r

theorem cast_pow_one_iff (p r k : ℕ) :
    (p : ZMod r) ^ k = 1 ↔ p ^ k % r = 1 % r := by
  simpa only [Nat.cast_pow, Nat.cast_one] using cast_eq_iff_mod (p ^ k) 1 r

theorem exactOrder_iff_orderOf {p r k : ℕ} (hk : 0 < k) :
    ExactOrder p r k ↔ orderOf (p : ZMod r) = k := by
  rw [orderOf_eq_iff hk]
  constructor
  · rintro ⟨_, he, hmin⟩
    exact ⟨(cast_pow_one_iff p r k).mpr he,
      fun j hj hj0 he' => hmin j hj0 hj ((cast_pow_one_iff p r j).mp he')⟩
  · rintro ⟨he, hmin⟩
    exact ⟨hk, (cast_pow_one_iff p r k).mp he,
      fun j hj0 hj he' => hmin j hj hj0 ((cast_pow_one_iff p r j).mpr he')⟩

theorem primitiveDivisor_iff_orderOf {r p k : ℕ} (hk : 0 < k) :
    PrimitiveDivisor r p k ↔ Nat.Prime r ∧ orderOf (p : ZMod r) = k := by
  constructor
  · rintro ⟨hr, he, hmin⟩
    exact ⟨hr, (exactOrder_iff_orderOf hk).mp ⟨hk, he, hmin⟩⟩
  · rintro ⟨hr, ho⟩
    have h := (exactOrder_iff_orderOf hk).mpr ho
    exact ⟨hr, h.2⟩

/-- Positivity is essential; PrimitiveDivisor itself permits k=0. -/
theorem primitive_order_dvd {r p k : ℕ} (hk : 0 < k)
    (h : PrimitiveDivisor r p k) : k ∣ r - 1 := by
  letI : Fact (Nat.Prime r) := ⟨h.1⟩
  have he : (p : ZMod r) ^ k = 1 := (cast_pow_one_iff p r k).mpr h.2.1
  have hp0 : (p : ZMod r) ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by omega : k ≠ 0)] at he
    exact zero_ne_one he
  have ho := ((primitiveDivisor_iff_orderOf hk).mp h).2
  rw [← ho]
  exact ZMod.orderOf_dvd_card_sub_one hp0

/-- A positive divisor of r-1 forces r to be one modulo that divisor. -/
theorem mod_eq_one_of_dvd_pred {r k : ℕ} (hr : 1 ≤ r)
    (hk : 1 < k) (hd : k ∣ r - 1) : r % k = 1 := by
  have he : r - 1 + 1 = r := by omega
  have hz := Nat.mod_eq_zero_of_dvd hd
  calc
    r % k = (r - 1 + 1) % k := by rw [he]
    _ = 1 := by rw [Nat.add_mod, hz]; simp [Nat.mod_eq_of_lt hk]

/-- x^(2^m)=-1 in odd characteristic has exact order 2^(m+1). -/
theorem dyadic_order {r p m : ℕ} (hr : Nat.Prime r) (hr2 : r ≠ 2)
    (hd : r ∣ p ^ (2 ^ m) + 1) :
    ExactOrder p r (2 ^ (m + 1)) ∧
    PrimitiveDivisor r p (2 ^ (m + 1)) ∧ r % (2 ^ (m + 1)) = 1 := by
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzero : (p : ZMod r) ^ (2 ^ m) + 1 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
      using (cast_zero_iff_dvd (p ^ (2 ^ m) + 1) r).mpr hd
  have hneg : (p : ZMod r) ^ (2 ^ m) = -1 := eq_neg_of_add_eq_zero_left hzero
  have hne : (-1 : ZMod r) ≠ 1 := by
    letI : Fact (2 < r) := ⟨by have := hr.two_le; omega⟩
    exact ZMod.neg_one_ne_one
  have hnot : (p : ZMod r) ^ (2 ^ m) ≠ 1 := by rw [hneg]; exact hne
  have hfin : (p : ZMod r) ^ (2 ^ (m + 1)) = 1 := by
    rw [pow_succ, pow_mul, hneg]
    ring
  have ho : orderOf (p : ZMod r) = 2 ^ (m + 1) := orderOf_eq_prime_pow hnot hfin
  have hk : 0 < 2 ^ (m + 1) := pow_pos (by decide) _
  have hex := (exactOrder_iff_orderOf hk).mpr ho
  have hprim : PrimitiveDivisor r p (2 ^ (m + 1)) := ⟨hr, hex.2⟩
  refine ⟨hex, hprim, mod_eq_one_of_dvd_pred (by have := hr.two_le; omega) ?_
    (primitive_order_dvd hk hprim)⟩
  rw [pow_succ]
  have : 0 < 2 ^ m := pow_pos (by decide) _
  omega

theorem proof_5_2 : t5_2 := by
  intro p hp
  have hr := (output_spec .mul hp hp).1
  have hd : mul p p ∣ p ^ 2 + 1 := by
    simpa only [kernel, pow_two] using (output_spec .mul hp hp).2.1
  have hn : mul p p ≠ 2 := by
    simpa only [exp, mul, output, kernel, pow_two] using square_output_ne_two hp
  have hh := dyadic_order (p := p) (m := 1) hr hn (by simpa using hd)
  simpa using And.intro hh.2.2 hh.2.1

theorem proof_5_3 : t5_3 := proof_5_3_from_5_2 proof_5_2

theorem proof_8_2 : t8_2 := by
  intro p hp
  rw [(proof_9_1 p hp).2]
  exact (proof_5_2 p hp).1

theorem proof_5_5_corrected : t5_5_corrected := by
  intro p q m hp hq hm
  dsimp only
  intro hr2 hqmod
  let r := mul p q
  have hr : Nat.Prime r := (output_spec .mul hp hq).1
  have hd : r ∣ p * q + 1 := (output_spec .mul hp hq).2.1
  have hmpos : 0 < 2 ^ m := pow_pos (by decide) _
  have hexp : 2 ^ m - 1 + 1 = 2 ^ m := by omega
  have hpw : p * p ^ (2 ^ m - 1) = p ^ (2 ^ m) := by
    calc
      p * p ^ (2 ^ m - 1) = p ^ (2 ^ m - 1 + 1) := by rw [pow_succ]; ring
      _ = p ^ (2 ^ m) := by rw [hexp]
  have he : (p * q + 1) % r = (p ^ (2 ^ m) + 1) % r := by
    calc
      (p * q + 1) % r = (p % r * (q % r) % r + 1 % r) % r := by
        rw [Nat.add_mod (p * q) 1 r, Nat.mul_mod p q r]
      _ = (p % r * (p ^ (2 ^ m - 1) % r) % r + 1 % r) % r :=
        congrArg (fun t : ℕ => (p % r * t % r + 1 % r) % r) hqmod
      _ = (p * p ^ (2 ^ m - 1) + 1) % r := by
        rw [Nat.add_mod (p * p ^ (2 ^ m - 1)) 1 r,
          Nat.mul_mod p (p ^ (2 ^ m - 1)) r]
      _ = (p ^ (2 ^ m) + 1) % r := by rw [hpw]
  have hd' : r ∣ p ^ (2 ^ m) + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    rw [← he]
    exact Nat.mod_eq_zero_of_dvd hd
  have h := dyadic_order hr hr2 hd'
  exact ⟨h.1, h.2.2, h.2.1, hd'⟩

end PrimeGPF
