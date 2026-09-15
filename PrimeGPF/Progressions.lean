import PrimeGPF.Unbounded

/-!
# Arithmetic-progression reductions

This module gives compiler-verified exact reductions of the additive and
multiplicative divisibility conditions to a single nonzero residue class.
The algebraic reductions are unconditional; the only remaining analytic input
is isolated explicitly in `PrimeAPInput`, which packages the required
prime-number-theorem-for-arithmetic-progressions asymptotic.
-/
namespace PrimeGPF
open Claims

/-- A nondegenerate affine congruence modulo a prime has one nonzero residue
class of solutions.  The hypotheses say that both the slope and constant term
are nonzero modulo `r`. -/
theorem affine_residue {a b r : ℕ} (hr : Nat.Prime r)
    (ha : (a : ZMod r) ≠ 0) (hb : (b : ZMod r) ≠ 0) :
    ∃ c : ℕ, 0 < c ∧ c < r ∧ ∀ q, r ∣ a * q + b ↔ q % r = c := by
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  let z : ZMod r := -(b : ZMod r) / (a : ZMod r)
  have hz0 : z ≠ 0 := div_ne_zero (neg_ne_zero.mpr hb) ha
  have hz : (a : ZMod r) * z + b = 0 := by
    dsimp [z]
    field_simp [ha] ; ring
  refine ⟨z.val, (ZMod.val_pos).mpr hz0, ZMod.val_lt z, ?_⟩
  intro q
  have heq : (q : ZMod r) = z ↔ q % r = z.val := by
    have hc := cast_eq_iff_mod q z.val r
    simpa only [ZMod.natCast_zmod_val, Nat.mod_eq_of_lt (ZMod.val_lt z)] using hc
  rw [← heq, ← cast_zero_iff_dvd]
  push_cast
  constructor
  · intro h
    apply mul_left_cancel₀ ha
    linear_combination h - hz
  · intro h
    simpa only [h] using hz

/-- For distinct prime anchor/output, the multiplicative divisibility condition
`r ∣ a*q+1` is exactly one reduced residue class modulo `r`; consequently the
corresponding divisor count is the arithmetic-progression count. -/
theorem multiplicative_progression {a r : ℕ} (ha : Nat.Prime a)
    (hr : Nat.Prime r) (har : a ≠ r) :
    ∃ c, 0 < c ∧ c < r ∧
      (∀ q, r ∣ a * q + 1 ↔ q % r = c) ∧
      (∀ x, divisorCount .mul a r x = apCount r c x) := by
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  have ha0 : (a : ZMod r) ≠ 0 := by
    intro hz
    have hd := (cast_zero_iff_dvd a r).mp hz
    rcases (Nat.dvd_prime ha).mp hd with h | h
    · exact hr.ne_one h
    · exact har h.symm
  obtain ⟨c, hc0, hcr, hc⟩ := affine_residue (b := 1) hr ha0 (by simp)
  refine ⟨c, hc0, hcr, hc, ?_⟩
  intro x
  unfold divisorCount apCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro q hq
  simp only [kernel, hc q, Nat.mod_eq_of_lt hcr]

/-- In the nondegenerate additive case, `r ∣ a+q+1` is likewise one nonzero
residue class modulo `r`, giving the exact additive divisor-count reduction. -/
theorem additive_progression {a r : ℕ} (hr : Nat.Prime r)
    (har : (a + 1) % r ≠ 0) :
    ∃ c, 0 < c ∧ c < r ∧
      (∀ q, r ∣ a + q + 1 ↔ q % r = c) ∧
      (∀ x, divisorCount .add a r x = apCount r c x) := by
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  have hb : ((a + 1 : ℕ) : ZMod r) ≠ 0 := by
    intro hz
    exact har (Nat.mod_eq_zero_of_dvd ((cast_zero_iff_dvd (a + 1) r).mp hz))
  obtain ⟨c, hc0, hcr, hc⟩ := affine_residue (a := 1) hr (by simp) hb
  have hc' : ∀ q, r ∣ a + q + 1 ↔ q % r = c := by
    intro q
    simpa only [one_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc q
  refine ⟨c, hc0, hcr, hc', ?_⟩
  intro x
  unfold divisorCount apCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro q hq
  simp only [kernel, hc' q, Nat.mod_eq_of_lt hcr]

/-- In the degenerate additive case `r ∣ a+1`, divisibility of the kernel by
`r` forces the prime input itself to be `r`. -/
theorem additive_degenerate_progression {a r : ℕ} (hr : Nat.Prime r)
    (har : (a + 1) % r = 0) (q : ℕ) (hq : Nat.Prime q) :
    r ∣ a + q + 1 ↔ q = r := by
  have hd : r ∣ a + 1 := Nat.dvd_of_mod_eq_zero har
  have he : r ∣ a + q + 1 ↔ r ∣ q := by
    rw [show a + q + 1 = (a + 1) + q by omega]
    simp only [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, har, zero_add, Nat.mod_mod]
  rw [he]
  constructor
  · intro h
    rcases (Nat.dvd_prime hq).mp h with h | h
    · exact False.elim (hr.ne_one h)
    · exact h.symm
  · rintro rfl
    exact dvd_refl _

/-- Analytic PNT-in-arithmetic-progressions input used by `proof_6_1_from_PNT_AP`.
Keeping it as an explicit proposition separates the exact compiler-verified
congruence reductions above from the external asymptotic hypothesis. -/
def PrimeAPInput : Prop := ∀ r c, Nat.Prime r → r ≠ 2 →
  0 < c → c < r → APAsymptotic r c

/-- Conditional assembly of theorem 6.1 from the exact residue-class
reductions and the explicit `PrimeAPInput` asymptotic hypothesis. -/
theorem proof_6_1_from_PNT_AP (H : PrimeAPInput) : t6_1 := by
  intro a r ha hr hr2
  refine ⟨?_, ?_, ?_⟩
  · intro har
    obtain ⟨c, hc0, hcr, hc, hcount⟩ := multiplicative_progression ha hr har
    exact ⟨c, hc0, hcr, hc, hcount, H r c hr hr2 hc0 hcr⟩
  · intro har
    obtain ⟨c, hc0, hcr, hc, hcount⟩ := additive_progression hr har
    exact ⟨c, hc0, hcr, hc, hcount, H r c hr hr2 hc0 hcr⟩
  · intro har q hq
    exact additive_degenerate_progression hr har q hq

end PrimeGPF
