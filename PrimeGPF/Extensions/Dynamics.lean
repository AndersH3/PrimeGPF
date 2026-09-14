import PrimeGPF.PrimeExponent

/-! Quantitative extensions 5 and 6. No additional mathematical hypotheses. -/
namespace PrimeGPF.Extensions
open Claims

theorem exp_double {a q : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q)
    (hex : (a, q) ≠ (2, 3)) : 2 * q + 1 ≤ exp a q := by
  by_cases hq2 : q = 2
  · subst q
    have hmod := proof_8_2 a ha
    have hp := (output_spec .exp ha Nat.prime_two).1.two_le
    change 2 ≤ exp a 2 at hp
    omega
  · exact (proof_8_3 a q ha hq hq2 hex).2

abbrev expIter (a q n : ℕ) := orbit (exp a) q n

theorem expIter_prime {a q : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q) (n : ℕ) :
    Nat.Prime (expIter a q n) := by
  induction n with
  | zero => exact hq
  | succ n ih => exact (output_spec .exp ha ih).1

theorem expIter_exception (n : ℕ) : expIter 2 3 n = 3 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change exp 2 (expIter 2 3 n) = 3
    rw [ih]
    exact proof_8_5.2.1

theorem expIter_nonexception {a q : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q)
    (hex : (a, q) ≠ (2, 3)) (n : ℕ) : (a, expIter a q n) ≠ (2, 3) := by
  induction n with
  | zero => exact hex
  | succ n ih =>
    have hb := exp_double ha (expIter_prime ha hq n) ih
    have hp := (expIter_prime ha hq n).two_le
    intro he
    have he' := congrArg Prod.snd he
    change exp a (expIter a q n) = 3 at he'
    omega

/-- Extension 5: a uniform exponential lower bound, with the unique exception removed. -/
theorem expIter_growth {a q : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q)
    (hex : (a, q) ≠ (2, 3)) (n : ℕ) :
    2 ^ n * (q + 1) ≤ expIter a q n + 1 := by
  induction n with
  | zero => simp [expIter, orbit]
  | succ n ih =>
    have hb := exp_double ha (expIter_prime ha hq n) (expIter_nonexception ha hq hex n)
    change 2 ^ (n + 1) * (q + 1) ≤ exp a (expIter a q n) + 1
    rw [pow_succ]
    nlinarith

theorem expIter_strictMono {a q : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q)
    (hex : (a, q) ≠ (2, 3)) : StrictMono (expIter a q) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hb := exp_double ha (expIter_prime ha hq n) (expIter_nonexception ha hq hex n)
  change expIter a q n < exp a (expIter a q n)
  omega

theorem expIter_escape {a q B n : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q)
    (hex : (a, q) ≠ (2, 3)) (hn : B + 1 < 2 ^ n * (q + 1)) :
    B < expIter a q n := by
  have := expIter_growth ha hq hex n
  omega

theorem expIter_index_bound {a q X n : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q)
    (hex : (a, q) ≠ (2, 3)) (hn : expIter a q n ≤ X) :
    2 ^ n ≤ (X + 1) / (q + 1) := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < q + 1)).mpr
  exact (expIter_growth ha hq hex n).trans (by omega)

theorem expIter_seed_le {a q : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q) (n : ℕ) :
    q ≤ expIter a q n := by
  by_cases hex : (a, q) = (2, 3)
  · have ha2 := congrArg Prod.fst hex
    have hq3 := congrArg Prod.snd hex
    simp only [Prod.fst, Prod.snd] at ha2 hq3
    subst a; subst q
    rw [expIter_exception]
  · have hg := expIter_growth ha hq hex n
    have hp : 1 ≤ 2 ^ n := Nat.succ_le_of_lt (pow_pos (by norm_num) n)
    nlinarith

def iterImage (a k : ℕ) : Set ℕ := {r | ∃ q, Nat.Prime q ∧ expIter a q k = r}

/-- Extension 6: every nonexceptional output has an explicit finite ancestry bound. -/
theorem ancestry_bound {a r k : ℕ} (ha : Nat.Prime a)
    (hex : (a, r) ≠ (2, 3)) (hr : r ∈ iterImage a k) : 3 * 2 ^ k ≤ r + 1 := by
  obtain ⟨q, hq, hqr⟩ := hr
  have hseed : (a, q) ≠ (2, 3) := by
    intro he
    have ha2 := congrArg Prod.fst he
    have hq3 := congrArg Prod.snd he
    simp only [Prod.fst, Prod.snd] at ha2 hq3
    subst a; subst q
    rw [expIter_exception] at hqr
    exact hex (by simp [← hqr])
  have hg := expIter_growth ha hq hseed k
  have := hq.two_le
  rw [hqr] at hg
  nlinarith

/-- The only prime with arbitrarily deep ancestry is the exceptional fixed point. -/
theorem infinite_ancestry_iff {a r : ℕ} (ha : Nat.Prime a) :
    (∀ k, r ∈ iterImage a k) ↔ a = 2 ∧ r = 3 := by
  constructor
  · intro hr
    by_contra he
    have hex : (a, r) ≠ (2, 3) := by
      intro h
      exact he ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    have hb := ancestry_bound ha hex (hr (r + 1))
    have hp : r + 1 < 2 ^ (r + 1) := Nat.lt_two_pow_self
    omega
  · rintro ⟨rfl, rfl⟩ k
    exact ⟨3, Nat.prime_three, expIter_exception k⟩

noncomputable def primesTo (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter Nat.Prime

@[simp] theorem mem_primesTo {q X : ℕ} : q ∈ primesTo X ↔ Nat.Prime q ∧ q ≤ X := by
  classical
  simp only [primesTo, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h, hp⟩
    exact ⟨hp, by omega⟩
  · rintro ⟨hp, h⟩
    exact ⟨by omega, hp⟩

noncomputable def imageTo (a k X : ℕ) : Finset ℕ := by
  classical
  exact (primesTo X).filter (fun r => r ∈ iterImage a k)

/-- Exact finite-cutoff image bound; integer division supplies the floor. -/
theorem image_count_bound {a : ℕ} (ha : Nat.Prime a) (k X : ℕ) :
    (imageTo a k X).card ≤
      primeCount ((X + 1) / 2 ^ k - 1) + if a = 2 then 1 else 0 := by
  classical
  let N := (X + 1) / 2 ^ k - 1
  let S := (primesTo N).image (fun q => expIter a q k)
  let T : Finset ℕ := if a = 2 then {3} else ∅
  have hsub : imageTo a k X ⊆ S ∪ T := by
    intro r hr
    obtain ⟨hrX, q, hq, hqr⟩ := Finset.mem_filter.mp hr
    have hrle := (mem_primesTo.mp hrX).2
    by_cases hex : (a, q) = (2, 3)
    · have ha2 := congrArg Prod.fst hex
      have hq3 := congrArg Prod.snd hex
      simp only [Prod.fst, Prod.snd] at ha2 hq3
      subst a; subst q
      rw [expIter_exception] at hqr
      apply Finset.mem_union_right
      simp [T, ← hqr]
    · have hg := expIter_growth ha hq hex k
      rw [hqr] at hg
      have hdiv : q + 1 ≤ (X + 1) / 2 ^ k := by
        apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ k)).mpr
        nlinarith
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨q, mem_primesTo.mpr ⟨hq, by dsimp [N]; omega⟩, hqr⟩
  calc
    _ ≤ (S ∪ T).card := Finset.card_le_card hsub
    _ ≤ S.card + T.card := Finset.card_union_le _ _
    _ ≤ (primesTo N).card + T.card := Nat.add_le_add_right (Finset.card_image_le) _
    _ = _ := by by_cases h : a = 2 <;> simp [primesTo, primeCount, N, T, h]

/-- Extension 5, logarithmic visit count, with the floor expressed by Nat.log. -/
theorem expIter_visit_count {a q : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q)
    (hex : (a, q) ≠ (2, 3)) (X : ℕ) :
    Set.ncard {n | expIter a q n ≤ X} ≤ Nat.log 2 ((X + 1) / (q + 1)) + 1 := by
  let L := Nat.log 2 ((X + 1) / (q + 1))
  have hs : {n | expIter a q n ≤ X} ⊆ (Finset.range (L + 1) : Set ℕ) := by
    intro n hn
    have hb := Nat.le_log_of_pow_le (by norm_num : 1 < 2)
      (expIter_index_bound ha hq hex hn)
    exact Finset.mem_range.mpr (by dsimp [L]; omega)
  simpa [L] using Set.ncard_le_ncard hs (Finset.finite_toSet _)

theorem ancestry_log_bound {a r k : ℕ} (ha : Nat.Prime a)
    (hex : (a, r) ≠ (2, 3)) (hr : r ∈ iterImage a k) :
    k ≤ Nat.log 2 ((r + 1) / 3) := by
  apply Nat.le_log_of_pow_le (by norm_num)
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).mpr
  simpa [Nat.mul_comm] using ancestry_bound ha hex hr

end PrimeGPF.Extensions
