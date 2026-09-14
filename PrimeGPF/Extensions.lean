import PrimeGPF.PrimeExponent
import PrimeGPF.Arithmetic

/-!
# Further extensions of the prime-GPF theory

This module formalizes the elementary/dynamical core of the September 2026
extensions.  The counting-constant refinements are documented separately.
-/
namespace PrimeGPF

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! ## Extension 5: explicit exponential escape -/

/-- Outside the unique exceptional pair `(2,3)`, the exponential output is at
least `2*q+1`, including the square-exponent case `q=2`. -/
theorem exp_ge_two_mul_add_one {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hex : (p, q) ≠ (2, 3)) : 2 * q + 1 ≤ exp p q := by
  by_cases hq2 : q = 2
  · subst q
    have hmod : exp p 2 % 4 = 1 := proof_8_2 p hp
    have hge : 2 ≤ exp p 2 := (output_spec .exp hp Nat.prime_two).1.two_le
    omega
  · exact (proof_8_3 p q hp hq hq2 hex).2

/-- Natural-number iterate of the anchored exponential translation. -/
def expIterNat (a q : ℕ) : ℕ → ℕ
  | 0 => q
  | n + 1 => exp a (expIterNat a q n)

theorem expIterNat_prime {a q : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q) :
    ∀ n, Nat.Prime (expIterNat a q n) := by
  intro n
  induction n with
  | zero => simpa [expIterNat] using hq
  | succ n ih =>
    simp only [expIterNat]
    exact (output_spec .exp ha ih).1

theorem expIterNat_eq_orbit_val (a q : Prime) :
    ∀ n, expIterNat a.val q.val n = (orbit (operate .exp a) q n).val := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [expIterNat, orbit]
    change exp a.val (expIterNat a.val q.val n) =
      exp a.val (orbit (operate .exp a) q n).val
    rw [ih]

/-- The exceptional anchored orbit is constant. -/
theorem expIterNat_two_three (n : ℕ) : expIterNat 2 3 n = 3 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [expIterNat, ih]
    exact proof_8_5.2.1

/-- Simultaneous invariant: the orbit never enters the exceptional state and
its shifted value doubles at every step. -/
theorem expIterNat_escape_invariant {a q : ℕ} (ha : Nat.Prime a)
    (hq : Nat.Prime q) (h0 : (a, q) ≠ (2, 3)) :
    ∀ n, (a, expIterNat a q n) ≠ (2, 3) ∧
      2 ^ n * (q + 1) ≤ expIterNat a q n + 1 := by
  intro n
  induction n with
  | zero =>
    constructor
    · simpa [expIterNat] using h0
    · simp [expIterNat]
  | succ n ih =>
    have hprime : Nat.Prime (expIterNat a q n) := expIterNat_prime ha hq n
    have hstep : 2 * expIterNat a q n + 1 ≤ exp a (expIterNat a q n) :=
      exp_ge_two_mul_add_one ha hprime ih.1
    constructor
    · intro hpair
      have hnext3 : expIterNat a q (n + 1) = 3 := congrArg Prod.snd hpair
      simp only [expIterNat] at hnext3
      have htwo := hprime.two_le
      omega
    · simp only [expIterNat]
      calc
        2 ^ (n + 1) * (q + 1) = 2 * (2 ^ n * (q + 1)) := by
          rw [pow_succ]
          ring
        _ ≤ 2 * (expIterNat a q n + 1) := Nat.mul_le_mul_left 2 ih.2
        _ ≤ exp a (expIterNat a q n) + 1 := by omega

/-- Equation (7): every nonexceptional anchored exponential orbit escapes at
least geometrically. -/
theorem extension5_exponential_escape {a q : ℕ} (ha : Nat.Prime a)
    (hq : Nat.Prime q) (h0 : (a, q) ≠ (2, 3)) (n : ℕ) :
    2 ^ n * (q + 1) ≤ expIterNat a q n + 1 :=
  (expIterNat_escape_invariant ha hq h0 n).2

/-- Exact discrete version of equation (8): if the `n`-th iterate is at most
`X`, then `n` is at most the base-two natural logarithm of the available
scale ratio. -/
theorem extension5_index_log_bound {a q X n : ℕ} (ha : Nat.Prime a)
    (hq : Nat.Prime q) (h0 : (a, q) ≠ (2, 3))
    (hX : expIterNat a q n ≤ X) :
    n ≤ Nat.log 2 ((X + 1) / (q + 1)) := by
  have hprod : 2 ^ n * (q + 1) ≤ X + 1 :=
    le_trans (extension5_exponential_escape ha hq h0 n) (by omega)
  have hpow : 2 ^ n ≤ (X + 1) / (q + 1) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < q + 1)).2
    simpa [Nat.mul_comm] using hprod
  exact Nat.le_log_of_pow_le (by decide : 1 < (2 : ℕ)) hpow

noncomputable def expVisitIndices (a q X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (Nat.log 2 ((X + 1) / (q + 1)) + 1)).filter
    (fun n => expIterNat a q n ≤ X)

/-- Finite-count form of equation (8). -/
theorem extension5_visit_count {a q X : ℕ} (ha : Nat.Prime a)
    (hq : Nat.Prime q) (h0 : (a, q) ≠ (2, 3)) :
    (∀ n, expIterNat a q n ≤ X → n ∈ expVisitIndices a q X) ∧
    (expVisitIndices a q X).card ≤
      1 + Nat.log 2 ((X + 1) / (q + 1)) := by
  constructor
  · intro n hn
    have hb := extension5_index_log_bound ha hq h0 hn
    simp [expVisitIndices, hb]
  · calc
      (expVisitIndices a q X).card ≤
          (Finset.range (Nat.log 2 ((X + 1) / (q + 1)) + 1)).card := by
        exact Finset.card_filter_le _ _
      _ = 1 + Nat.log 2 ((X + 1) / (q + 1)) := by simp [Nat.add_comm]

/-! ## Extension 6: iterated images shrink geometrically -/

noncomputable def primeStartsUpTo (Y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (Y + 1)).filter Nat.Prime

noncomputable def expCandidateOutputs (a k Y : ℕ) : Finset ℕ := by
  classical
  exact (primeStartsUpTo Y).image (fun q => expIterNat a q k)

noncomputable def expExceptionalOutputs (a : ℕ) : Finset ℕ := by
  classical
  exact if a = 2 then {3} else ∅

/-- The actual `k`-fold image values not exceeding `X`. -/
noncomputable def iteratedExpValuesUpTo (a k X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (X + 1)).filter (fun r =>
    Nat.Prime r ∧ ∃ q, Nat.Prime q ∧ expIterNat a q k = r)

/-- Equation (9), in the project's `primeCount` convention. -/
theorem extension6_image_card_bound {a k X : ℕ} (ha : Nat.Prime a) :
    (iteratedExpValuesUpTo a k X).card ≤
      Claims.primeCount ((X + 1) / 2 ^ k - 1) + (if a = 2 then 1 else 0) := by
  classical
  let Y := (X + 1) / 2 ^ k - 1
  have hsubset : iteratedExpValuesUpTo a k X ⊆
      expCandidateOutputs a k Y ∪ expExceptionalOutputs a := by
    intro r hr
    simp only [iteratedExpValuesUpTo, Finset.mem_filter, Finset.mem_range] at hr
    rcases hr.2.2 with ⟨q, hq, rfl⟩
    by_cases hex : (a, q) = (2, 3)
    · have ha2 : a = 2 := congrArg Prod.fst hex
      have hq3 : q = 3 := congrArg Prod.snd hex
      subst a
      subst q
      rw [expIterNat_two_three]
      simp [expExceptionalOutputs]
    · have hlower := extension5_exponential_escape ha hq hex k
      have houtle : expIterNat a q k ≤ X := by omega
      have hprod : 2 ^ k * (q + 1) ≤ X + 1 := le_trans hlower (by omega)
      have hqplus : q + 1 ≤ (X + 1) / 2 ^ k := by
        apply (Nat.le_div_iff_mul_le (pow_pos (by decide : 0 < (2 : ℕ)) k)).2
        simpa [Nat.mul_comm] using hprod
      have hqY : q ≤ Y := by
        dsimp [Y]
        omega
      have hqmem : q ∈ primeStartsUpTo Y := by
        simp [primeStartsUpTo, hq, hqY]
      have himg : expIterNat a q k ∈ expCandidateOutputs a k Y :=
        Finset.mem_image.mpr ⟨q, hqmem, rfl⟩
      exact Finset.mem_union_left _ himg
  have hcand : (expCandidateOutputs a k Y).card ≤ (primeStartsUpTo Y).card := by
    exact Finset.card_image_le
  have hcard := Finset.card_le_card hsubset
  have hunion := Finset.card_union_le (expCandidateOutputs a k Y) (expExceptionalOutputs a)
  have hexcard : (expExceptionalOutputs a).card = (if a = 2 then 1 else 0) := by
    simp [expExceptionalOutputs]
  have hstart : (primeStartsUpTo Y).card = Claims.primeCount Y := by
    simp [primeStartsUpTo, Claims.primeCount]
  dsimp [Y] at hstart ⊢
  omega

/-- Elementary bound used to rule out arbitrarily deep nonexceptional ancestry. -/
theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hdouble := Nat.mul_le_mul_left 2 ih
    nlinarith

def iteratedExpImage (a k r : ℕ) : Prop :=
  ∃ q, Nat.Prime q ∧ expIterNat a q k = r

/-- Equation (11): only the exceptional fixed point has ancestors of every
depth. -/
theorem extension6_deep_image_iff {a r : ℕ} (ha : Nat.Prime a)
    (hr : Nat.Prime r) :
    (∀ k, iteratedExpImage a k r) ↔ a = 2 ∧ r = 3 := by
  constructor
  · intro hdeep
    obtain ⟨q, hq, he⟩ := hdeep (r + 1)
    by_cases hex : (a, q) = (2, 3)
    · have ha2 : a = 2 := congrArg Prod.fst hex
      have hq3 : q = 3 := congrArg Prod.snd hex
      subst a
      subst q
      rw [expIterNat_two_three] at he
      exact ⟨rfl, he.symm⟩
    · have hlower := extension5_exponential_escape ha hq hex (r + 1)
      rw [he] at hlower
      have hpw : r + 2 ≤ 2 ^ (r + 1) := by
        simpa [Nat.add_assoc] using succ_le_two_pow (r + 1)
      have hmul : 2 ^ (r + 1) ≤ 2 ^ (r + 1) * (q + 1) := by
        have := Nat.mul_le_mul_left (2 ^ (r + 1)) (show 1 ≤ q + 1 by omega)
        simpa using this
      omega
  · rintro ⟨rfl, rfl⟩ k
    exact ⟨3, Nat.prime_three, expIterNat_two_three k⟩

/-! ## Extension 8: additive--exponential collision region -/

/-- Equation (14). -/
theorem extension8_add_exp_region {p q : ℕ} (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hcoll : add p q = exp p q) :
    (p, q) = (2, 3) ∨ q ≤ p := by
  by_cases hex : (p, q) = (2, 3)
  · exact Or.inl hex
  · right
    have hlower := exp_ge_two_mul_add_one hp hq hex
    rw [← hcoll] at hlower
    have hupper : add p q ≤ p + q + 1 := by
      simpa [add, output, kernel] using gpf_le (p + q + 1)
    omega

/-- For an odd composite integer, the greatest prime factor has cofactor at
least three. -/
theorem three_mul_gpf_le_of_odd_composite {n : ℕ} (hn : 1 < n)
    (hodd : n % 2 = 1) (hcomp : ¬ Nat.Prime n) :
    3 * gpf n ≤ n := by
  have hg := gpf_spec hn
  obtain ⟨s, hs⟩ := hg.2.1
  have hspos : 0 < s := by
    by_contra h
    have hs0 : s = 0 := by omega
    rw [hs0, Nat.mul_zero] at hs
    omega
  have hrodd : gpf n % 2 = 1 := by
    rcases hg.1.eq_two_or_odd with h2 | ho
    · rw [h2] at hg
      have hz := Nat.mod_eq_zero_of_dvd hg.2.1
      omega
    · exact ho
  have hsodd : s % 2 = 1 := by
    rw [hs] at hodd
    simpa [Nat.mul_mod, hrodd] using hodd
  have hsne : s ≠ 1 := by
    intro hs1
    apply hcomp
    have he : n = gpf n := by simpa [hs1] using hs
    simpa [he] using hg.1
  have hs3 : 3 ≤ s := by omega
  rw [hs]
  nlinarith

/-- Equation (15). -/
theorem extension8_composite_region {p q : ℕ} (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hcoll : add p q = exp p q) (hcomp : ¬ Nat.Prime (p + q + 1)) :
    5 * q + 2 ≤ p := by
  have hpo := hp.eq_two_or_odd.resolve_left hp2
  have hqo := hq.eq_two_or_odd.resolve_left hq2
  have hodd : (p + q + 1) % 2 = 1 := by omega
  have hn : 1 < p + q + 1 := by have := hp.two_le; have := hq.two_le; omega
  have hthree := three_mul_gpf_le_of_odd_composite hn hodd hcomp
  have hthree' : 3 * add p q ≤ p + q + 1 := by
    simpa [add, output, kernel] using hthree
  have hex : (p, q) ≠ (2, 3) := by intro h; exact hp2 (congrArg Prod.fst h)
  have hlower := exp_ge_two_mul_add_one hp hq hex
  rw [← hcoll] at hlower
  omega

/-- Equation (16), including exclusion of the exceptional pair from a triple
collision. -/
theorem extension8_triple_region {p q : ℕ} (hp : Nat.Prime p)
    (hq : Nat.Prime q) (ham : add p q = mul p q)
    (hae : add p q = exp p q) :
    q ≤ min p ((gpf (p ^ 2 + p - 1) - 1) / 2) := by
  have hex : (p, q) ≠ (2, 3) := by
    intro h
    have hp2 : p = 2 := congrArg Prod.fst h
    have hq3 : q = 3 := congrArg Prod.snd h
    subst p
    subst q
    norm_num [add, mul, output, kernel, gpf, scan] at ham
  have hqp : q ≤ p := (extension8_add_exp_region hp hq hae).resolve_left hex
  let r := add p q
  have hr : Nat.Prime r := (output_spec .add hp hq).1
  have hda : r ∣ p + q + 1 := (output_spec .add hp hq).2.1
  have hdm : r ∣ p * q + 1 := by
    have hm := (output_spec .mul hp hq).2.1
    simpa [r, ham] using hm
  have hpoly : r ∣ p ^ 2 + p - 1 := collision_divisor hda hdm
  have hpolypos : 1 < p ^ 2 + p - 1 := by
    have hp2 := hp.two_le
    nlinarith
  have hrle : r ≤ gpf (p ^ 2 + p - 1) :=
    (gpf_spec hpolypos).2.2 r hr hpoly
  have hlower := exp_ge_two_mul_add_one hp hq hex
  have hlower' : 2 * q + 1 ≤ r := by simpa [r, hae] using hlower
  have hqg : q ≤ (gpf (p ^ 2 + p - 1) - 1) / 2 := by omega
  exact Nat.le_min hqp hqg

/-! ## Extension 10: algebraic separation from H(p,q)=P⁺(p+q) -/

def homogeneousAdd (p q : ℕ) : ℕ := gpf (p + q)

def homogeneousOperate (p q : Prime) : Prime :=
  ⟨homogeneousAdd p.val q.val,
    (gpf_spec (by have := p.property.two_le; have := q.property.two_le; omega)).1⟩

/-- Every prime is idempotent for the homogeneous additive GPF magma. -/
theorem homogeneousAdd_idempotent {p : ℕ} (hp : Nat.Prime p) :
    homogeneousAdd p p = p := by
  apply gpf_eq_of_spec (by have := hp.two_le; omega)
  refine ⟨hp, ?_, ?_⟩
  · refine ⟨2, ?_⟩
    omega
  · intro s hs hd
    have hd' : s ∣ 2 * p := by simpa [homogeneousAdd, two_mul] using hd
    rcases hs.dvd_mul.mp hd' with h2 | hsp
    · have hs2 : s = 2 := (Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_left hs.ne_one
      subst s
      exact hp.two_le
    · exact Nat.le_of_dvd hp.pos hsp

@[simp] theorem homogeneousOperate_idempotent (p : Prime) :
    homogeneousOperate p p = p := by
  apply Subtype.ext
  exact homogeneousAdd_idempotent p.property

/-- Function-level definition of a magma homomorphism, sufficient for the
algebraic separation statement. -/
def IsMagmaHom (src dst : Prime → Prime → Prime) (f : Prime → Prime) : Prop :=
  ∀ p q, f (src p q) = dst (f p) (f q)

/-- No homomorphism exists from the idempotent homogeneous magma into any of
`A`, `M`, or `E`. -/
theorem extension10_no_hom_from_homogeneous (o : Op) (f : Prime → Prime) :
    ¬ IsMagmaHom homogeneousOperate (operate o) f := by
  intro hf
  let p : Prime := ⟨2, Nat.prime_two⟩
  have h := hf p p
  rw [homogeneousOperate_idempotent] at h
  have hv := congrArg Subtype.val h
  cases o with
  | add =>
      change (f p).val = add (f p).val (f p).val at hv
      exact add_not_idempotent (f p).property hv.symm
  | mul =>
      change (f p).val = mul (f p).val (f p).val at hv
      exact mul_ne_left (f p).property (f p).property hv.symm
  | exp =>
      change (f p).val = exp (f p).val (f p).val at hv
      exact exp_ne_left (f p).property (f p).property hv.symm

/-- Conversely, no injective homomorphism from any of `A`, `M`, or `E` can
land in the homogeneous idempotent magma. -/
theorem extension10_no_injective_hom_to_homogeneous (o : Op) (f : Prime → Prime)
    (hinj : Function.Injective f) :
    ¬ IsMagmaHom (operate o) homogeneousOperate f := by
  intro hf
  let p : Prime := ⟨2, Nat.prime_two⟩
  have h := hf p p
  rw [homogeneousOperate_idempotent] at h
  have hsrc : operate o p p = p := hinj h
  have hv := congrArg Subtype.val hsrc
  cases o with
  | add =>
      change add p.val p.val = p.val at hv
      exact add_not_idempotent p.property hv
  | mul =>
      change mul p.val p.val = p.val at hv
      exact mul_ne_left p.property p.property hv
  | exp =>
      change exp p.val p.val = p.val at hv
      exact exp_ne_left p.property p.property hv

end PrimeGPF
