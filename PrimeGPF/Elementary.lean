import PrimeGPF.Statements

/-! Proof scripts for elementary results. All scripts remain uncompiled. -/
namespace PrimeGPF
open Claims

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem proof_3_1 : t3_1 := by
  intro o p q hp hq
  exact ⟨(output_spec o hp hq).1, (output_spec o hp hq).2.1⟩

theorem add_comm (p q : ℕ) : add p q = add q p := by
  simp only [add, output, kernel, Nat.add_comm p q]

theorem mul_comm (p q : ℕ) : mul p q = mul q p := by
  simp only [mul, output, kernel, Nat.mul_comm p q]

theorem proof_3_2 : t3_2 := by
  refine ⟨fun p q _ _ => add_comm p q, fun p q _ _ => mul_comm p q, ?_⟩
  intro h
  have hh := h 2 3 Nat.prime_two Nat.prime_three
  norm_num [output, kernel, gpf, scan] at hh

theorem proof_3_3 : t3_3 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hh := h 2 2 5 Nat.prime_two Nat.prime_two Nat.prime_five
    norm_num [output, kernel, gpf, scan] at hh
  · intro h
    have hh := h 2 2 3 Nat.prime_two Nat.prime_two Nat.prime_three
    norm_num [output, kernel, gpf, scan] at hh
  · intro h
    have hh := h 2 2 2 Nat.prime_two Nat.prime_two Nat.prime_two
    norm_num [output, kernel, gpf, scan] at hh

theorem mul_ne_left {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    mul p q ≠ p := by
  intro he
  have hd := (output_spec .mul hp hq).2.1
  change mul p q ∣ p * q + 1 at hd
  rw [he] at hd
  have hh := Nat.mod_eq_zero_of_dvd hd
  simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hp.one_lt] at hh

theorem mul_ne_right {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    mul p q ≠ q := by rw [mul_comm]; exact mul_ne_left hq hp

theorem add_not_idempotent {p : ℕ} (hp : Nat.Prime p) : add p p ≠ p := by
  intro he
  have hd := (output_spec .add hp hp).2.1
  change add p p ∣ p + p + 1 at hd
  rw [he] at hd
  have hh := Nat.mod_eq_zero_of_dvd hd
  simp [Nat.add_mod, Nat.mod_eq_of_lt hp.one_lt] at hh

theorem exp_ne_left {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    exp p q ≠ p := by
  intro he
  have hd := (output_spec .exp hp hq).2.1
  change exp p q ∣ p ^ q + 1 at hd
  rw [he] at hd
  have hh := Nat.mod_eq_zero_of_dvd hd
  simp [Nat.add_mod, Nat.pow_mod, hq.ne_zero, Nat.mod_eq_of_lt hp.one_lt] at hh

theorem proof_3_4 : t3_4 := by
  refine ⟨fun _ _ hp hq => ⟨mul_ne_left hp hq, mul_ne_right hp hq⟩,
    fun _ hp => add_not_idempotent hp, fun _ _ hp hq => exp_ne_left hp hq, ?_⟩
  intro o h
  obtain ⟨e, he, hid⟩ := h
  have hh := (hid e he).1
  cases o with
  | add => exact add_not_idempotent he hh
  | mul => exact mul_ne_left he he hh
  | exp => exact exp_ne_left he he hh

theorem odd_add_closed : OddClosed .add := by
  intro p q hp hq hp2 hq2 he
  have ho := hp.eq_two_or_odd.resolve_left hp2
  have ho' := hq.eq_two_or_odd.resolve_left hq2
  have hd := (output_spec .add hp hq).2.1
  rw [he] at hd
  have hh := Nat.mod_eq_zero_of_dvd hd
  norm_num [kernel, Nat.add_mod, ho, ho'] at hh

theorem odd_mul_not_closed : ¬ OddClosed .mul := by
  intro h
  have hh := h 3 5 Nat.prime_three Nat.prime_five (by decide) (by decide)
  norm_num [output, kernel, gpf, scan] at hh

theorem proof_3_6 : t3_6 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hh := h 2 2 7 Nat.prime_two Nat.prime_two Nat.prime_seven (by
      norm_num [output, kernel, gpf, scan])
    norm_num at hh
  · intro h
    have hh := h 2 2 7 Nat.prime_two Nat.prime_two Nat.prime_seven (by
      norm_num [output, kernel, gpf, scan])
    norm_num at hh
  · intro h
    have hh := h 2 2 3 Nat.prime_two Nat.prime_two Nat.prime_three
    norm_num [output, kernel, gpf, scan] at hh
  · intro h
    have hh := h 2 2 2 Nat.prime_two Nat.prime_two Nat.prime_two
    norm_num [output, kernel, gpf, scan] at hh

theorem proof_3_7 : t3_7 := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h
  all_goals
    have hh := h 2 2 2 Nat.prime_two Nat.prime_two Nat.prime_two
    norm_num [output, kernel, gpf, scan] at hh

theorem proof_3_8 : t3_8 := by
  intro o
  cases o with
  | add =>
    constructor
    · intro h
      have hh := h 3 5 3 Nat.prime_three Nat.prime_five Nat.prime_three (by decide)
      norm_num [output, kernel, gpf, scan] at hh
    · intro h
      have hh := h 3 5 3 Nat.prime_three Nat.prime_five Nat.prime_three (by decide)
      norm_num [output, kernel, gpf, scan] at hh
  | mul =>
    constructor
    · intro h
      have hh := h 3 5 3 Nat.prime_three Nat.prime_five Nat.prime_three (by decide)
      norm_num [output, kernel, gpf, scan] at hh
    · intro h
      have hh := h 3 5 3 Nat.prime_three Nat.prime_five Nat.prime_three (by decide)
      norm_num [output, kernel, gpf, scan] at hh
  | exp =>
    constructor
    · intro h
      have hh := h 5 7 2 Nat.prime_five Nat.prime_seven Nat.prime_two (by decide)
      norm_num [output, kernel, gpf, scan] at hh
    · intro h
      have hh := h 2 3 2 Nat.prime_two Nat.prime_three Nat.prime_two (by decide)
      norm_num [output, kernel, gpf, scan] at hh

theorem proof_4_1 : t4_1 := by
  intro o p q r hp hq hr
  exact gpf_fiber (kernel_gt_one o hp hq) hr

theorem proof_4_2 : t4_2 := by
  intro o p q hp hq
  exact ⟨gpf_eq_self_iff (kernel_gt_one o hp hq),
    gpf_eq_two_iff (kernel_gt_one o hp hq)⟩

/-- Theorem 4.3(b), equivalence part, separately tracked from the parity claim. -/
theorem mul_two_iff {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    mul p q = 2 ↔ ∃ k, 0 < k ∧ p * q + 1 = 2 ^ k :=
  gpf_eq_two_iff (kernel_gt_one .mul hp hq)

/-- Theorem 5.1, divisibility/congruence part. Inverse clauses remain separate. -/
theorem kernel_congruences {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    (p * q + 1) % mul p q = 0 ∧ (p + q + 1) % add p q = 0 :=
  ⟨Nat.mod_eq_zero_of_dvd (output_spec .mul hp hq).2.1,
   Nat.mod_eq_zero_of_dvd (output_spec .add hp hq).2.1⟩

/-- Divisibility cancellation, without relying on a version-specific API. -/
theorem fixed_dvd {a q : ℕ} (hq : 0 < q) (hd : q ∣ a + q + 1) : q ∣ a + 1 := by
  obtain ⟨s, hs⟩ := hd
  have hs1 : 1 ≤ s := by
    by_contra h
    have hs0 : s = 0 := by omega
    rw [hs0, Nat.mul_zero] at hs
    omega
  have hs' := Nat.sub_add_cancel hs1
  refine ⟨s - 1, ?_⟩
  nlinarith

theorem fixed_criterion {a q : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q) :
    add a q = q ↔ q ∣ a + 1 ∧ Smooth q ((a + 1) / q + 1) := by
  have hf := gpf_fiber (kernel_gt_one .add ha hq) hq
  change (add a q = q ↔ ∃ s, 0 < s ∧ a + q + 1 = q * s ∧ Smooth q s) at hf
  constructor
  · intro he
    have hd := fixed_dvd hq.pos (by
      have hh := (output_spec .add ha hq).2.1
      simpa [he] using hh)
    obtain ⟨s, hs, hkernel, hsm⟩ := hf.mp he
    have hdiv : q * ((a + 1) / q) = a + 1 := Nat.mul_div_cancel' hd
    have heq : s = (a + 1) / q + 1 := by have := hq.pos; nlinarith
    exact ⟨hd, heq ▸ hsm⟩
  · rintro ⟨hd, hsm⟩
    apply hf.mpr
    refine ⟨(a + 1) / q + 1, Nat.succ_pos _, ?_, hsm⟩
    have hh : q * ((a + 1) / q) = a + 1 := Nat.mul_div_cancel' hd
    nlinarith

theorem fixed_set_subset {a : ℕ} (ha : Nat.Prime a) :
    {q | Nat.Prime q ∧ add a q = q} ⊆ {q | Nat.Prime q ∧ q ∣ a + 1} := by
  rintro q ⟨hq, he⟩
  exact ⟨hq, ((fixed_criterion ha hq).mp he).1⟩

theorem fixed_divisors_finite (a : ℕ) :
    Set.Finite {q | Nat.Prime q ∧ q ∣ a + 1} := by
  apply (Set.finite_Iic (a + 1)).subset
  intro q hq
  exact Nat.le_of_dvd (by omega) hq.2

theorem proof_7_1 : t7_1 := by
  intro a ha
  have hs := fixed_set_subset ha
  have hf := fixed_divisors_finite a
  exact ⟨fun q hq => fixed_criterion ha hq, hf.subset hs, hs,
    Set.ncard_le_ncard hs hf⟩

theorem proof_7_2 : t7_2 := by
  intro a q ha hq
  exact ⟨mul_ne_left ha hq, mul_ne_right ha hq⟩

theorem proof_7_3 : t7_3 := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    constructor
    · intro he
      have hd := ((fixed_criterion Nat.prime_two hq).mp he).1
      have hh := (Nat.prime_three.dvd_iff_eq hq.ne_one).mp hd
      exact hh.symm
    · intro he; subst q; norm_num [add, output, kernel, gpf, scan]
  · norm_num [add, output, kernel, gpf, scan]
  · intro q hq h
    obtain ⟨k, hk⟩ := h
    apply (gpf_eq_two_iff (kernel_gt_one .add Nat.prime_two hq)).mpr
    refine ⟨k, ?_, ?_⟩
    · by_contra hh
      have hk0 : k = 0 := by omega
      rw [hk0, pow_zero] at hk
      omega
    · change 2 + q + 1 = 2 ^ k; omega

theorem proof_7_4 : t7_4 := by
  intro a q ha hq
  rw [add_comm]
  exact fixed_criterion hq ha

theorem proof_9_1 : t9_1 := by
  intro p _
  constructor
  · change gpf (p + p + 1) = gpf (p * 2 + 1)
    congr 1; omega
  · change gpf (p ^ 2 + 1) = gpf (p * p + 1)
    rw [pow_two]

/-- A small concrete certificate for the flaw in Theorem 5.5. -/
theorem counterexample_5_5 :
    Nat.Prime 3 ∧ Nat.Prime 5 ∧ mul 3 5 = 2 ∧
    5 % 2 = 3 ^ (2 ^ 1 - 1) % 2 ∧ 2 % (2 ^ (1 + 1)) ≠ 1 := by
  norm_num [mul, output, kernel, gpf, scan]

theorem refutation_5_5 : ¬ t5_5_original := by
  intro h
  have hh := h 3 5 1 Nat.prime_three Nat.prime_five (by decide)
  have hc : 5 % mul 3 5 = 3 ^ (2 ^ 1 - 1) % mul 3 5 := by
    norm_num [mul, output, kernel, gpf, scan]
  have impossible := (hh hc).2.1
  norm_num [mul, output, kernel, gpf, scan] at impossible

end PrimeGPF
