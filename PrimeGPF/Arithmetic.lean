import PrimeGPF.Elementary

/-! Further arithmetic proof scripts. These have not been compiled. -/
namespace PrimeGPF
open Claims

/-- A number greater than 2 that is 2 modulo 4 cannot have GPF 2. -/
theorem gpf_ne_two_of_mod_four {n : ℕ} (hn : 2 < n) (hm : n % 4 = 2) :
    gpf n ≠ 2 := by
  intro he
  obtain ⟨k, hk, hn'⟩ := (gpf_eq_two_iff (by omega)).mp he
  have hk2 : 2 ≤ k := by
    by_contra h
    have : k = 1 := by omega
    simp_all
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hk2
  rw [hj, pow_add] at hn'
  have hh : n % 4 = 0 := by rw [hn']; simp [Nat.mul_mod]
  omega

theorem square_output_ne_two {p : ℕ} (hp : Nat.Prime p) : exp p 2 ≠ 2 := by
  rcases hp.eq_two_or_odd with he | ho
  · subst p; norm_num [exp, output, kernel, gpf, scan]
  · change gpf (p ^ 2 + 1) ≠ 2
    have hp2 := hp.two_le
    have hm : p % 4 = 1 ∨ p % 4 = 3 := by omega
    apply gpf_ne_two_of_mod_four (by nlinarith)
    rcases hm with hm | hm <;> norm_num [pow_two, Nat.add_mod, Nat.mul_mod, hm]

/-- An explicit inverse modulo r from pq ≡ -1, without a field API. -/
theorem inverse_witness {p q r : ℕ} (hr : 1 < r) (hd : r ∣ p * q + 1) :
    ∃ u, p * u % r = 1 ∧ (q + u) % r = 0 := by
  let u := (r - 1) * q
  have hr' : r - 1 + 1 = r := by omega
  have he : q + u = r * q := by dsimp [u]; nlinarith
  have hdqu : r ∣ q + u := by rw [he]; exact dvd_mul_right r q
  have hdtotal : r ∣ p * q + p * u := by
    have hh := Nat.dvd_mul_left_of_dvd hdqu p
    simpa [Nat.mul_add] using hh
  have hcon : Nat.ModEq r (p * q + p * u) (p * q + 1) := by
    change (p * q + p * u) % r = (p * q + 1) % r
    rw [Nat.mod_eq_zero_of_dvd hdtotal, Nat.mod_eq_zero_of_dvd hd]
  have hcancel := Nat.ModEq.add_left_cancel' (p * q) hcon
  refine ⟨u, ?_, Nat.mod_eq_zero_of_dvd hdqu⟩
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hr] using hcancel

theorem proof_5_1 : t5_1 := by
  intro p q hp hq
  have hr := (output_spec .mul hp hq).1
  have hd : mul p q ∣ p * q + 1 := (output_spec .mul hp hq).2.1
  have hd' : mul p q ∣ q * p + 1 := by simpa [Nat.mul_comm] using hd
  exact ⟨Nat.mod_eq_zero_of_dvd hd, inverse_witness hr.one_lt hd,
    inverse_witness hr.one_lt hd',
    Nat.mod_eq_zero_of_dvd (output_spec .add hp hq).2.1⟩

theorem proof_5_6 : t5_6 := by
  intro p q hp hq hp2 hq2
  have ho := hp.eq_two_or_odd.resolve_left hp2
  have ho' := hq.eq_two_or_odd.resolve_left hq2
  have first : p % 4 = q % 4 → mul p q ≠ 2 := by
    intro he
    have hcases : p % 4 = 1 ∨ p % 4 = 3 := by omega
    have hmod : (p * q + 1) % 4 = 2 := by
      rcases hcases with h | h
      all_goals have hqmod : q % 4 = p % 4 := he.symm
      all_goals norm_num [Nat.add_mod, Nat.mul_mod, hqmod, h]
    have hgt : 2 < p * q + 1 := by have := hp.two_le; have := hq.two_le; nlinarith
    exact gpf_ne_two_of_mod_four hgt hmod
  exact ⟨first, fun h he => first he h⟩

/-- The elimination identity underlying 9.4 and 9.6. -/
theorem collision_divisor {p q r : ℕ} (ha : r ∣ p + q + 1)
    (hm : r ∣ p * q + 1) : r ∣ p ^ 2 + p - 1 := by
  have hh := Nat.dvd_sub (Nat.dvd_mul_left_of_dvd ha p) hm
  have he : p * (p + q + 1) = p * q + (p ^ 2 + p) := by ring
  have he' : p * (p + q + 1) - (p * q + 1) = p ^ 2 + p - 1 := by rw [he]; omega
  simpa only [he'] using hh

theorem additive_residue_unique {p r q₁ q₂ : ℕ}
    (h₁ : r ∣ p + q₁ + 1) (h₂ : r ∣ p + q₂ + 1) : q₁ % r = q₂ % r := by
  have hc : Nat.ModEq r (p + 1 + q₁) (p + 1 + q₂) := by
    change (p + 1 + q₁) % r = (p + 1 + q₂) % r
    have h₁' : r ∣ p + 1 + q₁ := by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h₁
    have h₂' : r ∣ p + 1 + q₂ := by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h₂
    rw [Nat.mod_eq_zero_of_dvd h₁', Nat.mod_eq_zero_of_dvd h₂']
  exact Nat.ModEq.add_left_cancel' (p + 1) hc

theorem collision_residue_exists {p r : ℕ} (hp : Nat.Prime p) (hr : Nat.Prime r)
    (h : r ∣ p ^ 2 + p - 1) : ∃ q, r ∣ p + q + 1 ∧ r ∣ p * q + 1 := by
  let q := (r - 1) * (p + 1)
  have hr' : r - 1 + 1 = r := by have := hr.two_le; omega
  have hp' : p ^ 2 + p - 1 + 1 = p ^ 2 + p := by have := hp.two_le; omega
  have ha : p + q + 1 = r * (p + 1) := by dsimp [q]; nlinarith
  have hm : (p * q + 1) + (p ^ 2 + p - 1) = r * (p ^ 2 + p) := by
    dsimp [q]
    nlinarith [congrArg (fun t : ℕ => t * (p ^ 2 + p)) hr']
  refine ⟨q, ?_, ?_⟩
  · rw [ha]; exact dvd_mul_right r (p + 1)
  · apply (Nat.dvd_add_iff_left h).mpr
    rw [hm]
    exact dvd_mul_right r (p ^ 2 + p)

theorem proof_9_4 : t9_4 := by
  intro p r hp hr _
  refine ⟨?_, fun _ _ h₁ h₂ => additive_residue_unique h₁ h₂, ?_⟩
  · constructor
    · rintro ⟨q, ha, hm⟩; exact collision_divisor ha hm
    · exact collision_residue_exists hp hr
  · intro q hq ha hm
    apply collision_divisor (p := p) (q := q) (r := r)
    · simpa [ha] using (output_spec .add hp hq).2.1
    · simpa [hm] using (output_spec .mul hp hq).2.1

theorem proof_9_5 : t9_5 := by
  intro p hp
  have hs : commonOutputs p ⊆ {r | Nat.Prime r ∧ r ∣ p ^ 2 + p - 1} := by
    rintro r ⟨hr, q, hq, ha, hm⟩
    refine ⟨hr, collision_divisor (p := p) (q := q) (r := r) ?_ ?_⟩
    · simpa [ha] using (output_spec .add hp hq).2.1
    · simpa [hm] using (output_spec .mul hp hq).2.1
  have ht : tripleOutputs p ⊆ commonOutputs p := by
    rintro r ⟨hr, q, hq, ha, hm, _⟩
    exact ⟨hr, q, hq, ha, hm⟩
  have hn : 0 < p ^ 2 + p - 1 := by have := hp.two_le; omega
  have hf : Set.Finite {r | Nat.Prime r ∧ r ∣ p ^ 2 + p - 1} := by
    apply (Set.finite_Iic (p ^ 2 + p - 1)).subset
    intro r hr
    exact Nat.le_of_dvd hn hr.2
  exact ⟨hf.subset hs, hs, (hf.subset hs).subset ht, fun _ h => hs (ht h)⟩

/-- The two polynomial congruences in 9.6 (reciprocity not used here). -/
theorem collision_two_polynomials {p q r : ℕ}
    (ha : r ∣ p + q + 1) (hm : r ∣ p * q + 1) :
    r ∣ p ^ 2 + p - 1 ∧ r ∣ q ^ 2 + q - 1 := by
  refine ⟨collision_divisor ha hm, collision_divisor (p := q) (q := p) (r := r) ?_ ?_⟩
  · simpa [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using ha
  · simpa [Nat.mul_comm] using hm

theorem proof_9_7 : t9_7 := by
  intro p q r hp hq hm he
  have hr : Nat.Prime r := by simpa [hm] using (output_spec .mul hp hq).1
  have hdm : r ∣ p * q + 1 := by simpa [hm] using (output_spec .mul hp hq).2.1
  have hde : r ∣ p ^ q + 1 := by simpa [he] using (output_spec .exp hp hq).2.1
  obtain ⟨u, hu, _⟩ := inverse_witness hr.one_lt hdm
  have hc : Nat.ModEq r (p * q + 1) (p ^ q + 1) := by
    change (p * q + 1) % r = (p ^ q + 1) % r
    rw [Nat.mod_eq_zero_of_dvd hdm, Nat.mod_eq_zero_of_dvd hde]
  have hc' := Nat.ModEq.add_right_cancel' 1 hc
  have hq' : q - 1 + 1 = q := by have := hq.two_le; omega
  have hpw : p ^ q = p * p ^ (q - 1) := by
    calc
      p ^ q = p ^ (q - 1 + 1) := by rw [hq']
      _ = p * p ^ (q - 1) := by rw [pow_succ]; ring
  rw [hpw] at hc'
  have hh := Nat.ModEq.mul_left u hc'
  have e₁ : u * (p * q) = (p * u) * q := by ring
  have e₂ : u * (p * p ^ (q - 1)) = (p * u) * p ^ (q - 1) := by ring
  rw [e₁, e₂] at hh
  change ((p * u) * q) % r = ((p * u) * p ^ (q - 1)) % r at hh
  simpa [Nat.mul_mod, hu] using hh.symm

/-- Theorem 9.2, using explicit divisibility combinations. -/
theorem proof_9_2 : t9_2 := by
  intro p hp
  have hp2 := hp.two_le
  have prime_eq_five : ∀ r, Nat.Prime r → r ∣ 5 → r = 5 := by
    intro r hr hd
    exact ((Nat.prime_five.dvd_iff_eq hr.ne_one).mp hd).symm
  refine ⟨?_, ?_, ?_⟩
  · intro he
    let r := add p 2
    have hr : Nat.Prime r := (output_spec .add hp Nat.prime_two).1
    have ha : r ∣ p + 3 := by simpa [r, kernel, Nat.add_assoc] using (output_spec .add hp Nat.prime_two).2.1
    have hm : r ∣ 2 * p + 1 := by
      simpa [r, he, kernel, Nat.mul_comm] using (output_spec .mul hp Nat.prime_two).2.1
    have hd := Nat.dvd_sub (Nat.dvd_mul_left_of_dvd ha 2) hm
    have hh : 2 * (p + 3) - (2 * p + 1) = 5 := by omega
    exact prime_eq_five r hr (by simpa [hh] using hd)
  · intro he
    let r := add p 2
    have hr : Nat.Prime r := (output_spec .add hp Nat.prime_two).1
    have ha : r ∣ p + 3 := by simpa [r, kernel, Nat.add_assoc] using (output_spec .add hp Nat.prime_two).2.1
    have he' : r ∣ p ^ 2 + 1 := by simpa [r, he, kernel] using (output_spec .exp hp Nat.prime_two).2.1
    have hd := Nat.dvd_sub
      (Nat.dvd_add (Nat.dvd_mul_left_of_dvd ha (p + 3)) he')
      (Nat.dvd_mul_left_of_dvd ha (2 * p))
    have hi : (p + 3) * (p + 3) + (p ^ 2 + 1) - 2 * p * (p + 3) = 10 := by
      have hh : (p + 3) * (p + 3) + (p ^ 2 + 1) = 2 * p * (p + 3) + 10 := by ring
      omega
    have hd10 : r ∣ 2 * 5 := by simpa only [hi] using hd
    rcases hr.dvd_mul.mp hd10 with hd2 | hd5
    · have hr2 : r = 2 := ((Nat.prime_two.dvd_iff_eq hr.ne_one).mp hd2).symm
      exact False.elim (square_output_ne_two hp (he.symm.trans hr2))
    · exact prime_eq_five r hr hd5
  · intro he
    let r := mul p 2
    have hr : Nat.Prime r := (output_spec .mul hp Nat.prime_two).1
    have hm : r ∣ 2 * p + 1 := by simpa [r, kernel, Nat.mul_comm] using (output_spec .mul hp Nat.prime_two).2.1
    have he' : r ∣ p ^ 2 + 1 := by simpa [r, he, kernel] using (output_spec .exp hp Nat.prime_two).2.1
    have hd := Nat.dvd_sub (Nat.dvd_mul_left_of_dvd he' 4)
      (Nat.dvd_mul_left_of_dvd hm (2 * p - 1))
    have hi : 4 * (p ^ 2 + 1) - (2 * p - 1) * (2 * p + 1) = 5 := by
      have ht : 2 * p - 1 + 1 = 2 * p := by omega
      have hh : 4 * (p ^ 2 + 1) = (2 * p - 1) * (2 * p + 1) + 5 := by
        nlinarith [congrArg (fun n : ℕ => n * (2 * p + 1)) ht]
      omega
    exact prime_eq_five r hr (by simpa [hi] using hd)

end PrimeGPF
