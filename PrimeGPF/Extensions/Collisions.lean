import PrimeGPF.Extensions.Dynamics

namespace PrimeGPF.Extensions

/-- Extension 8: additive/exponential collisions lie below the diagonal,
apart from the known exceptional pair. -/
theorem add_exp_localization {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (h : add p q = exp p q) : q ≤ p ∨ (p = 2 ∧ q = 3) := by
  by_cases hex : (p, q) = (2, 3)
  · exact Or.inr ⟨congrArg Prod.fst hex, congrArg Prod.snd hex⟩
  · have hg := exp_double hp hq hex
    have hu : add p q ≤ p + q + 1 := gpf_le _
    rw [h] at hu
    exact Or.inl (by omega)

/-- A composite odd additive kernel makes the localization five times stronger. -/
theorem add_exp_composite_bound {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (h : add p q = exp p q)
    (hc : ¬ Nat.Prime (p + q + 1)) : 5 * q + 2 ≤ p := by
  have hpo := hp.eq_two_or_odd.resolve_left hp2
  have hqo := hq.eq_two_or_odd.resolve_left hq2
  have hnodd : (p + q + 1) % 2 = 1 := by omega
  have hg := exp_double hp hq (by intro he; exact hp2 (congrArg Prod.fst he))
  have hs := output_spec .add hp hq
  obtain ⟨t, ht⟩ := hs.2.1
  change p + q + 1 = add p q * t at ht
  have ht0 : t ≠ 0 := by intro he; simp [he] at ht
  have ht1 : t ≠ 1 := by
    intro he
    have hn : p + q + 1 = add p q := by simpa [he] using ht
    exact hc (hn ▸ hs.1)
  have ht2 : t ≠ 2 := by
    intro he
    have hh := congrArg (fun n : ℕ => n % 2) ht
    simp [he, Nat.mul_mod, hnodd] at hh
  have ht3 : 3 ≤ t := by omega
  rw [h] at ht
  nlinarith

theorem triple_localization {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (ham : add p q = mul p q) (hae : add p q = exp p q) :
    q ≤ p ∧ 2 * q + 1 ≤ gpf (p ^ 2 + p - 1) := by
  have hex : (p, q) ≠ (2, 3) := by
    intro he
    have hp2 := congrArg Prod.fst he
    have hq3 := congrArg Prod.snd he
    simp only [Prod.fst, Prod.snd] at hp2 hq3
    subst p; subst q
    norm_num [add, mul, output, kernel, gpf, scan] at ham
  have hqp : q ≤ p := (add_exp_localization hp hq hae).resolve_right
    (by rintro ⟨rfl, rfl⟩; exact hex rfl)
  have hd : add p q ∣ p ^ 2 + p - 1 := by
    apply collision_divisor (q := q)
    · exact (output_spec .add hp hq).2.1
    · rw [ham]; exact (output_spec .mul hp hq).2.1
  have hpos : 1 < p ^ 2 + p - 1 := by
    have := hp.two_le
    have hsq : 4 ≤ p ^ 2 := by nlinarith
    omega
  have hu := (gpf_spec hpos).2.2 _ (output_spec .add hp hq).1 hd
  change add p q ≤ gpf (p ^ 2 + p - 1) at hu
  have hg := exp_double hp hq hex
  rw [hae] at hu
  exact ⟨hqp, hg.trans hu⟩

theorem no_triple_of_prime_polynomial {p : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (hB : Nat.Prime (p ^ 2 + p - 1)) :
    ¬ ∃ q, Nat.Prime q ∧ add p q = mul p q ∧ add p q = exp p q := by
  rintro ⟨q, hq, ham, hae⟩
  have hqp := (triple_localization hp hq ham hae).1
  have hr := (output_spec .add hp hq).1
  have hd : add p q ∣ p ^ 2 + p - 1 := by
    apply collision_divisor (q := q)
    · exact (output_spec .add hp hq).2.1
    · rw [ham]; exact (output_spec .mul hp hq).2.1
  have he : add p q = p ^ 2 + p - 1 :=
    (Nat.dvd_prime hB).mp hd |>.resolve_left hr.ne_one
  have hu : add p q ≤ p + q + 1 := gpf_le _
  have hsub : p ^ 2 + p - 1 + 1 = p ^ 2 + p := by omega
  nlinarith

end PrimeGPF.Extensions
