import PrimeGPF.Extension34Structure

/-!
# Extension 3: coprimality of the exponent vector

This supplies the remaining primitive-exponent condition in the exact
anchor-2 output-5 classification.
-/
namespace PrimeGPF

/-- If a prime `q` satisfies `2q+1 = 3^α 5^β` with positive exponents and
odd `α`, then `α` and `β` are coprime. -/
theorem extension3_exponents_coprime
    {q α β : ℕ} (hq : Nat.Prime q)
    (hαpos : 0 < α) (hβpos : 0 < β) (hαodd : α % 2 = 1)
    (hfac : 2 * q + 1 = 3 ^ α * 5 ^ β) :
    Nat.Coprime α β := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let g := Nat.gcd α β
  have hgpos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_left β hαpos
  by_contra hg1
  have hg2 : 2 ≤ g := by omega
  have hgα : g ∣ α := by
    dsimp [g]
    exact Nat.gcd_dvd_left α β
  have hgβ : g ∣ β := by
    dsimp [g]
    exact Nat.gcd_dvd_right α β
  have hg_ne_two : g ≠ 2 := by
    intro he
    subst g
    have h2α : 2 ∣ α := hgα
    have hz := Nat.mod_eq_zero_of_dvd h2α
    omega
  have hg3 : 3 ≤ g := by omega

  let A := α / g
  let B := β / g
  have hAform : α = A * g := by
    have h := Nat.mul_div_cancel' hgα
    dsimp [A]
    simpa [Nat.mul_comm] using h.symm
  have hBform : β = B * g := by
    have h := Nat.mul_div_cancel' hgβ
    dsimp [B]
    simpa [Nat.mul_comm] using h.symm
  have hApos : 0 < A := by
    by_contra hA
    have hA0 : A = 0 := by omega
    rw [hA0, Nat.zero_mul] at hAform
    omega
  have hBpos : 0 < B := by
    by_contra hB
    have hB0 : B = 0 := by omega
    rw [hB0, Nat.zero_mul] at hBform
    omega

  let t := 3 ^ A * 5 ^ B
  have h3A : 3 ≤ 3 ^ A := by
    have h := Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ)) (show 1 ≤ A by omega)
    simpa using h
  have h5B : 5 ≤ 5 ^ B := by
    have h := Nat.pow_le_pow_right (by decide : 0 < (5 : ℕ)) (show 1 ≤ B by omega)
    simpa using h
  have ht15 : 15 ≤ t := by
    dsimp [t]
    calc
      15 = 3 * 5 := by norm_num
      _ ≤ 3 ^ A * 5 ^ B := Nat.mul_le_mul h3A h5B
  have htodd : t % 2 = 1 := by
    dsimp [t]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  have hkernelpow : 2 * q + 1 = t ^ g := by
    calc
      2 * q + 1 = 3 ^ α * 5 ^ β := hfac
      _ = 3 ^ (A * g) * 5 ^ (B * g) := by rw [hAform, hBform]
      _ = (3 ^ A) ^ g * (5 ^ B) ^ g := by rw [pow_mul, pow_mul]
      _ = (3 ^ A * 5 ^ B) ^ g := by rw [mul_pow]
      _ = t ^ g := rfl

  have htminus_even : 2 ∣ t - 1 := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let d := (t - 1) / 2
  have h2d : 2 * d = t - 1 := by
    dsimp [d]
    exact Nat.mul_div_cancel' htminus_even
  have hdgt1 : 1 < d := by omega

  have hpowminus : t ^ g - 1 = 2 * q := by omega
  have hgeom : t - 1 ∣ t ^ g - 1 := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow t 1 g
  rw [← h2d, hpowminus] at hgeom
  have hdq : d ∣ q :=
    Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < (2 : ℕ)) hgeom
  rcases (Nat.dvd_prime hq).mp hdq with hd1 | hdqeq
  · omega
  · have htg : t ^ g = t := by
      rw [hdqeq] at h2d
      omega
    have htgt1 : 1 < t := by omega
    have htlt : t < t ^ g := by
      calc
        t = t ^ 1 := by simp
        _ < t ^ g := Nat.pow_lt_pow_right htgt1 (by omega)
    exact htlt.ne htg.symm

end PrimeGPF
