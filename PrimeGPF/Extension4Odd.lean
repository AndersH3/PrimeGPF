import PrimeGPF.Extension34Structure

/-!
# Extension 4: both exponents are odd

The support argument gives equal parity.  This file excludes the even-even
case using the factorization of a square minus one.
-/
namespace PrimeGPF

/-- For `t ≥ 5`, an equation `3q+1=t²` is incompatible with primality of `q`. -/
theorem no_prime_three_mul_add_one_square
    {q t : ℕ} (hq : Nat.Prime q) (ht : 5 ≤ t)
    (hsq : 3 * q + 1 = t ^ 2) : False := by
  have h5t : 5 * t ≤ t * t :=
    Nat.mul_le_mul_right t ht
  have hlin : 3 * t + 4 < 5 * t := by omega
  have hquad : 3 * t + 4 < t ^ 2 := by
    rw [pow_two]
    exact hlin.trans_le h5t
  have hqt : t + 1 < q := by omega
  have hpowminus : t ^ 2 - 1 = 3 * q := by omega
  have hfactor : (t - 1) * (t + 1) = t ^ 2 - 1 := by
    rw [Nat.sub_mul, one_mul, Nat.mul_add, Nat.mul_one, pow_two]
    omega
  have hqprod : q ∣ (t - 1) * (t + 1) := by
    rw [hfactor, hpowminus]
    exact dvd_mul_left q 3
  rcases hq.dvd_mul.mp hqprod with hleft | hright
  · have htminus : 0 < t - 1 := by omega
    have hle : q ≤ t - 1 := Nat.le_of_dvd htminus hleft
    omega
  · have htplus : 0 < t + 1 := by omega
    have hle : q ≤ t + 1 := Nat.le_of_dvd htplus hright
    omega

/-- In the extension-4 exponent representation, both exponents are odd. -/
theorem extension4_exponents_odd
    {q α β : ℕ} (hq : Nat.Prime q)
    (hαpos : 0 < α) (hβpos : 0 < β)
    (hparity : α % 2 = β % 2)
    (hfac : 3 * q + 1 = 2 ^ α * 5 ^ β) :
    α % 2 = 1 ∧ β % 2 = 1 := by
  have hαlt := Nat.mod_lt α (by omega : 0 < 2)
  have hβlt := Nat.mod_lt β (by omega : 0 < 2)
  have hαodd : α % 2 = 1 := by
    by_contra hne
    have hαeven : α % 2 = 0 := by omega
    have hβeven : β % 2 = 0 := by omega
    have h2α : 2 ∣ α := Nat.dvd_of_mod_eq_zero hαeven
    have h2β : 2 ∣ β := Nat.dvd_of_mod_eq_zero hβeven
    let A := α / 2
    let B := β / 2
    have hAform : α = A * 2 := by
      have h := Nat.mul_div_cancel' h2α
      dsimp [A]
      simpa [Nat.mul_comm] using h.symm
    have hBform : β = B * 2 := by
      have h := Nat.mul_div_cancel' h2β
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
    let t := 2 ^ A * 5 ^ B
    have h2A : 2 ≤ 2 ^ A := by
      have h := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 1 ≤ A by omega)
      simpa using h
    have h5B : 5 ≤ 5 ^ B := by
      have h := Nat.pow_le_pow_right (by decide : 0 < (5 : ℕ)) (show 1 ≤ B by omega)
      simpa using h
    have ht10 : 10 ≤ t := by
      dsimp [t]
      calc
        10 = 2 * 5 := by norm_num
        _ ≤ 2 ^ A * 5 ^ B := Nat.mul_le_mul h2A h5B
    have hsq : 3 * q + 1 = t ^ 2 := by
      calc
        3 * q + 1 = 2 ^ α * 5 ^ β := hfac
        _ = 2 ^ (A * 2) * 5 ^ (B * 2) := by rw [hAform, hBform]
        _ = (2 ^ A) ^ 2 * (5 ^ B) ^ 2 := by rw [pow_mul, pow_mul]
        _ = (2 ^ A * 5 ^ B) ^ 2 := by rw [mul_pow]
        _ = t ^ 2 := rfl
    exact no_prime_three_mul_add_one_square hq (by omega) hsq
  have hβodd : β % 2 = 1 := by omega
  exact ⟨hαodd, hβodd⟩

/-- Applied directly to the extension-4 fiber structure. -/
theorem extension4_output_five_has_odd_exponents
    {q : ℕ} (hq : Nat.Prime q) (hout : mul 3 q = 5) :
    ∃ α β : ℕ,
      0 < α ∧ 0 < β ∧ α % 2 = 1 ∧ β % 2 = 1 ∧
      3 * q + 1 = 2 ^ α * 5 ^ β := by
  obtain ⟨α, β, hα, hβ, hpar, hfac⟩ :=
    extension4_exponent_structure hq hout
  have hodd := extension4_exponents_odd hq hα hβ hpar hfac
  exact ⟨α, β, hα, hβ, hodd.1, hodd.2, hfac⟩

end PrimeGPF
