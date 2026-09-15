import PrimeGPF.Extension4Odd
import PrimeGPF.Extension34PrimitiveHelpers

/-!
# Extension 4: coprimality of the exponent vector

This module proves the primitive-exponent condition for the anchor-3/output-5
classification.

As in Extension 3, the proof is split cleanly:

1. assume `g = gcd α β > 1` and write the kernel as `t^g`;
2. use oddness of `α` and `β` to show the reduced exponents remain odd, hence
   `t ≡ 1 (mod 3)`;
3. invoke the generic proper-power contradiction from
   `Extension34PrimitiveHelpers`.

The final geometric-series/primality argument is therefore shared with
Extension 3 rather than duplicated here.
-/
namespace PrimeGPF

/-- If a prime `q` satisfies `3q+1 = 2^α 5^β` with positive odd exponents,
then `α` and `β` are coprime. -/
theorem extension4_exponents_coprime
    {q α β : ℕ} (hq : Nat.Prime q)
    (hαpos : 0 < α) (hβpos : 0 < β)
    (hαodd : α % 2 = 1) (hβodd : β % 2 = 1)
    (hfac : 3 * q + 1 = 2 ^ α * 5 ^ β) :
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
    have h2α : 2 ∣ α := by simpa [he] using hgα
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
    dsimp [A]
    exact Nat.div_pos (Nat.le_of_dvd hαpos hgα) hgpos
  have hBpos : 0 < B := by
    dsimp [B]
    exact Nat.div_pos (Nat.le_of_dvd hβpos hgβ) hgpos

  -- Since `α = A*g` and `α` is odd, `A` must itself be odd.  The same
  -- argument applies to `B` using oddness of `β`.
  have hAodd : A % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one A with hzero | hone
    · have h2A : 2 ∣ A := Nat.dvd_of_mod_eq_zero hzero
      have h2α : 2 ∣ α := by
        rw [hAform]
        exact dvd_mul_of_dvd_left h2A g
      have hz := Nat.mod_eq_zero_of_dvd h2α
      omega
    · exact hone
  have hBodd : B % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one B with hzero | hone
    · have h2B : 2 ∣ B := Nat.dvd_of_mod_eq_zero hzero
      have h2β : 2 ∣ β := by
        rw [hBform]
        exact dvd_mul_of_dvd_left h2B g
      have hz := Nat.mod_eq_zero_of_dvd h2β
      omega
    · exact hone

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
  have htmod3 : t % 3 = 1 := by
    have h2pow := extension_two_pow_mod_three_of_odd hAodd
    have h5pow := five_pow_mod_three_of_odd hBodd
    dsimp [t]
    norm_num [Nat.mul_mod, h2pow, h5pow]
  have hkernelpow : 3 * q + 1 = t ^ g := by
    calc
      3 * q + 1 = 2 ^ α * 5 ^ β := hfac
      _ = 2 ^ (A * g) * 5 ^ (B * g) := by rw [hAform, hBform]
      _ = (2 ^ A) ^ g * (5 ^ B) ^ g := by rw [pow_mul, pow_mul]
      _ = (2 ^ A * 5 ^ B) ^ g := by rw [mul_pow]
      _ = t ^ g := rfl

  -- `t ≡ 1 (mod 3)` makes `(t-1)/3` integral; `t ≥ 10` makes it
  -- nontrivial.  The shared helper then contradicts primality of `q`.
  have htminus_three : 3 ∣ t - 1 := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  let d := (t - 1) / 3
  have h3d : 3 * d = t - 1 := by
    dsimp [d]
    exact Nat.mul_div_cancel' htminus_three
  have hdgt1 : 1 < d := by omega
  have hdquot : 1 < (t - 1) / 3 := by
    simpa [d] using hdgt1

  exact prime_kernel_not_proper_power
    hq (by norm_num) hg2 (by omega) htminus_three hdquot hkernelpow

/-- Applied directly to the output-5 Extension-4 fiber. -/
theorem extension4_output_five_primitive_structure
    {q : ℕ} (hq : Nat.Prime q) (hout : mul 3 q = 5) :
    ∃ α β : ℕ,
      0 < α ∧ 0 < β ∧ α % 2 = 1 ∧ β % 2 = 1 ∧
      Nat.Coprime α β ∧
      3 * q + 1 = 2 ^ α * 5 ^ β := by
  obtain ⟨α, β, hα, hβ, hαodd, hβodd, hfac⟩ :=
    extension4_output_five_has_odd_exponents hq hout
  have hcop := extension4_exponents_coprime hq hα hβ hαodd hβodd hfac
  exact ⟨α, β, hα, hβ, hαodd, hβodd, hcop, hfac⟩

end PrimeGPF
