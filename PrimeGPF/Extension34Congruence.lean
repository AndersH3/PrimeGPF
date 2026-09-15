import PrimeGPF.Extension34Exact

/-!
# Extensions 3 and 4: residue restrictions

These are the elementary congruence consequences recorded in the report for
the two explicitly classified output-5 multiplicative fibers.
-/
namespace PrimeGPF

/-- Every nonexceptional input in the anchor-2, output-5 multiplicative fiber
is congruent to 7 modulo 30. -/
theorem extension3_nonexceptional_mod_thirty
    {q : ℕ} (hq : Nat.Prime q) (hout : mul 2 q = 5) (hq2 : q ≠ 2) :
    q % 30 = 7 := by
  obtain ⟨α, β, hα, hβ, _hαodd, hfac⟩ :=
    extension3_exponent_structure hq hout hq2
  have h3pow : 3 ∣ 3 ^ α := dvd_pow_self 3 (by omega)
  have h5pow : 5 ∣ 5 ^ β := dvd_pow_self 5 (by omega)
  have h3ker : 3 ∣ 2 * q + 1 := by
    rw [hfac]
    exact dvd_mul_of_dvd_left h3pow _
  have h5ker : 5 ∣ 2 * q + 1 := by
    rw [hfac]
    exact dvd_mul_of_dvd_right h5pow _
  have hm3 : (2 * q + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h3ker
  have hm5 : (2 * q + 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd h5ker
  have hodd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left hq2
  omega

/-- Every input in the anchor-3, output-5 multiplicative fiber is congruent
to 3 modulo 10. -/
theorem extension4_mod_ten
    {q : ℕ} (hq : Nat.Prime q) (hout : mul 3 q = 5) :
    q % 10 = 3 := by
  obtain ⟨α, β, _hα, hβ, _hαodd, _hβodd, _hcop, hfac⟩ :=
    extension4_output_five_primitive_structure hq hout
  have h5pow : 5 ∣ 5 ^ β := dvd_pow_self 5 (by omega)
  have h5ker : 5 ∣ 3 * q + 1 := by
    rw [hfac]
    exact dvd_mul_of_dvd_right h5pow _
  have hm5 : (3 * q + 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd h5ker
  have hq2 : q ≠ 2 := by
    intro h
    subst q
    norm_num [mul, output, kernel, gpf, scan] at hout
  have hodd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left hq2
  omega

end PrimeGPF
