import PrimeGPF.Extension9Revised

/-!
# Extensions 3 and 4: easy residue consequences

These are the congruence conclusions from the two output-5 multiplicative
fiber classifications.  They are independent of the later primitive-exponent
counting/asymptotic arguments.
-/
namespace PrimeGPF

/-- Outside the exceptional input `q = 2`, every prime in the output-5
multiplicative fiber at anchor 2 is `7 mod 30`. -/
theorem extension3_residue_mod_30
    {q : ℕ} (hq : Nat.Prime q) (hout : mul 2 q = 5) (hq2 : q ≠ 2) :
    q % 30 = 7 := by
  have hodd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left hq2
  have hn : 1 < 2 * q + 1 := by
    have := hq.two_le
    omega
  have hg : gpf (2 * q + 1) = 5 := by
    simpa [mul, output, kernel] using hout
  have h5div : 5 ∣ 2 * q + 1 := by
    have hd := (gpf_spec hn).2.1
    simpa [hg] using hd
  have h3div : 3 ∣ 2 * q + 1 := by
    by_contra h3
    have hsupp : ∀ s, Nat.Prime s → s ∣ 2 * q + 1 → s = 5 := by
      intro s hs hd
      rcases prime_dvd_of_gpf_five hn hg hs hd with h2 | h3s | h5
      · subst s
        have hz := Nat.mod_eq_zero_of_dvd hd
        norm_num [Nat.add_mod, Nat.mul_mod, hodd] at hz
      · subst s
        exact (h3 hd).elim
      · exact h5
    obtain ⟨k, hk⟩ :=
      power_of_prime_support 5 (2 * q + 1) Nat.prime_five (by omega) hsupp
    have hNmod4 : (2 * q + 1) % 4 = 3 := by
      have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by omega
      rcases hq4 with h1 | h3 <;>
        norm_num [Nat.add_mod, Nat.mul_mod, h1, h3]
    rw [hk] at hNmod4
    have hpowmod : 5 ^ k % 4 = 1 := by simp [Nat.pow_mod]
    omega
  have h3zero := Nat.mod_eq_zero_of_dvd h3div
  have h5zero := Nat.mod_eq_zero_of_dvd h5div
  have hqmod3 : q % 3 = 1 := by
    have hlt := Nat.mod_lt q (by omega : 0 < 3)
    norm_num [Nat.add_mod, Nat.mul_mod] at h3zero
    omega
  have hqmod5 : q % 5 = 2 := by
    have hlt := Nat.mod_lt q (by omega : 0 < 5)
    norm_num [Nat.add_mod, Nat.mul_mod] at h5zero
    omega
  have hq30lt := Nat.mod_lt q (by omega : 0 < 30)
  omega

/-- Every prime in the output-5 multiplicative fiber at anchor 3 is
`3 mod 10`.  In particular the exceptional even prime cannot occur. -/
theorem extension4_residue_mod_10
    {q : ℕ} (hq : Nat.Prime q) (hout : mul 3 q = 5) :
    q % 10 = 3 := by
  have hq2 : q ≠ 2 := by
    intro h
    subst q
    norm_num [mul, output, kernel, gpf, scan] at hout
  have hodd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left hq2
  have hn : 1 < 3 * q + 1 := by
    have := hq.two_le
    omega
  have hg : gpf (3 * q + 1) = 5 := by
    simpa [mul, output, kernel] using hout
  have h5div : 5 ∣ 3 * q + 1 := by
    have hd := (gpf_spec hn).2.1
    simpa [hg] using hd
  have h5zero := Nat.mod_eq_zero_of_dvd h5div
  have hqmod5 : q % 5 = 3 := by
    have hlt := Nat.mod_lt q (by omega : 0 < 5)
    norm_num [Nat.add_mod, Nat.mul_mod] at h5zero
    omega
  have hq10lt := Nat.mod_lt q (by omega : 0 < 10)
  omega

end PrimeGPF
