import PrimeGPF.Extension2Support
import Mathlib.Algebra.Ring.GeomSum

/-!
# Extension 2: nonprimitive perfect-power kernels

This formalizes the elementary reduction used in the report before Möbius
inversion: for `q > a`, a perfect-power multiplicative kernel `a*q+1 = u^g`
with `g ≥ 2` can only come from `u = 2` or `u = a+1`.
-/
namespace PrimeGPF

/-- A positive divisor of the product of two distinct primes, smaller than the
larger prime, is either `1` or the smaller prime. -/
theorem divisor_prime_product_lt_right
    {a q d : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q)
    (haq : a < q) (hdpos : 0 < d) (hd : d ∣ a * q) (hdq : d < q) :
    d = 1 ∨ d = a := by
  obtain ⟨m, hm⟩ := hd
  by_cases had : a ∣ d
  · obtain ⟨n, rfl⟩ := had
    have hcancel : q = n * m := by
      apply Nat.eq_of_mul_eq_mul_left ha.pos
      calc
        a * q = (a * n) * m := hm
        _ = a * (n * m) := by ring
    have hnq : n ∣ q := ⟨m, hcancel⟩
    rcases (Nat.dvd_prime hq).mp hnq with hn1 | hnqeq
    · right
      subst n
      simp
    · subst n
      have ha2 := ha.two_le
      nlinarith
  · have ham : a ∣ m := by
      have hadm : a ∣ d * m := by
        rw [← hm]
        exact dvd_mul_right a q
      rcases (ha.dvd_mul.mp hadm) with had' | ham
      · exact (had had').elim
      · exact ham
    obtain ⟨n, rfl⟩ := ham
    have hcancel : q = d * n := by
      apply Nat.eq_of_mul_eq_mul_left ha.pos
      calc
        a * q = d * (a * n) := hm
        _ = a * (d * n) := by ring
    have hdq' : d ∣ q := ⟨n, hcancel⟩
    rcases (Nat.dvd_prime hq).mp hdq' with hd1 | hdeq
    · exact Or.inl hd1
    · subst d
      omega

/-- The nonprimitive perfect-power reduction from extension 2. -/
theorem extension2_nonprimitive_power_base
    {a q u g : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q)
    (haq : a < q) (hg : 2 ≤ g)
    (hpow : u ^ g = a * q + 1) :
    u = 2 ∨ u = a + 1 := by
  have hkernel : 1 < a * q + 1 := by
    exact Nat.succ_lt_succ (Nat.mul_pos ha.pos hq.pos)
  have hu2 : 2 ≤ u := by
    by_contra hu
    have hu_le : u ≤ 1 := by omega
    interval_cases u
    · have hg0 : g ≠ 0 := by omega
      have hz : (0 : ℕ) ^ g = 0 := by simp [hg0]
      rw [hz] at hpow
      omega
    · simp at hpow
      omega
  have hsqle : u ^ 2 ≤ u ^ g :=
    Nat.pow_le_pow_right (by omega : 0 < u) hg
  have hqSq : a * q + 1 < q ^ 2 := by
    have ha1q : a + 1 ≤ q := by omega
    have hstep : a * q + 1 < (a + 1) * q := by
      have hq2 := hq.two_le
      nlinarith
    have hstep2 : (a + 1) * q ≤ q * q :=
      Nat.mul_le_mul_right q ha1q
    simpa [pow_two] using hstep.trans_le hstep2
  have huq : u < q := by
    by_contra hnot
    have hqu : q ≤ u := by omega
    have hsq : q ^ 2 ≤ u ^ 2 := by
      exact Nat.pow_le_pow_left hqu 2
    have hbad : q ^ 2 ≤ a * q + 1 := by
      calc
        q ^ 2 ≤ u ^ 2 := hsq
        _ ≤ u ^ g := hsqle
        _ = a * q + 1 := hpow
    exact (not_lt_of_ge hbad) hqSq
  have hdvd : u - 1 ∣ a * q := by
    have h := Nat.sub_dvd_pow_sub_pow u 1 g
    rw [one_pow, hpow] at h
    simpa using h
  have hdpos : 0 < u - 1 := by omega
  have hdq : u - 1 < q := by omega
  rcases divisor_prime_product_lt_right ha hq haq hdpos hdvd hdq with h1 | ha1
  · left
    omega
  · right
    omega

/-- Consequently every such perfect-power kernel belongs to one of the two
families appearing explicitly in the report. -/
theorem extension2_nonprimitive_kernel_family
    {a q u g : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q)
    (haq : a < q) (hg : 2 ≤ g)
    (hpow : u ^ g = a * q + 1) :
    a * q + 1 = 2 ^ g ∨ a * q + 1 = (a + 1) ^ g := by
  rcases extension2_nonprimitive_power_base ha hq haq hg hpow with hu | hu
  · left
    rw [← hpow, hu]
  · right
    rw [← hpow, hu]

end PrimeGPF
