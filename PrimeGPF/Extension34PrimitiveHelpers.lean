import PrimeGPF.Extension34Structure

/-!
# Extensions 3 and 4: primitive-exponent helpers

The coprimality arguments for Extensions 3 and 4 share the same final number-
theoretic contradiction.  If a kernel

`c*q + 1 = t^g`

is a proper power with `g ≥ 2`, and `c ∣ t - 1`, then
`d = (t - 1) / c` divides the prime `q`.  When `d > 1`, primality forces
`d = q`; substituting back would give `t^g = t`, impossible for `t > 1` and
`g > 1`.

This module packages that common argument so the Extension 3/4 coprimality
proofs only need to construct the appropriate `t`, prove the residue condition,
and verify that `d` is nontrivial.
-/
namespace PrimeGPF

/-- A prime kernel of the form `c*q+1` cannot simultaneously be a genuine
proper power `t^g` when `(t-1)/c` is a nontrivial integer.

The divisibility `t-1 ∣ t^g-1` is the geometric-series factorization. -/
theorem prime_kernel_not_proper_power
    {c q t g : ℕ}
    (hq : Nat.Prime q) (hc : 0 < c) (hg : 2 ≤ g) (ht : 1 < t)
    (hcdiv : c ∣ t - 1) (hdgt1 : 1 < (t - 1) / c)
    (hkernel : c * q + 1 = t ^ g) : False := by
  let d := (t - 1) / c
  have hcd : c * d = t - 1 := by
    dsimp [d]
    exact Nat.mul_div_cancel' hcdiv
  have hpowminus : t ^ g - 1 = c * q := by
    omega

  have hgeom : t - 1 ∣ t ^ g - 1 := by
    let S := ∑ i ∈ Finset.range g, t ^ i
    refine ⟨S, ?_⟩
    have hsum := geom_sum_mul_of_one_le (show 1 ≤ t by omega) g
    dsimp [S]
    calc
      t ^ g - 1 = (∑ i ∈ Finset.range g, t ^ i) * (t - 1) := hsum.symm
      _ = (t - 1) * (∑ i ∈ Finset.range g, t ^ i) := by ring

  rw [← hcd, hpowminus] at hgeom
  have hdq : d ∣ q :=
    Nat.dvd_of_mul_dvd_mul_left hc hgeom
  rcases (Nat.dvd_prime hq).mp hdq with hd1 | hdqeq
  · have : 1 < d := by simpa [d] using hdgt1
    omega
  · have hcq : c * q = t - 1 := by
      simpa [hdqeq] using hcd
    have htg : t ^ g = t := by
      omega
    have htlt : t < t ^ g := by
      calc
        t = t ^ 1 := by simp
        _ < t ^ g := Nat.pow_lt_pow_right ht (by omega)
    exact htlt.ne htg.symm

end PrimeGPF
