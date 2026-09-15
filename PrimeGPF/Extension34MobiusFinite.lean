import PrimeGPF.Extension34MobiusSetup
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Extensions 3 and 4: finite Möbius detection of coprimality

The previous setup shows that every common divisor relevant to Extensions 3
and 4 is odd and rescales the weighted triangle in the expected way.  This
module adds the exact finite Möbius identity that detects primitivity.

Mathlib already proves the Dirichlet-convolution identity

`moebius * zeta = 1`.

Evaluating that identity at `n` says that the sum of `μ(d)` over divisors of
`n` is `1` when `n = 1` and `0` otherwise.  Taking `n = gcd(α,β)` therefore
turns the coprimality indicator into a finite divisor sum.  This is precisely
the combinatorial identity needed before interchanging the later lattice and
Möbius sums.
-/
namespace PrimeGPF

open ArithmeticFunction

/-- Sum of the Möbius function over the divisors of a positive integer.

This is a direct evaluation of Mathlib's convolution theorem
`moebius_mul_coe_zeta`. -/
theorem sum_moebius_divisors_eq_indicator_one
    {n : ℕ} (hn : 0 < n) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
      if n = 1 then 1 else 0 := by
  have hconv := congrArg
    (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  simpa [ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.one_apply] using hconv

/-- The coprimality indicator of two positive exponent coordinates is the
Möbius sum over the divisors of their gcd. -/
theorem coprime_indicator_eq_sum_moebius_gcd
    {α β : ℕ} (hα : 0 < α) :
    (if Nat.Coprime α β then (1 : ℤ) else 0) =
      ∑ d ∈ (Nat.gcd α β).divisors, ArithmeticFunction.moebius d := by
  have hgpos : 0 < Nat.gcd α β := Nat.gcd_pos_of_pos_left β hα
  have hsum := sum_moebius_divisors_eq_indicator_one hgpos
  rw [Nat.coprime_iff_gcd_eq_one]
  exact hsum.symm

/-- In an odd exponent pair, every divisor of the gcd is odd. -/
theorem gcd_divisor_is_odd_of_left_odd
    {d α β : ℕ} (hαodd : α % 2 = 1)
    (hd : d ∣ Nat.gcd α β) :
    d % 2 = 1 := by
  have hdα : d ∣ α := dvd_trans hd (Nat.gcd_dvd_left α β)
  rcases Nat.mod_two_eq_zero_or_one d with hdeven | hdodd
  · have h2d : 2 ∣ d := Nat.dvd_of_mod_eq_zero hdeven
    have h2α : 2 ∣ α := dvd_trans h2d hdα
    have hαzero := Nat.mod_eq_zero_of_dvd h2α
    omega
  · exact hdodd

/-- For an odd exponent pair, the finite Möbius coprimality detector may be
written as a sum restricted to odd divisors.  This is the finite precursor of
the report's odd Möbius Dirichlet series. -/
theorem coprime_indicator_eq_sum_odd_moebius_gcd
    {α β : ℕ} (hα : 0 < α) (hαodd : α % 2 = 1) :
    (if Nat.Coprime α β then (1 : ℤ) else 0) =
      ∑ d ∈ (Nat.gcd α β).divisors.filter (fun d => d % 2 = 1),
        ArithmeticFunction.moebius d := by
  have hall :
      ∀ d ∈ (Nat.gcd α β).divisors, d % 2 = 1 := by
    intro d hd
    have hdvd : d ∣ Nat.gcd α β := (Nat.mem_divisors.mp hd).1
    exact gcd_divisor_is_odd_of_left_odd hαodd hdvd
  have hfilter :
      (Nat.gcd α β).divisors.filter (fun d => d % 2 = 1) =
        (Nat.gcd α β).divisors := by
    exact Finset.filter_eq_self.mpr hall
  rw [hfilter]
  exact coprime_indicator_eq_sum_moebius_gcd hα

end PrimeGPF
