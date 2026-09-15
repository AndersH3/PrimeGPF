import PrimeGPF.Extension34MobiusFinite
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Extensions 3 and 4: the odd Möbius Dirichlet-series factor

The finite Möbius detector reduces primitivity to a sum over common divisors.
Because the relevant exponent vectors are odd, only odd common divisors occur.
The analytic constant needed in equations (4) and (6) is therefore

`sum_{g odd} μ(g) / g^2 = 4 / (3 * ζ(2))`.

Rather than re-proving an Euler product, we use Mathlib's Dirichlet-character
infrastructure.  The trivial character modulo `2` is the indicator of odd
integers.  Mathlib proves both:

* its L-function is `(1 - 2^{-s}) * riemannZeta s`;
* its L-series multiplied by the L-series of its Möbius twist is `1` for
  `re s > 1`.

At `s = 2`, the first factor is `3/4`, so the Möbius-twisted series is exactly
`4 / (3 * riemannZeta 2)`.
-/
namespace PrimeGPF

open Complex
open scoped LSeries.notation ArithmeticFunction.Moebius

/-- The trivial Dirichlet character modulo two.  As a function on naturals it
vanishes on even numbers and equals one on odd numbers. -/
noncomputable abbrev extension34OddCharacter : DirichletCharacter ℂ 2 := 1

/-- At `s = 2`, the L-series of the odd-number indicator is
`(3/4) * ζ(2)`. -/
theorem extension34_oddCharacter_LSeries_two :
    LSeries (extension34OddCharacter ·) (2 : ℂ) =
      (3 / 4 : ℂ) * riemannZeta 2 := by
  have hseries :=
    DirichletCharacter.LFunction_eq_LSeries
      extension34OddCharacter (s := (2 : ℂ)) (by norm_num)
  have htriv :=
    DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta
      (N := 2) (s := (2 : ℂ)) (by norm_num)
  have hpf : (2 : ℕ).primeFactors = ({2} : Finset ℕ) := by
    norm_num [Nat.primeFactors]
  have heuler :
      (∏ p ∈ (2 : ℕ).primeFactors,
          (1 - (p : ℂ) ^ (-(2 : ℂ)))) = (3 / 4 : ℂ) := by
    rw [hpf]
    simp only [Finset.prod_singleton]
    norm_num
  calc
    LSeries (extension34OddCharacter ·) (2 : ℂ) =
        DirichletCharacter.LFunction extension34OddCharacter 2 := hseries.symm
    _ = DirichletCharacter.LFunctionTrivChar 2 2 := rfl
    _ = (∏ p ∈ (2 : ℕ).primeFactors,
          (1 - (p : ℂ) ^ (-(2 : ℂ)))) * riemannZeta 2 := htriv
    _ = (3 / 4 : ℂ) * riemannZeta 2 := by rw [heuler]

/-- The L-series of the odd Möbius coefficients at `2` has the exact factor
`4 / (3 ζ(2))` appearing in the report.

The coefficient function is written explicitly as the pointwise product of
the trivial character modulo two and the Möbius function; this is exactly the
odd part of the Möbius Dirichlet series. -/
theorem extension34_odd_moebius_LSeries_two :
    LSeries
        (fun n : ℕ =>
          extension34OddCharacter n *
            (ArithmeticFunction.moebius n : ℂ))
        (2 : ℂ) =
      4 / (3 * riemannZeta 2) := by
  have hmul :=
    DirichletCharacter.LSeries.mul_mu_eq_one
      extension34OddCharacter (s := (2 : ℂ)) (by norm_num)
  have hchar := extension34_oddCharacter_LSeries_two
  have hmul' :
      ((3 / 4 : ℂ) * riemannZeta 2) *
        LSeries
          (fun n : ℕ =>
            extension34OddCharacter n *
              (ArithmeticFunction.moebius n : ℂ))
          (2 : ℂ) = 1 := by
    simpa [hchar] using hmul

  have hleft_ne : (3 / 4 : ℂ) * riemannZeta 2 ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hmul'
    norm_num at hmul'
  have hzeta_ne : riemannZeta 2 ≠ 0 := by
    intro hz
    apply hleft_ne
    rw [hz, mul_zero]
  have hden_ne : (3 : ℂ) * riemannZeta 2 ≠ 0 :=
    mul_ne_zero (by norm_num) hzeta_ne

  apply (eq_div_iff hden_ne).2
  calc
    LSeries
          (fun n : ℕ =>
            extension34OddCharacter n *
              (ArithmeticFunction.moebius n : ℂ))
          (2 : ℂ) * (3 * riemannZeta 2)
        = 4 *
            (((3 / 4 : ℂ) * riemannZeta 2) *
              LSeries
                (fun n : ℕ =>
                  extension34OddCharacter n *
                    (ArithmeticFunction.moebius n : ℂ))
                (2 : ℂ)) := by ring
    _ = 4 := by rw [hmul']; norm_num

end PrimeGPF
