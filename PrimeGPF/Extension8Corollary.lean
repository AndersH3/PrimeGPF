import PrimeGPF.Extensions

/-!
# Corollary to extension 8

If `p^2 + p - 1` is prime (for prime `p ≥ 3`), there is no triple
collision at anchor `p`.

The proof has three stages.  A common additive/multiplicative output divides
the polynomial `p^2+p-1`; primality of the polynomial therefore identifies
the output with that polynomial.  The additive/exponential collision region
then gives `q ≤ p`, while the additive kernel bounds the same output by
`2p+1`.  These two descriptions are incompatible for `p ≥ 3`.
-/
namespace PrimeGPF

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- If `p^2+p-1` is prime, no second prime input can give a triple collision
at anchor `p`. -/
theorem extension8_no_triple_of_polynomial_prime {p : ℕ}
    (hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (hP : Nat.Prime (p ^ 2 + p - 1)) :
    ¬ ∃ q, Nat.Prime q ∧ add p q = mul p q ∧ add p q = exp p q := by
  rintro ⟨q, hq, ham, hae⟩
  let r := add p q

  -- The common additive/multiplicative output divides the collision
  -- polynomial, so polynomial primality forces equality.
  have hr : Nat.Prime r := (output_spec .add hp hq).1
  have hda : r ∣ p + q + 1 := (output_spec .add hp hq).2.1
  have hdm : r ∣ p * q + 1 := by
    have hm := (output_spec .mul hp hq).2.1
    simpa [r, ham] using hm
  have hdiv : r ∣ p ^ 2 + p - 1 := collision_divisor hda hdm
  have hre : r = p ^ 2 + p - 1 := by
    rcases (Nat.dvd_prime hP).mp hdiv with h1 | hP'
    · exact (hr.ne_one h1).elim
    · exact hP'

  -- The additive/exponential collision lies in the `q ≤ p` region except
  -- for `(2,3)`, which is excluded by the hypothesis `p ≥ 3`.
  have hex : (p, q) ≠ (2, 3) := by
    intro h
    have hp2 : p = 2 := congrArg Prod.fst h
    omega
  have hqp : q ≤ p :=
    (extension8_add_exp_region hp hq hae).resolve_left hex

  -- The additive output is at most its kernel `p+q+1`, hence at most
  -- `2p+1`.  Substituting the polynomial value of `r` yields the final
  -- quadratic contradiction.
  have hupper : r ≤ p + q + 1 := by
    dsimp [r]
    simpa [add, output, kernel] using gpf_le (p + q + 1)
  have hupper' : r ≤ 2 * p + 1 := by omega
  rw [hre] at hupper'
  have hquadle : p ^ 2 + p ≤ 2 * p + 2 := by
    omega
  nlinarith

end PrimeGPF
