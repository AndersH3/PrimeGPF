import PrimeGPF.Extensions

/-!
# Corollary to extension 8

If `p^2 + p - 1` is prime (for prime `p ≥ 3`), there is no triple
collision at anchor `p`.
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
  have hex : (p, q) ≠ (2, 3) := by
    intro h
    have hp2 : p = 2 := congrArg Prod.fst h
    omega
  have hqp : q ≤ p :=
    (extension8_add_exp_region hp hq hae).resolve_left hex
  have hupper : r ≤ p + q + 1 := by
    dsimp [r]
    simpa [add, output, kernel] using gpf_le (p + q + 1)
  have hupper' : r ≤ 2 * p + 1 := by omega
  rw [hre] at hupper'
  have hpos : 1 ≤ p ^ 2 + p := by
    have hp0 : 0 < p := hp.pos
    nlinarith
  have hsub : (p ^ 2 + p - 1) + 1 = p ^ 2 + p :=
    Nat.sub_add_cancel hpos
  have hquadle : p ^ 2 + p ≤ 2 * p + 2 := by
    omega
  nlinarith

end PrimeGPF
