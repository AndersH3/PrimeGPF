import PrimeGPF.Progressions
import Mathlib.NumberTheory.LSeries.PrimesInAP

open Filter Topology ArithmeticFunction

namespace PrimeGPF

/-- Logarithmically weighted prime count in the same residue-class convention as `Claims.apCount`. -/
noncomputable def thetaAPCount (r c x : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (x + 1),
    if n.Prime ∧ n % r = c % r then Real.log n else 0

/-- Rewrite the weighted count as a sum over the filtered prime residue class. -/
theorem thetaAPCount_eq_sum_filter (r c x : ℕ) :
    thetaAPCount r c x =
      ∑ n ∈ (Finset.range (x + 1)).filter
          (fun n => n.Prime ∧ n % r = c % r),
        Real.log n := by
  classical
  simp [thetaAPCount, Finset.sum_filter]

/--
A first unweighting inequality: the theta-type sum is at most the number of
primes in the progression times the endpoint logarithm.
-/
theorem thetaAPCount_le_apCount_mul_log
    (r c x : ℕ) (hx : 2 ≤ x) :
    thetaAPCount r c x ≤
      (Claims.apCount r c x : ℝ) * Real.log x := by
  classical
  rw [thetaAPCount_eq_sum_filter]
  change
    (∑ n ∈ (Finset.range (x + 1)).filter
        (fun n => n.Prime ∧ n % r = c % r), Real.log n) ≤
      (((Finset.range (x + 1)).filter
        (fun n => n.Prime ∧ n % r = c % r)).card : ℝ) * Real.log x
  rw [← Finset.sum_const, Nat.cast_smul_eq_nsmul]
  apply Finset.sum_le_sum
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  have hnle : n ≤ x := Nat.lt_succ_iff.mp (by simpa [Nat.lt_add_one_iff] using hn.1)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn.2.1.pos
  have hxpos : 0 < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hx)
  exact Real.strictMonoOn_log.monotoneOn hnpos hxpos (by exact_mod_cast hnle)

#check thetaAPCount
#check thetaAPCount_eq_sum_filter
#check thetaAPCount_le_apCount_mul_log
#print axioms thetaAPCount_le_apCount_mul_log

end PrimeGPF
