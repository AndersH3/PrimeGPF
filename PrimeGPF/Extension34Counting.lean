import PrimeGPF.Extension2Dimension
import PrimeGPF.Extension34Exact

/-!
# Extensions 3 and 4: non-sharp counting corollaries

The exact arithmetic classifications are already formalized separately.  This
file specializes the general restricted-support multiplicative-fiber bound to
output 5 at anchors 2 and 3.  In both cases the allowed support has exactly two
primes, so the fiber has a quadratic polylogarithmic upper bound.  The sharper
coefficients involving parity and coprimality remain part of the later
Möbius/lattice-counting layer.
-/
namespace PrimeGPF
open Claims

/-- The only primes at most five are `2`, `3`, and `5`. -/
lemma claims_primeCount_five : Claims.primeCount 5 = 3 := by
  classical
  rw [Claims.primeCount]
  have hset :
      (Finset.range 6).filter Nat.Prime = ({2, 3, 5} : Finset ℕ) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hp6, hp⟩
      interval_cases p <;> norm_num at hp ⊢
    · rintro (rfl | rfl | rfl) <;> norm_num
  rw [hset]
  norm_num

lemma extension3_allowedPrimeCount :
    extension2AllowedPrimeCount 2 5 = 2 := by
  rw [extension2_allowedPrimeCount_eq_primeCount_sub_one
    (a := 2) (r := 5) (by norm_num) (by norm_num), claims_primeCount_five]
  norm_num

lemma extension4_allowedPrimeCount :
    extension2AllowedPrimeCount 3 5 = 2 := by
  rw [extension2_allowedPrimeCount_eq_primeCount_sub_one
    (a := 3) (r := 5) (by norm_num) (by norm_num), claims_primeCount_five]
  norm_num

/-- Non-sharp degree-two bound for the output-5 multiplicative fiber at anchor
2. -/
theorem extension3_fiberCount_real_le_log_sq
    {X : ℕ} (hx : 2 ≤ 2 * X + 1) :
    (Claims.fiberCount .mul 2 5 X : ℝ) ≤
      (2 / Real.log 2) ^ 2 *
        (Real.log ((2 * X + 1 : ℕ) : ℝ)) ^ 2 := by
  have h := extension2_fiberCount_real_le_polylog
    (a := 2) (r := 5) (X := X) (by norm_num) hx
  simpa [extension3_allowedPrimeCount] using h

/-- Non-sharp degree-two bound for the output-5 multiplicative fiber at anchor
3. -/
theorem extension4_fiberCount_real_le_log_sq
    {X : ℕ} (hx : 2 ≤ 3 * X + 1) :
    (Claims.fiberCount .mul 3 5 X : ℝ) ≤
      (2 / Real.log 2) ^ 2 *
        (Real.log ((3 * X + 1 : ℕ) : ℝ)) ^ 2 := by
  have h := extension2_fiberCount_real_le_polylog
    (a := 3) (r := 5) (X := X) (by norm_num) hx
  simpa [extension4_allowedPrimeCount] using h

end PrimeGPF
