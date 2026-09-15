import PrimeGPF.Extension2Dimension
import PrimeGPF.Extension34Exact
import PrimeGPF.Extension34FiberCounting

/-!
# Extensions 3 and 4: counting corollaries

This module keeps the original rectangular-box estimates because they are
simple, exact finite bounds obtained directly from the general restricted-
support theory.  The sharper weighted-triangle bounds are now imported from
`Extension34FiberCounting`.

The two layers serve different purposes:

* **rectangular box:** elementary and completely explicit, but with a coarse
  leading constant;
* **weighted triangle:** uses the actual logarithmic inequality and therefore
  has the sharp geometric leading coefficient `1 / (2*u*v)` before parity and
  coprimality corrections.

The final report constants involving `1/ζ(2)` still require the later
parity-restricted Möbius count.
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

/-- At anchor 2 and output 5, the exact exponent support is `{3,5}`. -/
lemma extension3_allowedPrimes :
    extension2AllowedPrimes 2 5 = ({3, 5} : Finset ℕ) := by
  classical
  ext p
  simp only [extension2AllowedPrimes, Finset.mem_filter, Finset.mem_range,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hp6, hp, hp2⟩
    interval_cases p <;> norm_num at hp hp2 ⊢
  · rintro (rfl | rfl) <;> norm_num

/-- At anchor 3 and output 5, the exact exponent support is `{2,5}`. -/
lemma extension4_allowedPrimes :
    extension2AllowedPrimes 3 5 = ({2, 5} : Finset ℕ) := by
  classical
  ext p
  simp only [extension2AllowedPrimes, Finset.mem_filter, Finset.mem_range,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hp6, hp, hp3⟩
    interval_cases p <;> norm_num at hp hp3 ⊢
  · rintro (rfl | rfl) <;> norm_num

/-- Both exact supports have cardinality two. -/
lemma extension3_allowedPrimeCount :
    extension2AllowedPrimeCount 2 5 = 2 := by
  rw [extension2_allowedPrimeCount_eq_primeCount_sub_one
    (a := 2) (r := 5) (by norm_num) (by norm_num), claims_primeCount_five]

lemma extension4_allowedPrimeCount :
    extension2AllowedPrimeCount 3 5 = 2 := by
  rw [extension2_allowedPrimeCount_eq_primeCount_sub_one
    (a := 3) (r := 5) (by norm_num) (by norm_num), claims_primeCount_five]

/-- The exact rectangular exponent box for Extension 3.  The sharper triangle
bound imported above replaces this rectangle only when a better leading
constant is needed. -/
theorem extension3RestrictedBoxBound_exact (x : ℕ) :
    extension2RestrictedBoxBound 2 5 x =
      (1 + ⌊Real.log (x : ℝ) / Real.log (3 : ℝ)⌋₊) *
      (1 + ⌊Real.log (x : ℝ) / Real.log (5 : ℝ)⌋₊) := by
  classical
  simp [extension2RestrictedBoxBound, extension3_allowedPrimes,
    mul_comm, mul_left_comm, mul_assoc]

/-- The exact rectangular exponent box for Extension 4. -/
theorem extension4RestrictedBoxBound_exact (x : ℕ) :
    extension2RestrictedBoxBound 3 5 x =
      (1 + ⌊Real.log (x : ℝ) / Real.log (2 : ℝ)⌋₊) *
      (1 + ⌊Real.log (x : ℝ) / Real.log (5 : ℝ)⌋₊) := by
  classical
  simp [extension2RestrictedBoxBound, extension4_allowedPrimes,
    mul_comm, mul_left_comm, mul_assoc]

/-- Explicit finite rectangular-box bound for the anchor-2, output-5 fiber. -/
theorem extension3_fiberCount_le_exact_log_box (X : ℕ) :
    Claims.fiberCount .mul 2 5 X ≤
      (1 + ⌊Real.log ((2 * X + 1 : ℕ) : ℝ) / Real.log (3 : ℝ)⌋₊) *
      (1 + ⌊Real.log ((2 * X + 1 : ℕ) : ℝ) / Real.log (5 : ℝ)⌋₊) := by
  calc
    Claims.fiberCount .mul 2 5 X
        ≤ mulRestrictedSmoothCount 2 5 (2 * X + 1) :=
      extension2_fiberCount_le_mulRestrictedSmoothCount
        (r := 5) (X := X) (by norm_num)
    _ ≤ extension2RestrictedBoxBound 2 5 (2 * X + 1) :=
      mulRestrictedSmoothCount_le_extension2RestrictedBoxBound
        2 5 (2 * X + 1)
    _ = (1 + ⌊Real.log ((2 * X + 1 : ℕ) : ℝ) / Real.log (3 : ℝ)⌋₊) *
        (1 + ⌊Real.log ((2 * X + 1 : ℕ) : ℝ) / Real.log (5 : ℝ)⌋₊) :=
      extension3RestrictedBoxBound_exact (2 * X + 1)

/-- Explicit finite rectangular-box bound for the anchor-3, output-5 fiber. -/
theorem extension4_fiberCount_le_exact_log_box (X : ℕ) :
    Claims.fiberCount .mul 3 5 X ≤
      (1 + ⌊Real.log ((3 * X + 1 : ℕ) : ℝ) / Real.log (2 : ℝ)⌋₊) *
      (1 + ⌊Real.log ((3 * X + 1 : ℕ) : ℝ) / Real.log (5 : ℝ)⌋₊) := by
  calc
    Claims.fiberCount .mul 3 5 X
        ≤ mulRestrictedSmoothCount 3 5 (3 * X + 1) :=
      extension2_fiberCount_le_mulRestrictedSmoothCount
        (r := 5) (X := X) (by norm_num)
    _ ≤ extension2RestrictedBoxBound 3 5 (3 * X + 1) :=
      mulRestrictedSmoothCount_le_extension2RestrictedBoxBound
        3 5 (3 * X + 1)
    _ = (1 + ⌊Real.log ((3 * X + 1 : ℕ) : ℝ) / Real.log (2 : ℝ)⌋₊) *
        (1 + ⌊Real.log ((3 * X + 1 : ℕ) : ℝ) / Real.log (5 : ℝ)⌋₊) :=
      extension4RestrictedBoxBound_exact (3 * X + 1)

/-- Coarse degree-two bound inherited from the general multiplicative-fiber
theory.  Prefer `extension3_fiberCount_cast_le_area_boundary` when the sharper
geometric coefficient is useful. -/
theorem extension3_fiberCount_real_le_log_sq
    {X : ℕ} (hx : 2 ≤ 2 * X + 1) :
    (Claims.fiberCount .mul 2 5 X : ℝ) ≤
      (2 / Real.log 2) ^ 2 *
        (Real.log ((2 * X + 1 : ℕ) : ℝ)) ^ 2 := by
  have h := extension2_fiberCount_real_le_polylog
    (a := 2) (r := 5) (X := X) (by norm_num) hx
  simpa [extension3_allowedPrimeCount] using h

/-- Coarse degree-two bound inherited from the general multiplicative-fiber
theory.  Prefer `extension4_fiberCount_cast_le_area_boundary` when the sharper
geometric coefficient is useful. -/
theorem extension4_fiberCount_real_le_log_sq
    {X : ℕ} (hx : 2 ≤ 3 * X + 1) :
    (Claims.fiberCount .mul 3 5 X : ℝ) ≤
      (2 / Real.log 2) ^ 2 *
        (Real.log ((3 * X + 1 : ℕ) : ℝ)) ^ 2 := by
  have h := extension2_fiberCount_real_le_polylog
    (a := 3) (r := 5) (X := X) (by norm_num) hx
  simpa [extension4_allowedPrimeCount] using h

end PrimeGPF
