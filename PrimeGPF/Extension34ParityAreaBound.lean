import PrimeGPF.Extension34CandidateCount
import PrimeGPF.Extension34ParityReduction

/-!
# Extensions 3 and 4: parity-improved finite area bounds

Applying the generic weighted-triangle area estimate after the parity scaling
improves the leading full-triangle coefficients by factors `1/2` and `1/4`.
The only remaining leading-constant refinement is therefore coprimality, which
is handled separately by Möbius inversion.
-/
namespace PrimeGPF

open Claims
open PrimeGPF.Analytic

/-- Anchor 2, output 5: after using the oddness of the first exponent, the
leading finite area coefficient is `1 / (4 log 3 log 5)`. -/
theorem extension3_fiberCount_real_le_parity_area
    (X : ℕ) (hX : 1 ≤ X) :
    let L := Real.log ((2 * X + 1 : ℕ) : ℝ) - Real.log 3
    (Claims.fiberCount .mul 2 5 X : ℝ) ≤
      L ^ 2 / (4 * Real.log 3 * Real.log 5) +
        L / (2 * Real.log 3) + 3 * L / (2 * Real.log 5) + 2 := by
  dsimp
  let L := Real.log ((2 * X + 1 : ℕ) : ℝ) - Real.log 3
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hlog5 : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  have harg : (3 : ℝ) ≤ ((2 * X + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 3 ≤ 2 * X + 1 by omega)
  have hlogle : Real.log (3 : ℝ) ≤ Real.log ((2 * X + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) harg
  have hL : 0 ≤ L := by
    dsimp [L]
    linarith
  have hfiber := extension3_fiberCount_le_candidatePairs_add_one X
  have hparity := extension3_candidatePairs_card_le_parityTriangle X
  have harea := weightedTriangle_card_cast_le_area_boundary
    (u := 2 * Real.log 3) (v := Real.log 5) (L := L)
    (by positivity) hlog5 hL
  calc
    (Claims.fiberCount .mul 2 5 X : ℝ)
        ≤ ((extension3CandidatePairs X).card : ℝ) + 1 := by
          exact_mod_cast hfiber
    _ ≤ ((weightedTriangle (2 * Real.log 3) (Real.log 5) L).card : ℝ) + 1 := by
          exact_mod_cast Nat.add_le_add_right hparity 1
    _ ≤ L ^ 2 / (2 * (2 * Real.log 3) * Real.log 5) +
          L / (2 * Real.log 3) + 3 * L / (2 * Real.log 5) + 2 := by
          linarith
    _ = L ^ 2 / (4 * Real.log 3 * Real.log 5) +
          L / (2 * Real.log 3) + 3 * L / (2 * Real.log 5) + 2 := by ring
    _ = (Real.log ((2 * X + 1 : ℕ) : ℝ) - Real.log 3) ^ 2 /
          (4 * Real.log 3 * Real.log 5) +
        (Real.log ((2 * X + 1 : ℕ) : ℝ) - Real.log 3) /
          (2 * Real.log 3) +
        3 * (Real.log ((2 * X + 1 : ℕ) : ℝ) - Real.log 3) /
          (2 * Real.log 5) + 2 := by rfl

/-- Anchor 3, output 5: using oddness of both exponents gives leading finite
area coefficient `1 / (8 log 2 log 5)`. -/
theorem extension4_fiberCount_real_le_parity_area
    (X : ℕ) (hX : 3 ≤ X) :
    let L := Real.log ((3 * X + 1 : ℕ) : ℝ) - Real.log 2 - Real.log 5
    (Claims.fiberCount .mul 3 5 X : ℝ) ≤
      L ^ 2 / (8 * Real.log 2 * Real.log 5) +
        L / (2 * Real.log 2) + 3 * L / (4 * Real.log 5) + 1 := by
  dsimp
  let L := Real.log ((3 * X + 1 : ℕ) : ℝ) - Real.log 2 - Real.log 5
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog5 : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  have harg : (10 : ℝ) ≤ ((3 * X + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 10 ≤ 3 * X + 1 by omega)
  have hlogle : Real.log (10 : ℝ) ≤ Real.log ((3 * X + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) harg
  have hsum : Real.log (2 : ℝ) + Real.log (5 : ℝ) = Real.log 10 := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)]
    norm_num
  have hL : 0 ≤ L := by
    dsimp [L]
    linarith
  have hfiber := extension4_fiberCount_le_candidatePairs X
  have hparity := extension4_candidatePairs_card_le_parityTriangle X
  have harea := weightedTriangle_card_cast_le_area_boundary
    (u := 2 * Real.log 2) (v := 2 * Real.log 5) (L := L)
    (by positivity) (by positivity) hL
  calc
    (Claims.fiberCount .mul 3 5 X : ℝ)
        ≤ ((extension4CandidatePairs X).card : ℝ) := by
          exact_mod_cast hfiber
    _ ≤ ((weightedTriangle (2 * Real.log 2) (2 * Real.log 5) L).card : ℝ) := by
          exact_mod_cast hparity
    _ ≤ L ^ 2 / (2 * (2 * Real.log 2) * (2 * Real.log 5)) +
          L / (2 * Real.log 2) + 3 * L / (2 * (2 * Real.log 5)) + 1 := harea
    _ = L ^ 2 / (8 * Real.log 2 * Real.log 5) +
          L / (2 * Real.log 2) + 3 * L / (4 * Real.log 5) + 1 := by ring
    _ = (Real.log ((3 * X + 1 : ℕ) : ℝ) - Real.log 2 - Real.log 5) ^ 2 /
          (8 * Real.log 2 * Real.log 5) +
        (Real.log ((3 * X + 1 : ℕ) : ℝ) - Real.log 2 - Real.log 5) /
          (2 * Real.log 2) +
        3 * (Real.log ((3 * X + 1 : ℕ) : ℝ) - Real.log 2 - Real.log 5) /
          (4 * Real.log 5) + 1 := by rfl

end PrimeGPF
