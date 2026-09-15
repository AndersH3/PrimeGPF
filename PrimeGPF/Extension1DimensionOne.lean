import PrimeGPF.Extension1RestrictedCounting

/-!
# Extension 1: sharp one-dimensional support bound

The general sharp simplex coefficient still requires a multidimensional
lattice-counting argument.  When the exact allowed support has one prime,
however, the exponent box is already the simplex, so the sharp coefficient is
available directly from the existing finite injection.
-/
namespace PrimeGPF
open Claims

/-- If the exact allowed support is the singleton `{p}`, the restricted
exponent box is exactly `1 + floor(log x / log p)`. -/
theorem extension1RestrictedBoxBound_of_allowedPrimes_eq_singleton
    {a r p x : ℕ}
    (hT : extension1AllowedPrimes a r = ({p} : Finset ℕ)) :
    extension1RestrictedBoxBound a r x =
      1 + ⌊Real.log (x : ℝ) / Real.log (p : ℝ)⌋₊ := by
  classical
  simp [extension1RestrictedBoxBound, hT]

/-- A singleton allowed support has dimension exactly one. -/
theorem extension1AllowedPrimeCount_eq_one_of_allowedPrimes_eq_singleton
    {a r p : ℕ}
    (hT : extension1AllowedPrimes a r = ({p} : Finset ℕ)) :
    extension1AllowedPrimeCount a r = 1 := by
  simp [extension1AllowedPrimeCount, hT]

/-- Finite sharp one-dimensional additive-fiber bound.  This is the exact
finite precursor of equation (1) when `|T| = 1`. -/
theorem extension1_fiberCount_le_singleton_log_box
    {a r p X : ℕ} (ha : Nat.Prime a) (hr : Nat.Prime r)
    (hT : extension1AllowedPrimes a r = ({p} : Finset ℕ)) :
    Claims.fiberCount .add a r X ≤
      Claims.primeCount r +
        (1 + ⌊Real.log ((X + a + 1 : ℕ) : ℝ) / Real.log (p : ℝ)⌋₊) := by
  have hfinite :=
    extension1_fiberCount_le_primeCount_add_restrictedSmoothCount
      (a := a) (r := r) (X := X) ha hr
  have hsmooth :=
    restrictedSmoothCount_le_extension1RestrictedBoxBound
      a r (X + a + 1)
  calc
    Claims.fiberCount .add a r X
        ≤ Claims.primeCount r + restrictedSmoothCount a r (X + a + 1) := hfinite
    _ ≤ Claims.primeCount r + extension1RestrictedBoxBound a r (X + a + 1) :=
      Nat.add_le_add_left hsmooth _
    _ = Claims.primeCount r +
        (1 + ⌊Real.log ((X + a + 1 : ℕ) : ℝ) /
          Real.log (p : ℝ)⌋₊) := by
      rw [extension1RestrictedBoxBound_of_allowedPrimes_eq_singleton hT]

/-- Real-valued version of the singleton-support bound, with the floor removed.
The coefficient of the logarithm is the sharp `1 / log p`. -/
theorem extension1_fiberCount_real_le_singleton_log
    {a r p X : ℕ} (ha : Nat.Prime a) (hr : Nat.Prime r) (hp : Nat.Prime p)
    (hT : extension1AllowedPrimes a r = ({p} : Finset ℕ)) :
    (Claims.fiberCount .add a r X : ℝ) ≤
      (Claims.primeCount r : ℝ) + 1 +
        Real.log ((X + a + 1 : ℕ) : ℝ) / Real.log (p : ℝ) := by
  have hnat := extension1_fiberCount_le_singleton_log_box
    (a := a) (r := r) (p := p) (X := X) ha hr hT
  have hp1 : 1 < p := hp.one_lt
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hp1)
  have harg1 : (1 : ℝ) ≤ ((X + a + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ X + a + 1 by omega)
  have hlogarg : 0 ≤ Real.log ((X + a + 1 : ℕ) : ℝ) :=
    Real.log_nonneg harg1
  have hquot0 :
      0 ≤ Real.log ((X + a + 1 : ℕ) : ℝ) / Real.log (p : ℝ) :=
    div_nonneg hlogarg hlogp.le
  have hfloor :
      (⌊Real.log ((X + a + 1 : ℕ) : ℝ) / Real.log (p : ℝ)⌋₊ : ℝ) ≤
        Real.log ((X + a + 1 : ℕ) : ℝ) / Real.log (p : ℝ) :=
    Nat.floor_le hquot0
  have hnatR :
      (Claims.fiberCount .add a r X : ℝ) ≤
        (Claims.primeCount r : ℝ) +
          ((1 + ⌊Real.log ((X + a + 1 : ℕ) : ℝ) /
            Real.log (p : ℝ)⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast hnat
  calc
    (Claims.fiberCount .add a r X : ℝ)
        ≤ (Claims.primeCount r : ℝ) +
          ((1 + ⌊Real.log ((X + a + 1 : ℕ) : ℝ) /
            Real.log (p : ℝ)⌋₊ : ℕ) : ℝ) := hnatR
    _ = (Claims.primeCount r : ℝ) + 1 +
          (⌊Real.log ((X + a + 1 : ℕ) : ℝ) /
            Real.log (p : ℝ)⌋₊ : ℝ) := by norm_num
    _ ≤ (Claims.primeCount r : ℝ) + 1 +
          Real.log ((X + a + 1 : ℕ) : ℝ) / Real.log (p : ℝ) :=
      add_le_add_left hfloor _

end PrimeGPF
