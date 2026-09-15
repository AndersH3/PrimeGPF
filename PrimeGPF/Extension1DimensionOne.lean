import PrimeGPF.Extension1RestrictedCounting
import PrimeGPF.LogAsymptotics
import Mathlib

/-!
# Extension 1: sharp one-dimensional support bound

The general sharp simplex coefficient still requires a multidimensional
lattice-counting argument.  When the exact allowed support has one prime,
however, the exponent box is already the simplex, so the sharp coefficient is
available directly from the existing finite injection.
-/
namespace PrimeGPF
open Claims Filter
open scoped Topology

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

/-- Epsilon form of the sharp one-dimensional specialization of equation (1). -/
theorem extension1_singleton_ratio_eventually_le
    {a r p : ℕ} (ha : Nat.Prime a) (hr : Nat.Prime r) (hp : Nat.Prime p)
    (hT : extension1AllowedPrimes a r = ({p} : Finset ℕ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      (Claims.fiberCount .add a r X : ℝ) / Real.log (X : ℝ) ≤
        (1 : ℝ) / Real.log (p : ℝ) + ε := by
  let B : ℝ := (Claims.primeCount r : ℝ) + 1
  have hp1 : 1 < p := hp.one_lt
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hp1)
  have hlogTop :
      Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv :
      Tendsto (fun X : ℕ => (Real.log (X : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlogTop
  have hfixed :
      Tendsto (fun X : ℕ => B / Real.log (X : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hinv.const_mul B
  have hshift := fixed_add_log_ratio_tendsto_one (a + 1)
  have hshiftScaled :
      Tendsto
        (fun X : ℕ =>
          (Real.log ((X + a + 1 : ℕ) : ℝ) / Real.log (X : ℝ)) /
            Real.log (p : ℝ))
        atTop (𝓝 ((1 : ℝ) / Real.log (p : ℝ))) := by
    simpa [Nat.add_assoc] using hshift.div_const (Real.log (p : ℝ))
  have hupperLimit :
      Tendsto
        (fun X : ℕ =>
          B / Real.log (X : ℝ) +
            (Real.log ((X + a + 1 : ℕ) : ℝ) / Real.log (X : ℝ)) /
              Real.log (p : ℝ))
        atTop (𝓝 ((1 : ℝ) / Real.log (p : ℝ))) := by
    simpa using hfixed.add hshiftScaled
  have hlt :
      (1 : ℝ) / Real.log (p : ℝ) <
        (1 : ℝ) / Real.log (p : ℝ) + ε :=
    lt_add_of_pos_right _ hε
  have heventUpper := hupperLimit.eventually (Iio_mem_nhds hlt)
  filter_upwards [heventUpper, eventually_ge_atTop (2 : ℕ)] with X hUpper hX
  have hlogXpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hf := extension1_fiberCount_real_le_singleton_log
    (a := a) (r := r) (p := p) (X := X) ha hr hp hT
  have hdiv :
      (Claims.fiberCount .add a r X : ℝ) / Real.log (X : ℝ) ≤
        ((Claims.primeCount r : ℝ) + 1 +
          Real.log ((X + a + 1 : ℕ) : ℝ) / Real.log (p : ℝ)) /
            Real.log (X : ℝ) :=
    div_le_div_of_nonneg_right hf hlogXpos.le
  calc
    (Claims.fiberCount .add a r X : ℝ) / Real.log (X : ℝ)
        ≤ ((Claims.primeCount r : ℝ) + 1 +
          Real.log ((X + a + 1 : ℕ) : ℝ) / Real.log (p : ℝ)) /
            Real.log (X : ℝ) := hdiv
    _ = B / Real.log (X : ℝ) +
          (Real.log ((X + a + 1 : ℕ) : ℝ) / Real.log (X : ℝ)) /
            Real.log (p : ℝ) := by
      dsimp [B]
      field_simp [hlogXpos.ne', hlogp.ne']
      ring
    _ ≤ (1 : ℝ) / Real.log (p : ℝ) + ε := hUpper.le

/-- Equation (1) with the report's sharp coefficient in every case where the
exact allowed support has dimension one. -/
theorem extension1_singleton_ratio_limsup_le
    {a r p : ℕ} (ha : Nat.Prime a) (hr : Nat.Prime r) (hp : Nat.Prime p)
    (hT : extension1AllowedPrimes a r = ({p} : Finset ℕ)) :
    limsup
      (fun X : ℕ =>
        (Claims.fiberCount .add a r X : ℝ) / Real.log (X : ℝ))
      atTop ≤ (1 : ℝ) / Real.log (p : ℝ) := by
  let u : ℕ → ℝ := fun X =>
    (Claims.fiberCount .add a r X : ℝ) / Real.log (X : ℝ)
  have hu0 : ∀ X, 0 ≤ u X := by
    intro X
    dsimp [u]
    cases X with
    | zero => simp
    | succ X =>
        have hcast : (1 : ℝ) ≤ ((X + 1 : ℕ) : ℝ) := by positivity
        exact div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hcast)
  have hcob : IsCoboundedUnder (· ≤ ·) atTop u :=
    isCoboundedUnder_le_of_le atTop (x := 0) hu0
  have hbound : IsBoundedUnder (· ≤ ·) atTop u := by
    apply isBoundedUnder_of_eventually_le
    simpa [u] using
      (extension1_singleton_ratio_eventually_le ha hr hp hT
        (ε := (1 : ℝ)) (by norm_num))
  rw [limsup_le_iff' hcob hbound]
  intro y hy
  have hε : 0 < y - (1 : ℝ) / Real.log (p : ℝ) := sub_pos.mpr hy
  have hev := extension1_singleton_ratio_eventually_le ha hr hp hT hε
  filter_upwards [hev] with X hX
  dsimp [u]
  calc
    (Claims.fiberCount .add a r X : ℝ) / Real.log (X : ℝ)
        ≤ (1 : ℝ) / Real.log (p : ℝ) +
            (y - (1 : ℝ) / Real.log (p : ℝ)) := hX
    _ = y := by ring

end PrimeGPF
