import PrimeGPF.Extension7Finite
import PrimeGPF.Extension1DimensionOne
import PrimeGPF.LogAsymptotics

/-!
# Extension 7: sharp one-dimensional collision bound

When the exact collision support `T_a` consists of one prime, the general
simplex-counting problem collapses to one dimension.  In that case equation
(12) has the sharp coefficient `1 / log p` without any multidimensional
lattice machinery.
-/
namespace PrimeGPF

open Claims Filter
open scoped Topology

/-- Finite sharp collision bound when the exact allowed support is `{p}`. -/
theorem extension7_collisionCount_le_singleton_log_box
    {a p X : ℕ} (ha : Nat.Prime a)
    (hT : extension1AllowedPrimes a (gpf (a ^ 2 + a - 1)) =
      ({p} : Finset ℕ)) :
    extension7CollisionCount a X ≤
      Claims.primeCount (gpf (a ^ 2 + a - 1)) +
        (1 + ⌊Real.log ((X + a + 1 : ℕ) : ℝ) / Real.log (p : ℝ)⌋₊) := by
  let R := gpf (a ^ 2 + a - 1)
  have hfinite :=
    extension7_collisionCount_le_primeCount_add_restrictedSmoothCount
      (a := a) (X := X) ha
  have hsmooth :=
    restrictedSmoothCount_le_extension1RestrictedBoxBound
      a R (X + a + 1)
  have hbox :=
    extension1RestrictedBoxBound_of_allowedPrimes_eq_singleton
      (a := a) (r := R) (p := p) (x := X + a + 1) (by simpa [R] using hT)
  calc
    extension7CollisionCount a X
        ≤ Claims.primeCount R + restrictedSmoothCount a R (X + a + 1) := by
          simpa [R] using hfinite
    _ ≤ Claims.primeCount R + extension1RestrictedBoxBound a R (X + a + 1) :=
      Nat.add_le_add_left hsmooth _
    _ = Claims.primeCount R +
        (1 + ⌊Real.log ((X + a + 1 : ℕ) : ℝ) / Real.log (p : ℝ)⌋₊) := by
      rw [hbox]
    _ = Claims.primeCount (gpf (a ^ 2 + a - 1)) +
        (1 + ⌊Real.log ((X + a + 1 : ℕ) : ℝ) / Real.log (p : ℝ)⌋₊) := by
      rfl

/-- Real-valued singleton-support collision bound with the floor removed. -/
theorem extension7_collisionCount_real_le_singleton_log
    {a p X : ℕ} (ha : Nat.Prime a) (hp : Nat.Prime p)
    (hT : extension1AllowedPrimes a (gpf (a ^ 2 + a - 1)) =
      ({p} : Finset ℕ)) :
    (extension7CollisionCount a X : ℝ) ≤
      (Claims.primeCount (gpf (a ^ 2 + a - 1)) : ℝ) + 1 +
        Real.log ((X + a + 1 : ℕ) : ℝ) / Real.log (p : ℝ) := by
  have hnat := extension7_collisionCount_le_singleton_log_box
    (a := a) (p := p) (X := X) ha hT
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  have harg1 : (1 : ℝ) ≤ ((X + a + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ X + a + 1 by omega)
  have hquot0 :
      0 ≤ Real.log ((X + a + 1 : ℕ) : ℝ) / Real.log (p : ℝ) :=
    div_nonneg (Real.log_nonneg harg1) hlogp.le
  have hfloor :
      (⌊Real.log ((X + a + 1 : ℕ) : ℝ) / Real.log (p : ℝ)⌋₊ : ℝ) ≤
        Real.log ((X + a + 1 : ℕ) : ℝ) / Real.log (p : ℝ) :=
    Nat.floor_le hquot0
  have hnatR :
      (extension7CollisionCount a X : ℝ) ≤
        (Claims.primeCount (gpf (a ^ 2 + a - 1)) : ℝ) +
          ((1 + ⌊Real.log ((X + a + 1 : ℕ) : ℝ) /
            Real.log (p : ℝ)⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast hnat
  calc
    (extension7CollisionCount a X : ℝ)
        ≤ (Claims.primeCount (gpf (a ^ 2 + a - 1)) : ℝ) +
          ((1 + ⌊Real.log ((X + a + 1 : ℕ) : ℝ) /
            Real.log (p : ℝ)⌋₊ : ℕ) : ℝ) := hnatR
    _ = (Claims.primeCount (gpf (a ^ 2 + a - 1)) : ℝ) + 1 +
          (⌊Real.log ((X + a + 1 : ℕ) : ℝ) /
            Real.log (p : ℝ)⌋₊ : ℝ) := by
      push_cast
      ring
    _ ≤ (Claims.primeCount (gpf (a ^ 2 + a - 1)) : ℝ) + 1 +
          Real.log ((X + a + 1 : ℕ) : ℝ) / Real.log (p : ℝ) :=
      add_le_add_left hfloor _

/-- Sharp dimension-one specialization of equation (12). -/
theorem extension7_singleton_collision_ratio_limsup_le
    {a p : ℕ} (ha : Nat.Prime a) (hp : Nat.Prime p)
    (hT : extension1AllowedPrimes a (gpf (a ^ 2 + a - 1)) =
      ({p} : Finset ℕ)) :
    limsup
      (fun X : ℕ =>
        (extension7CollisionCount a X : ℝ) / Real.log (X : ℝ))
      atTop ≤ (1 : ℝ) / Real.log (p : ℝ) := by
  apply limsup_div_log_le_inv_log_of_le
    (p := p) (c := a + 1)
    (B := (Claims.primeCount (gpf (a ^ 2 + a - 1)) : ℝ) + 1)
    hp.one_lt
  · intro X
    positivity
  · intro X
    simpa [Nat.add_assoc] using
      (extension7_collisionCount_real_le_singleton_log
        (a := a) (p := p) (X := X) ha hp hT)

end PrimeGPF
