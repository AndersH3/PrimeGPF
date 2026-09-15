import PrimeGPF.Arithmetic

/-!
# Extension 7: structural core

This file isolates the elementary part of the quantitative rarity theorem for
additive--multiplicative collisions.  The asymptotic counting step is separate.
-/
namespace PrimeGPF

/-- The polynomial controlling additive--multiplicative collisions is > 1 for
prime anchors. -/
theorem extension7_polynomial_gt_one {a : ℕ} (ha : Nat.Prime a) :
    1 < a ^ 2 + a - 1 := by
  have ha2 : 2 ≤ a := ha.two_le
  have hsquare : 4 ≤ a ^ 2 := by nlinarith
  omega

/-- The greatest prime factor `R_a` occurring in extension 7 is prime. -/
theorem extension7_R_prime {a : ℕ} (ha : Nat.Prime a) :
    Nat.Prime (gpf (a ^ 2 + a - 1)) :=
  (gpf_spec (extension7_polynomial_gt_one ha)).1

/-- `R_a` divides the collision polynomial. -/
theorem extension7_R_dvd_polynomial {a : ℕ} (ha : Nat.Prime a) :
    gpf (a ^ 2 + a - 1) ∣ a ^ 2 + a - 1 :=
  (gpf_spec (extension7_polynomial_gt_one ha)).2.1

/-- The greatest prime factor of `a^2+a-1` cannot divide `a+1`.
This is the report's observation that `T_a` is nonempty. -/
theorem extension7_R_not_dvd_anchor_succ {a : ℕ} (ha : Nat.Prime a) :
    ¬ gpf (a ^ 2 + a - 1) ∣ a + 1 := by
  intro hanchor
  let R := gpf (a ^ 2 + a - 1)
  have hRprime : Nat.Prime R := by
    dsimp [R]
    exact extension7_R_prime ha
  have hRpoly : R ∣ a ^ 2 + a - 1 := by
    dsimp [R]
    exact extension7_R_dvd_polynomial ha
  have hbase : 1 ≤ a ^ 2 + a := by
    have := ha.two_le
    nlinarith
  have hplus : (a ^ 2 + a - 1) + 1 = a * (a + 1) := by
    rw [Nat.sub_add_cancel hbase]
    ring
  have hRplus : R ∣ (a ^ 2 + a - 1) + 1 := by
    rw [hplus]
    exact dvd_mul_of_dvd_right hanchor a
  have hRone : R ∣ 1 := by
    have h := Nat.dvd_sub hRplus hRpoly
    simpa using h
  exact hRprime.not_dvd_one hRone

/-- Explicit nonemptiness of the prime set `T_a` from extension 7. -/
theorem extension7_support_nonempty {a : ℕ} (ha : Nat.Prime a) :
    ∃ l : ℕ,
      Nat.Prime l ∧
      l ≤ gpf (a ^ 2 + a - 1) ∧
      ¬ l ∣ a + 1 := by
  refine ⟨gpf (a ^ 2 + a - 1), extension7_R_prime ha, le_rfl, ?_⟩
  exact extension7_R_not_dvd_anchor_succ ha

/-- Every additive kernel occurring in an additive--multiplicative collision is
`R_a`-smooth, where `R_a = P⁺(a²+a-1)`. -/
theorem extension7_collision_add_kernel_smooth
    {a q : ℕ} (ha : Nat.Prime a) (hq : Nat.Prime q)
    (hcoll : add a q = mul a q) :
    Smooth (gpf (a ^ 2 + a - 1)) (a + q + 1) := by
  let r := add a q
  have hr : Nat.Prime r := by
    dsimp [r]
    exact (output_spec .add ha hq).1
  have hadd : r ∣ a + q + 1 := by
    dsimp [r]
    simpa [kernel] using (output_spec .add ha hq).2.1
  have hmul : r ∣ a * q + 1 := by
    dsimp [r]
    simpa [hcoll, kernel] using (output_spec .mul ha hq).2.1
  have hrpoly : r ∣ a ^ 2 + a - 1 :=
    collision_divisor hadd hmul
  have hrR : r ≤ gpf (a ^ 2 + a - 1) :=
    (gpf_spec (extension7_polynomial_gt_one ha)).2.2 r hr hrpoly
  constructor
  · have hgt := kernel_gt_one .add ha hq
    simpa [kernel] using (show 0 < kernel .add a q by omega)
  · intro s hs hsd
    have hsr : s ≤ r := by
      dsimp [r]
      apply (output_spec .add ha hq).2.2 s hs
      simpa [kernel] using hsd
    exact hsr.trans hrR

end PrimeGPF
