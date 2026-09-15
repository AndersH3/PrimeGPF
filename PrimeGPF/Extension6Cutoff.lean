import PrimeGPF.Extension6Asymptotic

/-!
# Extension 6: floor-cutoff arithmetic

These lemmas isolate the natural-number arithmetic of the cutoff
`(X + 1) / m - 1` appearing in the finite image bound.  They are independent
of the PNT beyond importing the scale-ratio theorem used later.
-/
namespace PrimeGPF
open Filter

/-- The natural cutoff occurring in the iterated exponential image bound. -/
def extension6Cutoff (m X : ℕ) : ℕ := (X + 1) / m - 1

/-- For fixed positive `m`, the cutoff tends to infinity with `X`. -/
theorem extension6Cutoff_tendsto_atTop (m : ℕ) (hm : 0 < m) :
    Tendsto (extension6Cutoff m) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop (m * (b + 1))] with X hX
  have hmul : m * (b + 1) ≤ X + 1 := hX.trans (Nat.le_succ X)
  have hdiv : b + 1 ≤ (X + 1) / m := by
    exact (Nat.le_div_iff_mul_le hm).2 (by simpa [Nat.mul_comm] using hmul)
  dsimp [extension6Cutoff]
  omega

/-- The scaled cutoff never exceeds the original cutoff variable. -/
theorem extension6Cutoff_mul_le (m X : ℕ) (hm : 0 < m) :
    m * extension6Cutoff m X ≤ X := by
  let q := (X + 1) / m
  have hqmul : m * q ≤ X + 1 := by
    dsimp [q]
    exact Nat.mul_div_le (X + 1) m
  dsimp [extension6Cutoff, q] at hqmul ⊢
  by_cases hq : (X + 1) / m = 0
  · simp [hq]
  · have hqpos : 0 < (X + 1) / m := Nat.pos_of_ne_zero hq
    have hqone : 1 ≤ (X + 1) / m := hqpos
    have hqsplit : ((X + 1) / m - 1) + 1 = (X + 1) / m :=
      Nat.sub_add_cancel hqone
    have hsum :
        m * ((X + 1) / m - 1) + m ≤ X + 1 := by
      calc
        m * ((X + 1) / m - 1) + m =
            m * (((X + 1) / m - 1) + 1) := by ring
        _ = m * ((X + 1) / m) := by rw [hqsplit]
        _ ≤ X + 1 := hqmul
    have hm1 : 1 ≤ m := hm
    have hplusone :
        m * ((X + 1) / m - 1) + 1 ≤ X + 1 := by
      exact (Nat.add_le_add_left hm1 _).trans hsum
    omega

end PrimeGPF
