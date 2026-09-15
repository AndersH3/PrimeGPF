import PrimeGPF.Extension34CandidatePairs
import PrimeGPF.WeightedTriangleArea

/-!
# Extensions 3 and 4: parity-scaled weighted triangles

Before imposing coprimality, the parity conditions already shrink the relevant
lattice triangles.  For Extension 3, writing the odd first exponent as
`α = 2k+1` doubles its weight.  For Extension 4, both exponents are odd, so
both weights double.  These reductions isolate the easy parity density factors
before the later Möbius/primitivity argument.
-/
namespace PrimeGPF

open PrimeGPF.Analytic

/-- The Extension-3 candidate pairs inject into the parity-scaled triangle
with weights `(2 log 3, log 5)` and cutoff `log(2X+1)-log 3`. -/
theorem extension3_candidatePairs_card_le_parityTriangle (X : ℕ) :
    (extension3CandidatePairs X).card ≤
      (weightedTriangle (2 * Real.log 3) (Real.log 5)
        (Real.log ((2 * X + 1 : ℕ) : ℝ) - Real.log 3)).card := by
  classical
  let S := extension3CandidatePairs X
  let T := weightedTriangle (2 * Real.log 3) (Real.log 5)
    (Real.log ((2 * X + 1 : ℕ) : ℝ) - Real.log 3)
  let f : ℕ × ℕ → ℕ × ℕ := fun e => (e.1 / 2, e.2)
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hlog5 : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  have hinj : Set.InjOn f (S : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    have hxmem := (mem_extension3CandidatePairs_iff X x.1 x.2).1 hx
    have hymem := (mem_extension3CandidatePairs_iff X y.1 y.2).1 hy
    have hxdec := Nat.mod_add_div x.1 2
    have hydec := Nat.mod_add_div y.1 2
    have hxfst : x.1 / 2 = y.1 / 2 := congrArg Prod.fst hxy
    have hxsnd : x.2 = y.2 := congrArg Prod.snd hxy
    apply Prod.ext
    · omega
    · exact hxsnd
  have himage : S.image f ⊆ T := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨e, heS, rfl⟩
    have he := (mem_extension3CandidatePairs_iff X e.1 e.2).1 heS
    rcases he with ⟨hα, hβ, hodd, hcop, hweighted⟩
    have hdec := Nat.mod_add_div e.1 2
    have hform : e.1 = 2 * (e.1 / 2) + 1 := by omega
    have htarget :
        ((e.1 / 2 : ℕ) : ℝ) * (2 * Real.log 3) +
            (e.2 : ℝ) * Real.log 5 ≤
          Real.log ((2 * X + 1 : ℕ) : ℝ) - Real.log 3 := by
      rw [hform] at hweighted
      push_cast at hweighted
      linarith
    have hcut :
        0 ≤ Real.log ((2 * X + 1 : ℕ) : ℝ) - Real.log 3 := by
      have hleft :
          0 ≤ ((e.1 / 2 : ℕ) : ℝ) * (2 * Real.log 3) +
            (e.2 : ℝ) * Real.log 5 := by positivity
      linarith
    exact (mem_weightedTriangle_iff (by positivity) hlog5 hcut _ _).2 htarget
  have hcardImage : (S.image f).card = S.card :=
    Finset.card_image_of_injOn hinj
  rw [← hcardImage]
  exact Finset.card_le_card himage

/-- The Extension-4 candidate pairs inject into the parity-scaled triangle
with weights `(2 log 2, 2 log 5)` and cutoff `log(3X+1)-log 2-log 5`. -/
theorem extension4_candidatePairs_card_le_parityTriangle (X : ℕ) :
    (extension4CandidatePairs X).card ≤
      (weightedTriangle (2 * Real.log 2) (2 * Real.log 5)
        (Real.log ((3 * X + 1 : ℕ) : ℝ) - Real.log 2 - Real.log 5)).card := by
  classical
  let S := extension4CandidatePairs X
  let T := weightedTriangle (2 * Real.log 2) (2 * Real.log 5)
    (Real.log ((3 * X + 1 : ℕ) : ℝ) - Real.log 2 - Real.log 5)
  let f : ℕ × ℕ → ℕ × ℕ := fun e => (e.1 / 2, e.2 / 2)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog5 : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  have hinj : Set.InjOn f (S : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    have hxmem := (mem_extension4CandidatePairs_iff X x.1 x.2).1 hx
    have hymem := (mem_extension4CandidatePairs_iff X y.1 y.2).1 hy
    have hxdec1 := Nat.mod_add_div x.1 2
    have hydec1 := Nat.mod_add_div y.1 2
    have hxdec2 := Nat.mod_add_div x.2 2
    have hydec2 := Nat.mod_add_div y.2 2
    have hfst : x.1 / 2 = y.1 / 2 := congrArg Prod.fst hxy
    have hsnd : x.2 / 2 = y.2 / 2 := congrArg Prod.snd hxy
    apply Prod.ext <;> omega
  have himage : S.image f ⊆ T := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨e, heS, rfl⟩
    have he := (mem_extension4CandidatePairs_iff X e.1 e.2).1 heS
    rcases he with ⟨hα, hβ, hαodd, hβodd, hcop, hweighted⟩
    have hdec1 := Nat.mod_add_div e.1 2
    have hdec2 := Nat.mod_add_div e.2 2
    have hform1 : e.1 = 2 * (e.1 / 2) + 1 := by omega
    have hform2 : e.2 = 2 * (e.2 / 2) + 1 := by omega
    have htarget :
        ((e.1 / 2 : ℕ) : ℝ) * (2 * Real.log 2) +
            ((e.2 / 2 : ℕ) : ℝ) * (2 * Real.log 5) ≤
          Real.log ((3 * X + 1 : ℕ) : ℝ) - Real.log 2 - Real.log 5 := by
      rw [hform1, hform2] at hweighted
      push_cast at hweighted
      linarith
    have hcut :
        0 ≤ Real.log ((3 * X + 1 : ℕ) : ℝ) - Real.log 2 - Real.log 5 := by
      have hleft :
          0 ≤ ((e.1 / 2 : ℕ) : ℝ) * (2 * Real.log 2) +
            ((e.2 / 2 : ℕ) : ℝ) * (2 * Real.log 5) := by positivity
      linarith
    exact (mem_weightedTriangle_iff (by positivity) (by positivity) hcut _ _).2 htarget
  have hcardImage : (S.image f).card = S.card :=
    Finset.card_image_of_injOn hinj
  rw [← hcardImage]
  exact Finset.card_le_card himage

end PrimeGPF
