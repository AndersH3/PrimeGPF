import PrimeGPF.Progressions
import Mathlib.NumberTheory.LSeries.PrimesInAP

open Complex ArithmeticFunction Filter Topology
open scoped LSeries.notation

namespace PrimeGPF

/--
An abstract Wiener--Ikehara input, stated in exactly the form needed for
von Mangoldt functions in residue classes.  This isolates the Tauberian step
from the arithmetic-progression reductions in `PrimeGPF.Progressions`.
-/
def WienerIkeharaInput : Prop :=
  ∀ {f : ℕ → ℝ} {A : ℝ} {F : ℂ → ℂ},
    (∀ n, 0 ≤ f n) →
    Set.EqOn F (fun s ↦ L ↗f s - A / (s - 1)) {s | 1 < s.re} →
    ContinuousOn F {s | 1 ≤ s.re} →
    Tendsto (fun N : ℕ ↦ ((Finset.range N).sum f) / N) atTop (𝓝 A)

/--
The exact-v4.19 mathlib `PrimesInAP` API plus Wiener--Ikehara already gives
PNT-AP for the von Mangoldt weighted residue-class sum.  This is the first
analytic layer needed for `PrimeAPInput`.
-/
theorem vonMangoldt_AP_from_WienerIkehara
    (WIT : WienerIkeharaInput) {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) :
    Tendsto
      (fun N : ℕ ↦
        (((Finset.range N).filter (fun n : ℕ ↦ (n : ZMod q) = a)).sum Λ) / N)
      atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  classical
  have H N :
      ((Finset.range N).filter (fun n : ℕ ↦ (n : ZMod q) = a)).sum Λ =
        (Finset.range N).sum ({n : ℕ | (n : ZMod q) = a}.indicator Λ) :=
    (Finset.sum_indicator_eq_sum_filter _ _ (fun _ ↦ {n : ℕ | n = a}) _).symm
  simp only [H]
  refine WIT (F := vonMangoldt.LFunctionResidueClassAux a) (fun n ↦ ?_) ?_ ?_
  · exact Set.indicator_apply_nonneg fun _ ↦ vonMangoldt_nonneg
  · convert vonMangoldt.eqOn_LFunctionResidueClassAux ha with s
    push_cast
    rfl
  · exact vonMangoldt.continuousOn_LFunctionResidueClassAux a

#check WienerIkeharaInput
#check vonMangoldt_AP_from_WienerIkehara
#print axioms vonMangoldt_AP_from_WienerIkehara

end PrimeGPF
