import PrimeGPF.Progressions
import Mathlib.NumberTheory.LSeries.PrimesInAP

open Complex ArithmeticFunction Filter Topology
open scoped LSeries.notation

namespace PrimeGPF

/--
An abstract Wiener--Ikehara input, stated in exactly the form needed for
von Mangoldt functions in residue classes. This isolates the Tauberian step
from the arithmetic-progression reductions in `PrimeGPF.Progressions`.
-/
def WienerIkeharaInput : Prop :=
  ∀ {f : ℕ → ℝ} {A : ℝ} {F : ℂ → ℂ},
    (∀ n, 0 ≤ f n) →
    Set.EqOn F (fun s ↦ L ↗f s - A / (s - 1)) {s | 1 < s.re} →
    ContinuousOn F {s | 1 ≤ s.re} →
    Tendsto (fun N : ℕ ↦ ((Finset.range N).sum f) / N) atTop (𝓝 A)

/--
The pinned-v4.19 mathlib `PrimesInAP` API plus Wiener--Ikehara already gives
PNT-AP for the von Mangoldt weighted residue-class sum. This is the first
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

/--
Prime-modulus/natural-residue specialization of the previous theorem.  This
matches the arithmetic data used by `PrimeAPInput` up to the still-missing
steps that remove prime powers and unweight the prime sum.
-/
theorem vonMangoldt_AP_prime_modulus_from_WienerIkehara
    (WIT : WienerIkeharaInput) {r c : ℕ}
    (hr : Nat.Prime r) (hc0 : 0 < c) (hcr : c < r) :
    Tendsto
      (fun N : ℕ ↦
        (((Finset.range N).filter (fun n : ℕ ↦ n % r = c)).sum Λ) / N)
      atTop (𝓝 ((((r - 1 : ℕ) : ℝ))⁻¹)) := by
  letI : NeZero r := ⟨hr.ne_zero⟩
  have hcop : c.Coprime r :=
    (hr.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hc0 hcr)).symm
  have hunit : IsUnit (c : ZMod r) :=
    (ZMod.isUnit_iff_coprime c r).mpr hcop
  have h := vonMangoldt_AP_from_WienerIkehara WIT hunit
  have hfilter (N : ℕ) :
      (Finset.range N).filter (fun n : ℕ ↦ (n : ZMod r) = (c : ZMod r)) =
        (Finset.range N).filter (fun n : ℕ ↦ n % r = c) := by
    apply Finset.filter_congr
    intro n hn
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hcr]
  simpa [hfilter, Nat.totient_prime hr] using h

/-- The complete von-Mangoldt-weighted prime-modulus AP layer. -/
def VonMangoldtPrimeAPInput : Prop :=
  ∀ r c, Nat.Prime r → 0 < c → c < r →
    Tendsto
      (fun N : ℕ ↦
        (((Finset.range N).filter (fun n : ℕ ↦ n % r = c)).sum Λ) / N)
      atTop (𝓝 ((((r - 1 : ℕ) : ℝ))⁻¹))

/-- Wiener--Ikehara discharges the complete von-Mangoldt AP layer. -/
theorem vonMangoldtPrimeAPInput_from_WienerIkehara
    (WIT : WienerIkeharaInput) : VonMangoldtPrimeAPInput := by
  intro r c hr hc0 hcr
  exact vonMangoldt_AP_prime_modulus_from_WienerIkehara WIT hr hc0 hcr

#check WienerIkeharaInput
#check vonMangoldt_AP_from_WienerIkehara
#check vonMangoldt_AP_prime_modulus_from_WienerIkehara
#check VonMangoldtPrimeAPInput
#check vonMangoldtPrimeAPInput_from_WienerIkehara
#print axioms vonMangoldt_AP_from_WienerIkehara
#print axioms vonMangoldt_AP_prime_modulus_from_WienerIkehara
#print axioms vonMangoldtPrimeAPInput_from_WienerIkehara

end PrimeGPF
