import PrimeGPF.Progressions
import PrimeNumberTheoremAnd.Wiener
import Mathlib.NumberTheory.LSeries.PrimesInAP

namespace PrimeGPF

open Filter Topology
open ArithmeticFunction
open ArithmeticFunction.vonMangoldt
open Complex LSeries

/--
First analytic milestone toward `PrimeAPInput`: the von Mangoldt sum in a
reduced residue class has the expected main term.  This uses only the proved
Wiener--Ikehara theorem from the version-compatible PNT development and the
residue-class L-series facts already present in the pinned mathlib.
-/
theorem weakPNT_AP_vonMangoldt
    {q c : ℕ} (hq : 1 ≤ q) (hc : Nat.Coprime c q) (hclt : c < q) :
    Tendsto
      (fun N : ℕ =>
        cumsum
            (ArithmeticFunction.vonMangoldt.residueClass
              (q := q) (c : ZMod q)) N /
          (N : ℝ))
      atTop
      (nhds ((q.totient : ℝ)⁻¹)) := by
  letI : NeZero q := ⟨by omega⟩
  let z : ZMod q := (c : ZMod q)
  let f : ℕ → ℝ := ArithmeticFunction.vonMangoldt.residueClass z
  let F : ℂ → ℂ := ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux z

  have hz : IsUnit z := by
    dsimp [z]
    exact (ZMod.isUnit_iff_coprime c q).2 hc

  have hpos : 0 ≤ f := by
    intro n
    exact ArithmeticFunction.vonMangoldt.residueClass_nonneg z n

  have hf :
      ∀ σ : ℝ, 1 < σ →
        Summable (nterm (fun n => (f n : ℂ)) σ) := by
    intro σ hσ
    have hs : Summable (fun n : ℕ => f n / (n : ℝ) ^ σ) := by
      apply LSeries.summable_real_of_abscissaOfAbsConv_lt
      exact
        (ArithmeticFunction.vonMangoldt.abscissaOfAbsConv_residueClass_le_one z).trans_lt hσ
    convert hs using 1 with n
    by_cases hn : n = 0
    · subst n
      simp [nterm]
    · simp only [nterm, hn, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (hpos n)]

  have hcheby : cheby (fun n => (f n : ℂ)) := by
    obtain ⟨C, hC⟩ := vonMangoldt_cheby
    refine ⟨C, ?_⟩
    intro N
    unfold chebyWith at hC ⊢
    unfold cumsum at hC ⊢
    refine (Finset.sum_le_sum ?_).trans (hC N)
    intro n hn
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (hpos n), abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact ArithmeticFunction.vonMangoldt.residueClass_le z n

  have hcont : ContinuousOn F {s | 1 ≤ s.re} := by
    simpa [F] using
      (ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux z)

  have heq :
      Set.EqOn F
        (fun s =>
          LSeries (fun n => (f n : ℂ)) s -
            (((q.totient : ℝ)⁻¹ : ℝ) : ℂ) / (s - 1))
        {s | 1 < s.re} := by
    simpa [F, f] using
      (ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux hz)

  have h :=
    WienerIkeharaTheorem'
      (A := (q.totient : ℝ)⁻¹)
      (f := f)
      hpos hf hcheby hcont heq

  simpa [f, z] using h

#print axioms weakPNT_AP_vonMangoldt

end PrimeGPF
