import PrimeAPExperiment
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open Filter Topology ArithmeticFunction

namespace PrimeGPF

/-- Finite summation-by-parts identity used in Kronecker's lemma. -/
lemma weighted_sum_eq_partial_sums (b : ℕ → ℝ) (n : ℕ) :
    (∑ k in Finset.range n, (k : ℝ) * b k) =
      (n : ℝ) * (∑ k in Finset.range n, b k) -
        ∑ k in Finset.range n, ∑ i in Finset.range (k + 1), b i := by
  let s : ℕ → ℝ := fun m ↦ ∑ i in Finset.range m, b i
  change (∑ k in Finset.range n, (k : ℝ) * b k) =
    (n : ℝ) * s n - ∑ k in Finset.range n, s (k + 1)
  have hs (m : ℕ) : s (m + 1) = s m + b m := by
    simp [s, Finset.sum_range_succ]
  induction n with
  | zero => simp [s]
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hs n, hs n]
      push_cast
      ring

/--
Kronecker's lemma in the form needed here: if `b` is summable, then the
weighted partial sums `sum_{k<n} k*b k`, divided by `n`, tend to zero.
-/
theorem kronecker_weighted_of_summable (b : ℕ → ℝ) (hb : Summable b) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k in Finset.range n, (k : ℝ) * b k)
      atTop (𝓝 0) := by
  let s : ℕ → ℝ := fun n ↦ ∑ k in Finset.range n, b k
  have hs : Tendsto s atTop (𝓝 (∑' k, b k)) := by
    simpa [s] using hb.hasSum.tendsto_sum_nat
  have hs1 : Tendsto (fun n : ℕ ↦ s (n + 1)) atTop (𝓝 (∑' k, b k)) :=
    hs.comp (tendsto_add_atTop_nat 1)
  have hces :
      Tendsto
        (fun n : ℕ ↦ (n⁻¹ : ℝ) • ∑ k in Finset.range n, s (k + 1))
        atTop (𝓝 (∑' k, b k)) :=
    hs1.cesaro_smul
  have hdiff :
      Tendsto
        (fun n : ℕ ↦ s n - (n⁻¹ : ℝ) • ∑ k in Finset.range n, s (k + 1))
        atTop (𝓝 0) := by
    simpa using hs.sub hces
  apply hdiff.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0n : n ≠ 0 := by omega
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn0n
  rw [weighted_sum_eq_partial_sums b n]
  change
    (n : ℝ)⁻¹ * ((n : ℝ) * s n - ∑ k in Finset.range n, s (k + 1)) =
      s n - (n : ℝ)⁻¹ * ∑ k in Finset.range n, s (k + 1)
  field_simp [hn0]
  <;> ring

/--
The non-prime prime-power part of a residue-class von Mangoldt sum is `o(N)`.
The convergence input is already proved in pinned mathlib's `PrimesInAP` file.
-/
theorem nonprime_residueClass_sum_div_tendsto_zero
    {q : ℕ} (a : ZMod q) :
    Tendsto
      (fun N : ℕ ↦
        ((N : ℝ)⁻¹ *
          ∑ n in Finset.range N,
            (if n.Prime then 0 else vonMangoldt.residueClass a n)))
      atTop (𝓝 0) := by
  let A : ℕ → ℝ := fun n ↦ if n.Prime then 0 else vonMangoldt.residueClass a n
  have hsum : Summable (fun n : ℕ ↦ A n / n) := by
    simpa [A] using vonMangoldt.summable_residueClass_non_primes_div a
  have hk := kronecker_weighted_of_summable (fun n : ℕ ↦ A n / n) hsum
  have hterm (n : ℕ) : (n : ℝ) * (A n / n) = A n := by
    by_cases hn : n = 0
    · subst n
      simp [A]
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp [hn']
  have hsum_eq (N : ℕ) :
      (∑ n in Finset.range N, (n : ℝ) * (A n / n)) =
        ∑ n in Finset.range N, A n := by
    exact Finset.sum_congr rfl (fun n hn ↦ hterm n)
  simpa [A, hsum_eq] using hk

#check weighted_sum_eq_partial_sums
#check kronecker_weighted_of_summable
#check nonprime_residueClass_sum_div_tendsto_zero
#print axioms kronecker_weighted_of_summable
#print axioms nonprime_residueClass_sum_div_tendsto_zero

end PrimeGPF
