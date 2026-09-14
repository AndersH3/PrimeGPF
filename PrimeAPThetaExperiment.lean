import PrimeAPExperiment
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open Filter Topology ArithmeticFunction

namespace PrimeGPF

/-- Finite summation-by-parts identity used in Kronecker's lemma. -/
lemma weighted_sum_eq_partial_sums (b : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (k : ℝ) * b k) =
      (n : ℝ) * (∑ k ∈ Finset.range n, b k) -
        ∑ k ∈ Finset.range n, ∑ i ∈ Finset.range (k + 1), b i := by
  let s : ℕ → ℝ := fun m ↦ ∑ i ∈ Finset.range m, b i
  change (∑ k ∈ Finset.range n, (k : ℝ) * b k) =
    (n : ℝ) * s n - ∑ k ∈ Finset.range n, s (k + 1)
  have hs (m : ℕ) : s (m + 1) = s m + b m := by
    simp [s, Finset.sum_range_succ]
  induction n with
  | zero => simp [s]
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hs n]
      push_cast
      ring

/--
Kronecker's lemma in the form needed here: if `b` is summable, then the
weighted partial sums `sum_{k<n} k*b k`, divided by `n`, tend to zero.
-/
theorem kronecker_weighted_of_summable (b : ℕ → ℝ) (hb : Summable b) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (k : ℝ) * b k)
      atTop (𝓝 0) := by
  let s : ℕ → ℝ := fun n ↦ ∑ k ∈ Finset.range n, b k
  have hs : Tendsto s atTop (𝓝 (∑' k, b k)) := by
    simpa [s] using hb.hasSum.tendsto_sum_nat
  have hs1 : Tendsto (fun n : ℕ ↦ s (n + 1)) atTop (𝓝 (∑' k, b k)) :=
    hs.comp (tendsto_add_atTop_nat 1)
  have hces :
      Tendsto
        (fun n : ℕ ↦ (n⁻¹ : ℝ) • ∑ k ∈ Finset.range n, s (k + 1))
        atTop (𝓝 (∑' k, b k)) :=
    hs1.cesaro_smul
  have hdiff :
      Tendsto
        (fun n : ℕ ↦ s n - (n⁻¹ : ℝ) • ∑ k ∈ Finset.range n, s (k + 1))
        atTop (𝓝 0) := by
    simpa using hs.sub hces
  apply hdiff.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0n : n ≠ 0 := by omega
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn0n
  rw [weighted_sum_eq_partial_sums b n]
  simp only [smul_eq_mul, s]
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
          ∑ n ∈ Finset.range N,
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
      (∑ n ∈ Finset.range N, (n : ℝ) * (A n / n)) =
        ∑ n ∈ Finset.range N, A n := by
    exact Finset.sum_congr rfl (fun n hn ↦ hterm n)
  simpa [A, hsum_eq] using hk

/--
After removing proper prime powers, Wiener--Ikehara gives the same asymptotic
for the prime part of the residue-class von Mangoldt sum.
-/
theorem prime_residueClass_sum_div_from_WienerIkehara
    (WIT : WienerIkeharaInput) {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) :
    Tendsto
      (fun N : ℕ ↦
        (N : ℝ)⁻¹ *
          ∑ n ∈ Finset.range N,
            (if n.Prime then vonMangoldt.residueClass a n else 0))
      atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  classical
  have hVM := vonMangoldt_AP_from_WienerIkehara WIT ha
  have hfull :
      Tendsto
        (fun N : ℕ ↦
          (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, vonMangoldt.residueClass a n)
        atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
    apply hVM.congr'
    filter_upwards with N
    have H :
        ((Finset.range N).filter (fun n : ℕ ↦ (n : ZMod q) = a)).sum Λ =
          ∑ n ∈ Finset.range N, vonMangoldt.residueClass a n := by
      exact (Finset.sum_indicator_eq_sum_filter _ _
        (fun _ ↦ {n : ℕ | (n : ZMod q) = a}) _).symm
    rw [H]
    ring
  have hnon := nonprime_residueClass_sum_div_tendsto_zero a
  have hsub := hfull.sub hnon
  simp only [sub_zero] at hsub
  apply hsub.congr'
  filter_upwards with N
  have hsplit :
      (∑ n ∈ Finset.range N, vonMangoldt.residueClass a n) =
        (∑ n ∈ Finset.range N,
          (if n.Prime then vonMangoldt.residueClass a n else 0)) +
        (∑ n ∈ Finset.range N,
          (if n.Prime then 0 else vonMangoldt.residueClass a n)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime <;> simp [hp]
  rw [hsplit]
  ring

/--
Prime-modulus version written as the usual logarithmically weighted prime sum.
-/
theorem primeLog_AP_prime_modulus_from_WienerIkehara
    (WIT : WienerIkeharaInput) {r c : ℕ}
    (hr : Nat.Prime r) (hc0 : 0 < c) (hcr : c < r) :
    Tendsto
      (fun N : ℕ ↦
        (N : ℝ)⁻¹ *
          ∑ n ∈ Finset.range N,
            (if n.Prime ∧ n % r = c then Real.log n else 0))
      atTop (𝓝 ((((r - 1 : ℕ) : ℝ))⁻¹)) := by
  letI : NeZero r := ⟨hr.ne_zero⟩
  have hcop : c.Coprime r :=
    (hr.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hc0 hcr)).symm
  have hunit : IsUnit (c : ZMod r) :=
    (ZMod.isUnit_iff_coprime c r).mpr hcop
  have h := prime_residueClass_sum_div_from_WienerIkehara WIT hunit
  rw [Nat.totient_prime hr] at h
  apply h.congr'
  filter_upwards with N
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hres : ((n : ZMod r) = (c : ZMod r)) ↔ n % r = c := by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hcr]
  by_cases hp : n.Prime
  · by_cases hnc : n % r = c
    · have hz : (n : ZMod r) = (c : ZMod r) := hres.mpr hnc
      simp [hp, hnc, vonMangoldt.residueClass, hz, vonMangoldt_apply_prime hp]
    · have hz : (n : ZMod r) ≠ (c : ZMod r) := fun hnc' => hnc (hres.mp hnc')
      simp [hp, hnc, vonMangoldt.residueClass, hz]
  · simp [hp]

/-- The complete logarithmically weighted prime-modulus AP layer. -/
def ThetaPrimeAPInput : Prop :=
  ∀ r c, Nat.Prime r → 0 < c → c < r →
    Tendsto
      (fun N : ℕ ↦
        (N : ℝ)⁻¹ *
          ∑ n ∈ Finset.range N,
            (if n.Prime ∧ n % r = c then Real.log n else 0))
      atTop (𝓝 ((((r - 1 : ℕ) : ℝ))⁻¹))

/-- Wiener--Ikehara discharges the complete logarithmically weighted AP layer. -/
theorem thetaPrimeAPInput_from_WienerIkehara
    (WIT : WienerIkeharaInput) : ThetaPrimeAPInput := by
  intro r c hr hc0 hcr
  exact primeLog_AP_prime_modulus_from_WienerIkehara WIT hr hc0 hcr

#check weighted_sum_eq_partial_sums
#check kronecker_weighted_of_summable
#check nonprime_residueClass_sum_div_tendsto_zero
#check prime_residueClass_sum_div_from_WienerIkehara
#check primeLog_AP_prime_modulus_from_WienerIkehara
#check ThetaPrimeAPInput
#check thetaPrimeAPInput_from_WienerIkehara
#print axioms kronecker_weighted_of_summable
#print axioms nonprime_residueClass_sum_div_tendsto_zero
#print axioms prime_residueClass_sum_div_from_WienerIkehara
#print axioms primeLog_AP_prime_modulus_from_WienerIkehara
#print axioms thetaPrimeAPInput_from_WienerIkehara

end PrimeGPF
