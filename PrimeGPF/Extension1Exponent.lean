import PrimeGPF.Extension1Finite

/-!
# Extension 1: support-dimension saving

The allowed prime support excludes at least one prime whenever the output prime
is at least three.  This is the exact finite combinatorial statement behind the
exponent `π(r)-1` in the report.
-/
namespace PrimeGPF
open Claims

noncomputable def extension1AllowedPrimes (a r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (r + 1)).filter
    (fun p => Nat.Prime p ∧ ¬ p ∣ a + 1)

noncomputable def extension1AllowedPrimeCount (a r : ℕ) : ℕ :=
  (extension1AllowedPrimes a r).card

/-- The restricted support is contained in the full set of primes up to `r`. -/
theorem extension1AllowedPrimes_subset_all (a r : ℕ) :
    extension1AllowedPrimes a r ⊆
      (Finset.range (r + 1)).filter Nat.Prime := by
  classical
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hp'.1, hp'.2.1⟩

/-- At an output prime `r ≠ 2`, at least one prime up to `r` is excluded from
`T`: `2` when the anchor is odd, and `3` when the anchor is `2`. -/
theorem extension1_exists_excluded_prime
    {a r : ℕ} (ha : Nat.Prime a) (hr : Nat.Prime r) (hr2 : r ≠ 2) :
    ∃ p,
      p ∈ (Finset.range (r + 1)).filter Nat.Prime ∧
      p ∉ extension1AllowedPrimes a r := by
  classical
  rcases ha.eq_two_or_odd with ha2 | haodd
  · subst a
    refine ⟨3, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, Nat.prime_three⟩
      have hr3 : 3 ≤ r := by
        have := hr.two_le
        omega
      omega
    · simp [extension1AllowedPrimes]
  · refine ⟨2, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by have := hr.two_le; omega), Nat.prime_two⟩
    · have h2dvd : 2 ∣ a + 1 := by
        exact Nat.dvd_of_mod_eq_zero (by
          have hmod : a % 2 = 1 := haodd
          omega)
      simp [extension1AllowedPrimes, h2dvd]

/-- The allowed-support dimension is strictly smaller than the full prime count. -/
theorem extension1_allowedPrimeCount_lt_primeCount
    {a r : ℕ} (ha : Nat.Prime a) (hr : Nat.Prime r) (hr2 : r ≠ 2) :
    extension1AllowedPrimeCount a r < Claims.primeCount r := by
  classical
  let U := (Finset.range (r + 1)).filter Nat.Prime
  have hsub : extension1AllowedPrimes a r ⊆ U :=
    extension1AllowedPrimes_subset_all a r
  obtain ⟨p, hpU, hpnot⟩ := extension1_exists_excluded_prime ha hr hr2
  have hproper : extension1AllowedPrimes a r ⊂ U := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
    intro heq
    have : p ∈ extension1AllowedPrimes a r := by
      rw [heq]
      exact hpU
    exact hpnot this
  have hcard := Finset.card_lt_card hproper
  simpa [extension1AllowedPrimeCount, Claims.primeCount, U] using hcard

/-- In the report's natural-number form, the support dimension is at most
`π(r)-1`. -/
theorem extension1_allowedPrimeCount_le_primeCount_sub_one
    {a r : ℕ} (ha : Nat.Prime a) (hr : Nat.Prime r) (hr2 : r ≠ 2) :
    extension1AllowedPrimeCount a r ≤ Claims.primeCount r - 1 := by
  have h := extension1_allowedPrimeCount_lt_primeCount ha hr hr2
  omega

end PrimeGPF
