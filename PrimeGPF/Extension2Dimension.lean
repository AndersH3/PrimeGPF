import PrimeGPF.Extension2RestrictedCounting

/-!
# Extension 2: exact support dimension

The support `T = {p ≤ r : p prime, p ≠ a}` has one fewer element than the
full prime set precisely when the prime anchor itself lies below the cutoff.
-/
namespace PrimeGPF
open Claims

/-- Exact cardinality of the prime support used in extension 2. -/
theorem extension2_allowedPrimeCount_eq
    {a r : ℕ} (ha : Nat.Prime a) :
    extension2AllowedPrimeCount a r =
      if a ≤ r then Claims.primeCount r - 1 else Claims.primeCount r := by
  classical
  let U := (Finset.range (r + 1)).filter Nat.Prime
  have hUcard : U.card = Claims.primeCount r := by
    simp [U, Claims.primeCount]
  by_cases har : a ≤ r
  · have har' : a < r + 1 := by omega
    have haU : a ∈ U := by
      simp [U, ha, har']
    have hset : extension2AllowedPrimes a r = U.erase a := by
      ext p
      simp only [extension2AllowedPrimes, U, Finset.mem_filter,
        Finset.mem_range, Finset.mem_erase]
      constructor
      · rintro ⟨hpr, hp, hpa⟩
        exact ⟨hpa, hpr, hp⟩
      · rintro ⟨hpa, hpr, hp⟩
        exact ⟨hpr, hp, hpa⟩
    rw [extension2AllowedPrimeCount, hset, Finset.card_erase_of_mem haU,
      hUcard]
    simp [har]
  · have hset : extension2AllowedPrimes a r = U := by
      ext p
      simp only [extension2AllowedPrimes, U, Finset.mem_filter,
        Finset.mem_range]
      constructor
      · rintro ⟨hpr, hp, _⟩
        exact ⟨hpr, hp⟩
      · rintro ⟨hpr, hp⟩
        refine ⟨hpr, hp, ?_⟩
        intro hpa
        subst p
        exact har (by omega)
    rw [extension2AllowedPrimeCount, hset, hUcard]
    simp [har]

/-- In particular, if the anchor lies in the output range, the support degree
is exactly `π(r)-1`. -/
theorem extension2_allowedPrimeCount_eq_primeCount_sub_one
    {a r : ℕ} (ha : Nat.Prime a) (har : a ≤ r) :
    extension2AllowedPrimeCount a r = Claims.primeCount r - 1 := by
  rw [extension2_allowedPrimeCount_eq ha]
  simp [har]

end PrimeGPF
