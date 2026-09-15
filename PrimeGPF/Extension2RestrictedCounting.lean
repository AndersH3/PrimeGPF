import PrimeGPF.Extension2Support
import PrimeGPF.Counting

/-!
# Extension 2: restricted-support counting

This file proves the non-sharp polylogarithmic bound for a fixed
multiplicative fiber using exactly the report's support
`T = {p ≤ r : p prime, p ≠ a}`.  The later `1 / ζ(d)` improvement is a
primitive-exponent refinement of this counting layer.
-/
namespace PrimeGPF
open Claims

/-- Integers whose prime divisors are at most `r` and avoid the anchor prime
`a`. -/
def MulRestrictedSmooth (a r n : ℕ) : Prop :=
  Smooth r n ∧ ∀ s, Nat.Prime s → s ∣ n → s ≠ a

noncomputable def mulRestrictedSmoothCount (a r X : ℕ) : ℕ := by
  classical
  exact ((Finset.range (X + 1)).filter (MulRestrictedSmooth a r)).card

noncomputable def extension2AllowedPrimes (a r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (r + 1)).filter
    (fun p => Nat.Prime p ∧ p ≠ a)

noncomputable def extension2AllowedPrimeCount (a r : ℕ) : ℕ :=
  (extension2AllowedPrimes a r).card

noncomputable def extension2RestrictedBoxBound (a r x : ℕ) : ℕ := by
  classical
  exact ∏ p ∈ extension2AllowedPrimes a r,
    (1 + ⌊Real.log (x : ℝ) / Real.log (p : ℝ)⌋₊)

/-- Every multiplicative fiber input maps injectively to a kernel with exactly
the restricted support `T`. -/
theorem extension2_fiberCount_le_mulRestrictedSmoothCount
    {a r X : ℕ} (ha : Nat.Prime a) :
    Claims.fiberCount .mul a r X ≤
      mulRestrictedSmoothCount a r (a * X + 1) := by
  classical
  let F := (Finset.range (X + 1)).filter
    (fun q => Nat.Prime q ∧ mul a q = r)
  let B := (Finset.range (a * X + 2)).filter (MulRestrictedSmooth a r)
  let code : {q // q ∈ F} → ℕ := fun q => a * q.1 + 1

  have hcode_mem : ∀ q : {q // q ∈ F}, code q ∈ B := by
    intro q
    have hqF := Finset.mem_filter.mp q.property
    have hq : Nat.Prime q.1 := hqF.2.1
    have hout : mul a q.1 = r := hqF.2.2
    have hqx : q.1 ≤ X := by
      have := Finset.mem_range.mp hqF.1
      omega
    have hsmooth : Smooth r (a * q.1 + 1) := by
      constructor
      · have hgt := kernel_gt_one .mul ha hq
        simpa [kernel] using (show 0 < kernel .mul a q.1 by omega)
      · intro s hs hsd
        exact (extension2_mul_kernel_support_exclusion ha hq hout hs hsd).1
    have hrestricted : MulRestrictedSmooth a r (a * q.1 + 1) := by
      refine ⟨hsmooth, ?_⟩
      intro s hs hsd
      exact (extension2_mul_kernel_support_exclusion ha hq hout hs hsd).2
    apply Finset.mem_filter.mpr
    refine ⟨?_, hrestricted⟩
    apply Finset.mem_range.mpr
    dsimp [code]
    have hle : a * q.1 + 1 ≤ a * X + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left a hqx) 1
    omega

  have hcode_inj : Function.Injective code := by
    intro q₁ q₂ h
    apply Subtype.ext
    dsimp [code] at h
    have hmul : a * q₁.1 = a * q₂.1 := Nat.add_right_cancel h
    exact Nat.eq_of_mul_eq_mul_left ha.pos hmul

  let I : Finset ℕ := F.attach.image code
  have hI_subset : I ⊆ B := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨q, hq, rfl⟩
    exact hcode_mem q
  have hIcard : I.card = F.card := by
    dsimp [I]
    rw [Finset.card_image_of_injective _ hcode_inj]
    simp

  have hF : Claims.fiberCount .mul a r X = F.card := by
    simp [Claims.fiberCount, F]

  calc
    Claims.fiberCount .mul a r X = F.card := hF
    _ = I.card := hIcard.symm
    _ ≤ B.card := Finset.card_le_card hI_subset
    _ = mulRestrictedSmoothCount a r (a * X + 1) := by
      simp [mulRestrictedSmoothCount, B]

/-- Restricted-smooth multiplicative kernels inject into their exponent vectors
on the allowed prime set. -/
theorem mulRestrictedSmoothCount_le_extension2RestrictedBoxBound
    (a r x : ℕ) :
    mulRestrictedSmoothCount a r x ≤ extension2RestrictedBoxBound a r x := by
  classical
  let S : Finset ℕ := extension2AllowedPrimes a r
  let A : Finset ℕ :=
    (Finset.range (x + 1)).filter (MulRestrictedSmooth a r)
  let E : ℕ → ℕ := fun p =>
    ⌊Real.log (x : ℝ) / Real.log (p : ℝ)⌋₊
  let T : ℕ → Finset ℕ := fun p => Finset.range (1 + E p)
  let code : {n // n ∈ A} → (∀ p ∈ S, ℕ) :=
    fun n p _ => n.1.factorization p

  have hcode_mem : ∀ n : {n // n ∈ A}, code n ∈ S.pi T := by
    intro n
    apply Finset.mem_pi.mpr
    intro p hpS
    have hpS' := Finset.mem_filter.mp hpS
    have hp : Nat.Prime p := hpS'.2.1
    have hnA := Finset.mem_filter.mp n.property
    have hnx : n.1 ≤ x := by
      have := Finset.mem_range.mp hnA.1
      omega
    have hnpos : 0 < n.1 := hnA.2.1.1
    have he : n.1.factorization p ≤ E p := by
      dsimp [E]
      exact factorization_le_boxExponent hp hnpos hnx
    simp only [T, Finset.mem_range]
    change n.1.factorization p < 1 + E p
    omega

  have hcode_inj : Function.Injective code := by
    intro m n hmn
    apply Subtype.ext
    have hmA := Finset.mem_filter.mp m.property
    have hnA := Finset.mem_filter.mp n.property
    have hm0 : m.1 ≠ 0 := Nat.ne_of_gt hmA.2.1.1
    have hn0 : n.1 ≠ 0 := Nat.ne_of_gt hnA.2.1.1
    apply Nat.factorization_inj hm0 hn0
    ext p
    by_cases hp : Nat.Prime p
    · by_cases hpS : p ∈ S
      · exact congrFun (congrFun hmn p) hpS
      · have hpmd : ¬ p ∣ m.1 := by
          intro hpd
          have hle := hmA.2.1.2 p hp hpd
          have havoid := hmA.2.2 p hp hpd
          have : p ∈ S := by
            simp only [S, extension2AllowedPrimes, Finset.mem_filter,
              Finset.mem_range]
            exact ⟨by omega, hp, havoid⟩
          exact hpS this
        have hpnd : ¬ p ∣ n.1 := by
          intro hpd
          have hle := hnA.2.1.2 p hp hpd
          have havoid := hnA.2.2 p hp hpd
          have : p ∈ S := by
            simp only [S, extension2AllowedPrimes, Finset.mem_filter,
              Finset.mem_range]
            exact ⟨by omega, hp, havoid⟩
          exact hpS this
        rw [Nat.factorization_eq_zero_of_not_dvd hpmd,
            Nat.factorization_eq_zero_of_not_dvd hpnd]
    · rw [Nat.factorization_eq_zero_of_non_prime _ hp,
          Nat.factorization_eq_zero_of_non_prime _ hp]

  let I : Finset (∀ p ∈ S, ℕ) := A.attach.image code
  have hI_subset : I ⊆ S.pi T := by
    intro f hf
    rcases Finset.mem_image.mp hf with ⟨n, hn, rfl⟩
    exact hcode_mem n
  have hIcard : I.card = A.card := by
    dsimp [I]
    rw [Finset.card_image_of_injective _ hcode_inj]
    simp

  calc
    mulRestrictedSmoothCount a r x = A.card := by
      simp [mulRestrictedSmoothCount, A]
    _ = I.card := hIcard.symm
    _ ≤ (S.pi T).card := Finset.card_le_card hI_subset
    _ = ∏ p ∈ S, (T p).card := Finset.card_pi S T
    _ = ∏ p ∈ S, (1 + E p) := by simp [T]
    _ = extension2RestrictedBoxBound a r x := by
      simp [extension2RestrictedBoxBound, S, E]

/-- The extension-2 exponent box has degree exactly `d=|T|`. -/
theorem extension2RestrictedBoxBound_real_le
    (a r x : ℕ) (hx : 2 ≤ x) :
    (extension2RestrictedBoxBound a r x : ℝ) ≤
      (2 / Real.log 2) ^ extension2AllowedPrimeCount a r *
        (Real.log (x : ℝ)) ^ extension2AllowedPrimeCount a r := by
  classical
  let S : Finset ℕ := extension2AllowedPrimes a r
  have hprod :
      (∏ p ∈ S,
        (((1 + ⌊Real.log (x : ℝ) / Real.log (p : ℝ)⌋₊ : ℕ) : ℝ))) ≤
      ∏ p ∈ S, ((2 / Real.log 2) * Real.log (x : ℝ)) := by
    apply Finset.prod_le_prod
    · intro p hpS
      positivity
    · intro p hpS
      have hp : Nat.Prime p := by
        have hp' := Finset.mem_filter.mp hpS
        exact hp'.2.1
      exact smoothBox_factor_real_le hp hx
  calc
    (extension2RestrictedBoxBound a r x : ℝ) =
        ∏ p ∈ S,
          (((1 + ⌊Real.log (x : ℝ) / Real.log (p : ℝ)⌋₊ : ℕ) : ℝ)) := by
      simp [extension2RestrictedBoxBound, S, Nat.cast_prod]
    _ ≤ ∏ p ∈ S, ((2 / Real.log 2) * Real.log (x : ℝ)) := hprod
    _ = (2 / Real.log 2) ^ extension2AllowedPrimeCount a r *
        (Real.log (x : ℝ)) ^ extension2AllowedPrimeCount a r := by
      simp [S, extension2AllowedPrimeCount, mul_pow]

/-- Non-sharp fixed-fiber estimate with the exact exponent `d=|T|`. -/
theorem extension2_fiberCount_real_le_polylog
    {a r X : ℕ} (ha : Nat.Prime a) (hx : 2 ≤ a * X + 1) :
    (Claims.fiberCount .mul a r X : ℝ) ≤
      (2 / Real.log 2) ^ extension2AllowedPrimeCount a r *
        (Real.log ((a * X + 1 : ℕ) : ℝ)) ^ extension2AllowedPrimeCount a r := by
  have hfinite :
      (Claims.fiberCount .mul a r X : ℝ) ≤
        (mulRestrictedSmoothCount a r (a * X + 1) : ℝ) := by
    exact_mod_cast extension2_fiberCount_le_mulRestrictedSmoothCount
      (r := r) (X := X) ha
  have hbox :
      (mulRestrictedSmoothCount a r (a * X + 1) : ℝ) ≤
        (extension2RestrictedBoxBound a r (a * X + 1) : ℝ) := by
    exact_mod_cast
      mulRestrictedSmoothCount_le_extension2RestrictedBoxBound
        a r (a * X + 1)
  exact hfinite.trans (hbox.trans
    (extension2RestrictedBoxBound_real_le a r (a * X + 1) hx))

end PrimeGPF
