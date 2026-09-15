import PrimeGPF.Extension1Exponent
import PrimeGPF.Counting

/-!
# Extension 1: restricted-support exponent box

This is the non-sharp counting layer needed for the logarithm-saving exponent.
It retains the exact restricted prime support `T`, but uses the rectangular
exponent box rather than the sharp simplex-volume asymptotic.
-/
namespace PrimeGPF
open Claims

noncomputable def extension1RestrictedBoxBound (a r x : ℕ) : ℕ := by
  classical
  exact ∏ p ∈ extension1AllowedPrimes a r,
    (1 + ⌊Real.log (x : ℝ) / Real.log (p : ℝ)⌋₊)

/-- Restricted-smooth integers inject into their exponent vectors on the
allowed prime set. -/
theorem restrictedSmoothCount_le_extension1RestrictedBoxBound
    (a r x : ℕ) :
    restrictedSmoothCount a r x ≤ extension1RestrictedBoxBound a r x := by
  classical
  let S : Finset ℕ := extension1AllowedPrimes a r
  let A : Finset ℕ :=
    (Finset.range (x + 1)).filter (RestrictedSmooth a r)
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
            simp only [S, extension1AllowedPrimes, Finset.mem_filter,
              Finset.mem_range]
            exact ⟨by omega, hp, havoid⟩
          exact hpS this
        have hpnd : ¬ p ∣ n.1 := by
          intro hpd
          have hle := hnA.2.1.2 p hp hpd
          have havoid := hnA.2.2 p hp hpd
          have : p ∈ S := by
            simp only [S, extension1AllowedPrimes, Finset.mem_filter,
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
    restrictedSmoothCount a r x = A.card := by
      simp [restrictedSmoothCount, A]
    _ = I.card := hIcard.symm
    _ ≤ (S.pi T).card := Finset.card_le_card hI_subset
    _ = ∏ p ∈ S, (T p).card := Finset.card_pi S T
    _ = ∏ p ∈ S, (1 + E p) := by simp [T]
    _ = extension1RestrictedBoxBound a r x := by
      simp [extension1RestrictedBoxBound, S, E]

/-- The restricted exponent box has degree exactly the number of allowed
primes. -/
theorem extension1RestrictedBoxBound_real_le
    (a r x : ℕ) (hx : 2 ≤ x) :
    (extension1RestrictedBoxBound a r x : ℝ) ≤
      (2 / Real.log 2) ^ extension1AllowedPrimeCount a r *
        (Real.log (x : ℝ)) ^ extension1AllowedPrimeCount a r := by
  classical
  let S : Finset ℕ := extension1AllowedPrimes a r
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
    (extension1RestrictedBoxBound a r x : ℝ) =
        ∏ p ∈ S,
          (((1 + ⌊Real.log (x : ℝ) / Real.log (p : ℝ)⌋₊ : ℕ) : ℝ)) := by
      simp [extension1RestrictedBoxBound, S, Nat.cast_prod]
    _ ≤ ∏ p ∈ S, ((2 / Real.log 2) * Real.log (x : ℝ)) := hprod
    _ = (2 / Real.log 2) ^ extension1AllowedPrimeCount a r *
        (Real.log (x : ℝ)) ^ extension1AllowedPrimeCount a r := by
      simp [S, extension1AllowedPrimeCount, mul_pow]

/-- Non-sharp polylogarithmic bound for the exact restricted support. -/
theorem restrictedSmoothCount_real_le_polylog
    (a r x : ℕ) (hx : 2 ≤ x) :
    (restrictedSmoothCount a r x : ℝ) ≤
      (2 / Real.log 2) ^ extension1AllowedPrimeCount a r *
        (Real.log (x : ℝ)) ^ extension1AllowedPrimeCount a r := by
  have hcount :
      (restrictedSmoothCount a r x : ℝ) ≤
        (extension1RestrictedBoxBound a r x : ℝ) := by
    exact_mod_cast restrictedSmoothCount_le_extension1RestrictedBoxBound a r x
  exact hcount.trans (extension1RestrictedBoxBound_real_le a r x hx)

/-- End-to-end non-sharp form of extension 1: the additive fiber itself is
bounded by a degree-`|T|` polylogarithm, apart from the fixed low-input term
`π(r)`.  Together with `extension1_allowedPrimeCount_le_primeCount_sub_one`,
this is the formal logarithm saving claimed in the report; only the sharp
simplex coefficient remains to be formalized. -/
theorem extension1_fiberCount_real_le_polylog
    {a r X : ℕ} (ha : Nat.Prime a) (hr : Nat.Prime r)
    (hx : 2 ≤ X + a + 1) :
    (Claims.fiberCount .add a r X : ℝ) ≤
      (Claims.primeCount r : ℝ) +
      (2 / Real.log 2) ^ extension1AllowedPrimeCount a r *
        (Real.log ((X + a + 1 : ℕ) : ℝ)) ^ extension1AllowedPrimeCount a r := by
  have hfinite :
      (Claims.fiberCount .add a r X : ℝ) ≤
        (Claims.primeCount r : ℝ) +
          (restrictedSmoothCount a r (X + a + 1) : ℝ) := by
    exact_mod_cast
      extension1_fiberCount_le_primeCount_add_restrictedSmoothCount
        (X := X) ha hr
  have hsmooth := restrictedSmoothCount_real_le_polylog a r (X + a + 1) hx
  exact hfinite.trans (add_le_add_left hsmooth _)

/-- For the report's concrete example `a = r = 5`, the exact restricted
support is the singleton `{5}`. -/
lemma extension1AllowedPrimes_five_five :
    extension1AllowedPrimes 5 5 = ({5} : Finset ℕ) := by
  classical
  ext p
  simp only [extension1AllowedPrimes, Finset.mem_filter, Finset.mem_range,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hp6, hp, havoid⟩
    interval_cases p <;> norm_num at hp havoid ⊢
  · intro hp
    subst p
    norm_num

/-- Consequently the rectangular exponent bound is already sharp in dimension
one: it is exactly `1 + floor(log x / log 5)`. -/
theorem extension1RestrictedBoxBound_five_five (x : ℕ) :
    extension1RestrictedBoxBound 5 5 x =
      1 + ⌊Real.log (x : ℝ) / Real.log (5 : ℝ)⌋₊ := by
  classical
  simp [extension1RestrictedBoxBound, extension1AllowedPrimes_five_five]

/-- Finite explicit version of the report's example
`F⁺_{5,5}(X) ≤ log X / log 5 + O(1)`.  The fixed `π(5)` term accounts for the
small-input part of the general fiber decomposition. -/
theorem extension1_five_five_fiberCount_le_log_box (X : ℕ) :
    Claims.fiberCount .add 5 5 X ≤
      Claims.primeCount 5 +
        (1 + ⌊Real.log ((X + 5 + 1 : ℕ) : ℝ) / Real.log (5 : ℝ)⌋₊) := by
  have hfinite :=
    extension1_fiberCount_le_primeCount_add_restrictedSmoothCount
      (a := 5) (r := 5) (X := X) (by norm_num) (by norm_num)
  have hsmooth :=
    restrictedSmoothCount_le_extension1RestrictedBoxBound 5 5 (X + 5 + 1)
  calc
    Claims.fiberCount .add 5 5 X
        ≤ Claims.primeCount 5 + restrictedSmoothCount 5 5 (X + 5 + 1) := hfinite
    _ ≤ Claims.primeCount 5 + extension1RestrictedBoxBound 5 5 (X + 5 + 1) :=
      Nat.add_le_add_left hsmooth _
    _ = Claims.primeCount 5 +
        (1 + ⌊Real.log ((X + 5 + 1 : ℕ) : ℝ) / Real.log (5 : ℝ)⌋₊) := by
      rw [extension1RestrictedBoxBound_five_five]

end PrimeGPF
