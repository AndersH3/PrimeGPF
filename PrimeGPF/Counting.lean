import PrimeGPF.Statements
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Pi

set_option autoImplicit false

namespace PrimeGPF

/-- A prime exponent in n is at most log_p x whenever 0 < n ≤ x. -/
theorem factorization_le_natLog
    {n p x : ℕ}
    (hp : Nat.Prime p)
    (hn : 0 < n)
    (hnx : n ≤ x) :
    n.factorization p ≤ Nat.log p x := by
  apply Nat.le_log_of_pow_le hp.one_lt
  exact
    (Nat.le_of_dvd hn (Nat.ordProj_dvd n p)).trans hnx

/-- The exponent bound in the exact form occurring in smoothBoxBound. -/
theorem factorization_le_boxExponent
    {n p x : ℕ}
    (hp : Nat.Prime p)
    (hn : 0 < n)
    (hnx : n ≤ x) :
    n.factorization p ≤
      ⌊Real.log (x : ℝ) / Real.log (p : ℝ)⌋₊ := by
  have h := factorization_le_natLog hp hn hnx
  rw [← Real.natFloor_logb_natCast p x] at h
  simpa [Real.logb] using h

/--
The explicit exponent-vector bound appearing in the second clause of theorem 6.2.
-/
theorem smoothCount_le_smoothBoxBound
    (r x : ℕ) :
    Claims.smoothCount r x ≤ Claims.smoothBoxBound r x := by
  classical

  let S : Finset ℕ :=
    (Finset.range (r + 1)).filter Nat.Prime

  let A : Finset ℕ :=
    (Finset.range (x + 1)).filter (Smooth r)

  let E : ℕ → ℕ :=
    fun p =>
      ⌊Real.log (x : ℝ) / Real.log (p : ℝ)⌋₊

  let T : ℕ → Finset ℕ :=
    fun p => Finset.range (1 + E p)

  let code : {n // n ∈ A} → (∀ p ∈ S, ℕ) :=
    fun n p _ => n.1.factorization p

  have hcode_mem :
      ∀ n : {n // n ∈ A}, code n ∈ S.pi T := by
    intro n
    apply Finset.mem_pi.mpr
    intro p hpS

    have hpS' := Finset.mem_filter.mp hpS
    have hp : Nat.Prime p := hpS'.2

    have hnA := Finset.mem_filter.mp n.property
    have hnxlt : n.1 < x + 1 :=
      Finset.mem_range.mp hnA.1
    have hnx : n.1 ≤ x := by
      omega
    have hnpos : 0 < n.1 :=
      hnA.2.1

    have he :
        n.1.factorization p ≤ E p := by
      dsimp [E]
      exact factorization_le_boxExponent hp hnpos hnx

    simp only [T, Finset.mem_range]
    change n.1.factorization p < 1 + E p
    omega

  have hcode_inj : Function.Injective code := by
    intro a b hab
    apply Subtype.ext

    have haA := Finset.mem_filter.mp a.property
    have hbA := Finset.mem_filter.mp b.property

    have ha0 : a.1 ≠ 0 :=
      Nat.ne_of_gt haA.2.1
    have hb0 : b.1 ≠ 0 :=
      Nat.ne_of_gt hbA.2.1

    apply Nat.factorization_inj ha0 hb0

    ext p

    by_cases hp : Nat.Prime p
    · by_cases hpr : p ≤ r
      · have hpS : p ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hp⟩

        exact congrFun (congrFun hab p) hpS

      · have hpa : ¬ p ∣ a.1 := by
          intro hpd
          exact hpr (haA.2.2 p hp hpd)

        have hpb : ¬ p ∣ b.1 := by
          intro hpd
          exact hpr (hbA.2.2 p hp hpd)

        rw [Nat.factorization_eq_zero_of_not_dvd hpa,
            Nat.factorization_eq_zero_of_not_dvd hpb]

    · rw [Nat.factorization_eq_zero_of_non_prime _ hp,
          Nat.factorization_eq_zero_of_non_prime _ hp]

  let I : Finset (∀ p ∈ S, ℕ) :=
    A.attach.image code

  have hI_subset : I ⊆ S.pi T := by
    intro f hf
    rcases Finset.mem_image.mp hf with ⟨n, hn, rfl⟩
    exact hcode_mem n

  have hIcard : I.card = A.card := by
    dsimp [I]
    rw [Finset.card_image_of_injective _ hcode_inj]
    simp

  calc
    Claims.smoothCount r x
        = A.card := by
            simp [Claims.smoothCount, A]

    _ = I.card := hIcard.symm

    _ ≤ (S.pi T).card :=
      Finset.card_le_card hI_subset

    _ = ∏ p ∈ S, (T p).card := by
      exact Finset.card_pi S T

    _ = ∏ p ∈ S, (1 + E p) := by
      simp [T]

    _ = Claims.smoothBoxBound r x := by
      simp [Claims.smoothBoxBound, S, E]


/--
Each individual exponent-box factor is at most
`(2 / log 2) * log x` once `x ≥ 2`.
-/
theorem smoothBox_factor_real_le
    {p x : ℕ}
    (hp : Nat.Prime p)
    (hx : 2 ≤ x) :
    (((1 + ⌊Real.log (x : ℝ) / Real.log (p : ℝ)⌋₊ : ℕ) : ℝ))
      ≤ (2 / Real.log 2) * Real.log (x : ℝ) := by

  have hlog2 : 0 < Real.log (2 : ℝ) := by
    exact Real.log_pos (by norm_num)

  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : 1 < p := hp.one_lt
  have hx1 : 1 < x := by omega

  have hlogp : 0 < Real.log (p : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hp1)

  have hlogx : 0 < Real.log (x : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hx1)

  have h2p :
      Real.log (2 : ℝ) ≤ Real.log (p : ℝ) := by
    apply Real.log_le_log
    · norm_num
    · exact_mod_cast hp2

  have h2x :
      Real.log (2 : ℝ) ≤ Real.log (x : ℝ) := by
    apply Real.log_le_log
    · norm_num
    · exact_mod_cast hx

  let y : ℝ :=
    Real.log (x : ℝ) / Real.log (p : ℝ)

  have hy0 : 0 ≤ y := by
    dsimp [y]
    positivity

  have hfloor :
      ((⌊y⌋₊ : ℕ) : ℝ) ≤ y := by
    exact (Nat.le_floor_iff hy0).1 le_rfl

  have hy_le :
      y ≤ Real.log (x : ℝ) / Real.log (2 : ℝ) := by
    dsimp [y]
    exact
      (div_le_div_iff_of_pos_left hlogx hlogp hlog2).2 h2p

  have hone :
      (1 : ℝ) ≤ Real.log (x : ℝ) / Real.log (2 : ℝ) := by
    rw [le_div_iff₀ hlog2]
    simpa using h2x

  change
    ((1 + ⌊y⌋₊ : ℕ) : ℝ)
      ≤ (2 / Real.log 2) * Real.log (x : ℝ)

  calc
    ((1 + ⌊y⌋₊ : ℕ) : ℝ)
        = 1 + ((⌊y⌋₊ : ℕ) : ℝ) := by
            norm_num
    _ ≤ 1 + y := by
          exact add_le_add_left hfloor 1
    _ ≤ Real.log (x : ℝ) / Real.log 2
          + Real.log (x : ℝ) / Real.log 2 := by
          exact add_le_add hone hy_le
    _ = (2 / Real.log 2) * Real.log (x : ℝ) := by
          ring

/--
The explicit box bound is bounded by a fixed power of log x.
The constant depends only on r.
-/
theorem smoothBoxBound_real_le
    (r x : ℕ)
    (hx : 2 ≤ x) :
    (Claims.smoothBoxBound r x : ℝ)
      ≤ (2 / Real.log 2) ^ Claims.primeCount r
          * (Real.log (x : ℝ)) ^ Claims.primeCount r := by
  classical

  let S : Finset ℕ :=
    (Finset.range (r + 1)).filter Nat.Prime

  have hprod :
      (∏ p ∈ S,
          (((1 +
            ⌊Real.log (x : ℝ) / Real.log (p : ℝ)⌋₊ : ℕ) : ℝ)))
        ≤
      ∏ p ∈ S,
        ((2 / Real.log 2) * Real.log (x : ℝ)) := by
    apply Finset.prod_le_prod
    · intro p hpS
      positivity
    · intro p hpS
      have hp : Nat.Prime p :=
        (Finset.mem_filter.mp hpS).2
      exact smoothBox_factor_real_le hp hx

  calc
    (Claims.smoothBoxBound r x : ℝ)
        =
      ∏ p ∈ S,
        (((1 +
          ⌊Real.log (x : ℝ) / Real.log (p : ℝ)⌋₊ : ℕ) : ℝ)) := by
          simp [Claims.smoothBoxBound, S, Nat.cast_prod]

    _ ≤
      ∏ p ∈ S,
        ((2 / Real.log 2) * Real.log (x : ℝ)) :=
      hprod

    _ =
      (2 / Real.log 2) ^ Claims.primeCount r
        * (Real.log (x : ℝ)) ^ Claims.primeCount r := by
          simp [S, Claims.primeCount, mul_pow]

/--
Unconditional smooth-number polylogarithmic estimate.
No primality assumption on r is needed.
-/
theorem proof_smoothPolylog (r : ℕ) :
    Claims.SmoothPolylog r := by

  let C : ℝ :=
    (2 / Real.log 2) ^ Claims.primeCount r

  refine ⟨C, ?_, 2, ?_⟩

  · dsimp [C]
    have hlog2 : 0 < Real.log (2 : ℝ) :=
      Real.log_pos (by norm_num)
    positivity

  · intro x hx

    have hcount :
        (Claims.smoothCount r x : ℝ)
          ≤ (Claims.smoothBoxBound r x : ℝ) := by
      exact_mod_cast smoothCount_le_smoothBoxBound r x

    have hbox :=
      smoothBoxBound_real_le r x hx

    calc
      (Claims.smoothCount r x : ℝ)
          ≤ (Claims.smoothBoxBound r x : ℝ) :=
        hcount

      _ ≤
        (2 / Real.log 2) ^ Claims.primeCount r
          * (Real.log (x : ℝ)) ^ Claims.primeCount r :=
        hbox

      _ =
        C * (Real.log (x : ℝ)) ^ Claims.primeCount r := by
        rfl

end PrimeGPF
