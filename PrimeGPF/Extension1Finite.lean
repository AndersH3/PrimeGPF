import PrimeGPF.Extension17Support
import PrimeGPF.Statements

/-!
# Extension 1: exact finite restricted-support bound

This formalizes the combinatorial inequality immediately preceding the sharp
lattice-point asymptotic in extension 1.
-/
namespace PrimeGPF
open Claims

/-- Integers whose prime divisors are at most `r` and avoid all prime divisors
of the shifted anchor `a+1`. -/
def RestrictedSmooth (a r n : ℕ) : Prop :=
  Smooth r n ∧ ∀ s, Nat.Prime s → s ∣ n → ¬ s ∣ a + 1

noncomputable def restrictedSmoothCount (a r X : ℕ) : ℕ := by
  classical
  exact ((Finset.range (X + 1)).filter (RestrictedSmooth a r)).card

noncomputable def extension1FiberInputs (a r X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (X + 1)).filter
    (fun q => Nat.Prime q ∧ add a q = r)

/-- Inputs `q ≤ r` contribute at most the number of primes up to `r`. -/
theorem extension1_low_fiber_count_le_primeCount
    {a r X : ℕ} :
    ((extension1FiberInputs a r X).filter (fun q => q ≤ r)).card
      ≤ Claims.primeCount r := by
  classical
  apply Finset.card_le_card
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  have hF := Finset.mem_filter.mp hq'.1
  simp only [Claims.primeCount, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hF.2.1⟩

/-- A large additive-fiber input maps injectively to its additive kernel, which
has exactly the restricted support used in the report. -/
theorem extension1_high_fiber_count_le_restrictedSmoothCount
    {a r X : ℕ} (ha : Nat.Prime a) (hr : Nat.Prime r) :
    ((extension1FiberInputs a r X).filter (fun q => ¬ q ≤ r)).card
      ≤ restrictedSmoothCount a r (X + a + 1) := by
  classical
  let H := (extension1FiberInputs a r X).filter (fun q => ¬ q ≤ r)
  let B := (Finset.range (X + a + 2)).filter (RestrictedSmooth a r)
  let code : {q // q ∈ H} → ℕ := fun q => a + q.1 + 1

  have hcode_mem : ∀ q : {q // q ∈ H}, code q ∈ B := by
    intro q
    have hqH := Finset.mem_filter.mp q.property
    have hqF := Finset.mem_filter.mp hqH.1
    have hq : Nat.Prime q.1 := hqF.2.1
    have hout : add a q.1 = r := hqF.2.2
    have hrq : r < q.1 := by omega
    have hqx : q.1 ≤ X := by
      have := Finset.mem_range.mp hqF.1
      omega
    have hsmooth : Smooth r (a + q.1 + 1) := by
      constructor
      · have hgt := kernel_gt_one .add ha hq
        simpa [kernel] using (show 0 < kernel .add a q.1 by omega)
      · intro s hs hsd
        exact (extension1_large_input_support_exclusion ha hr hq hout hrq hs hsd).1
    have hrestrict : RestrictedSmooth a r (a + q.1 + 1) := by
      refine ⟨hsmooth, ?_⟩
      intro s hs hsd
      exact (extension1_large_input_support_exclusion ha hr hq hout hrq hs hsd).2
    apply Finset.mem_filter.mpr
    refine ⟨?_, hrestrict⟩
    apply Finset.mem_range.mpr
    dsimp [code]
    omega

  have hcode_inj : Function.Injective code := by
    intro q₁ q₂ h
    apply Subtype.ext
    dsimp [code] at h
    omega

  let I : Finset ℕ := H.attach.image code
  have hI_subset : I ⊆ B := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨q, hq, rfl⟩
    exact hcode_mem q
  have hIcard : I.card = H.card := by
    dsimp [I]
    rw [Finset.card_image_of_injective _ hcode_inj]
    simp

  calc
    ((extension1FiberInputs a r X).filter (fun q => ¬ q ≤ r)).card
        = H.card := by rfl
    _ = I.card := hIcard.symm
    _ ≤ B.card := Finset.card_le_card hI_subset
    _ = restrictedSmoothCount a r (X + a + 1) := by
      simp [restrictedSmoothCount, B]

/-- Exact finite version of the report's estimate
`F⁺_{a,r}(X) ≤ π(r) + S_T(X+a+1)` (with the support restriction expressed
intrinsically rather than by naming the finite prime set `T`). -/
theorem extension1_fiberCount_le_primeCount_add_restrictedSmoothCount
    {a r X : ℕ} (ha : Nat.Prime a) (hr : Nat.Prime r) :
    Claims.fiberCount .add a r X ≤
      Claims.primeCount r + restrictedSmoothCount a r (X + a + 1) := by
  classical
  let F := extension1FiberInputs a r X
  let L := F.filter (fun q => q ≤ r)
  let H := F.filter (fun q => ¬ q ≤ r)
  have hsplit : L.card + H.card = F.card := by
    dsimp [L, H]
    exact Finset.filter_card_add_filter_neg_card_eq_card
      (s := F) (fun q : ℕ => q ≤ r)
  have hL : L.card ≤ Claims.primeCount r := by
    dsimp [L, F]
    exact extension1_low_fiber_count_le_primeCount
  have hH : H.card ≤ restrictedSmoothCount a r (X + a + 1) := by
    dsimp [H, F]
    exact extension1_high_fiber_count_le_restrictedSmoothCount ha hr
  have hF : Claims.fiberCount .add a r X = F.card := by
    simp [Claims.fiberCount, extension1FiberInputs, F]
  calc
    Claims.fiberCount .add a r X = F.card := hF
    _ = L.card + H.card := hsplit.symm
    _ ≤ Claims.primeCount r + restrictedSmoothCount a r (X + a + 1) :=
      Nat.add_le_add hL hH

end PrimeGPF
