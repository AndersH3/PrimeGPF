import PrimeGPF.Extension7Core
import PrimeGPF.Statements

/-!
# Extension 7: finite counting bound

This isolates the exact finite combinatorial estimate preceding the asymptotic
lattice-counting step in extension 7.
-/
namespace PrimeGPF
open Claims

noncomputable def extension7CollisionInputs (a X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (X + 1)).filter
    (fun q => Nat.Prime q ∧ add a q = mul a q)

noncomputable def extension7CollisionCount (a X : ℕ) : ℕ :=
  (extension7CollisionInputs a X).card

/-- Every collision input at most `R_a` is among the primes at most `R_a`. -/
theorem extension7_low_collision_count_le_primeCount
    {a X : ℕ} (_ha : Nat.Prime a) :
    ((extension7CollisionInputs a X).filter
      (fun q => q ≤ gpf (a ^ 2 + a - 1))).card
      ≤ Claims.primeCount (gpf (a ^ 2 + a - 1)) := by
  classical
  apply Finset.card_le_card
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  have hC := Finset.mem_filter.mp hq'.1
  simp only [Claims.primeCount, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hC.2.1⟩

/-- Large collision inputs inject, via their additive kernels, into the
`R_a`-smooth integers up to `X+a+1`. -/
theorem extension7_high_collision_count_le_smoothCount
    {a X : ℕ} (ha : Nat.Prime a) :
    ((extension7CollisionInputs a X).filter
      (fun q => ¬ q ≤ gpf (a ^ 2 + a - 1))).card
      ≤ Claims.smoothCount (gpf (a ^ 2 + a - 1)) (X + a + 1) := by
  classical
  let R := gpf (a ^ 2 + a - 1)
  let H := (extension7CollisionInputs a X).filter (fun q => ¬ q ≤ R)
  let B := (Finset.range (X + a + 2)).filter (Smooth R)
  let code : {q // q ∈ H} → ℕ := fun q => a + q.1 + 1

  have hcode_mem : ∀ q : {q // q ∈ H}, code q ∈ B := by
    intro q
    have hqH := Finset.mem_filter.mp q.property
    have hqC := Finset.mem_filter.mp hqH.1
    have hq : Nat.Prime q.1 := hqC.2.1
    have hcoll : add a q.1 = mul a q.1 := hqC.2.2
    have hqx : q.1 ≤ X := by
      have := Finset.mem_range.mp hqC.1
      omega
    have hsmooth : Smooth R (a + q.1 + 1) := by
      dsimp [R]
      exact extension7_collision_add_kernel_smooth ha hq hcoll
    apply Finset.mem_filter.mpr
    refine ⟨?_, hsmooth⟩
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
    ((extension7CollisionInputs a X).filter
      (fun q => ¬ q ≤ gpf (a ^ 2 + a - 1))).card
        = H.card := by rfl
    _ = I.card := hIcard.symm
    _ ≤ B.card := Finset.card_le_card hI_subset
    _ = Claims.smoothCount R (X + a + 1) := by
      simp [Claims.smoothCount, B]
    _ = Claims.smoothCount (gpf (a ^ 2 + a - 1)) (X + a + 1) := by rfl

/-- Exact finite estimate underlying equation (12), before replacing the
restricted smooth count by its sharp asymptotic. -/
theorem extension7_collisionCount_le_primeCount_add_smoothCount
    {a X : ℕ} (ha : Nat.Prime a) :
    extension7CollisionCount a X ≤
      Claims.primeCount (gpf (a ^ 2 + a - 1)) +
      Claims.smoothCount (gpf (a ^ 2 + a - 1)) (X + a + 1) := by
  classical
  let C := extension7CollisionInputs a X
  let R := gpf (a ^ 2 + a - 1)
  let L := C.filter (fun q => q ≤ R)
  let H := C.filter (fun q => ¬ q ≤ R)
  have hsplit : L.card + H.card = C.card := by
    dsimp [L, H]
    exact Finset.filter_card_add_filter_neg_card_eq_card
      (s := C) (fun q : ℕ => q ≤ R)
  have hL : L.card ≤ Claims.primeCount R := by
    dsimp [L, C, R]
    exact extension7_low_collision_count_le_primeCount ha
  have hH : H.card ≤ Claims.smoothCount R (X + a + 1) := by
    dsimp [H, C, R]
    exact extension7_high_collision_count_le_smoothCount ha
  calc
    extension7CollisionCount a X = C.card := by rfl
    _ = L.card + H.card := hsplit.symm
    _ ≤ Claims.primeCount R + Claims.smoothCount R (X + a + 1) :=
      Nat.add_le_add hL hH
    _ = Claims.primeCount (gpf (a ^ 2 + a - 1)) +
        Claims.smoothCount (gpf (a ^ 2 + a - 1)) (X + a + 1) := by rfl

end PrimeGPF
