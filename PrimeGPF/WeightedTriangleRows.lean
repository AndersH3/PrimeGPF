import PrimeGPF.WeightedTriangle

/-!
# Row decomposition for weighted lattice triangles

This file refines the rectangular bound in `WeightedTriangle` by slicing the
triangle at fixed first coordinate.  It is the finite combinatorial step
behind the sharp two-dimensional area coefficient.
-/
namespace PrimeGPF.Analytic

/-- A row of a weighted triangle at fixed first coordinate. -/
noncomputable def weightedTriangleRow (u v L : ℝ) (α : ℕ) : Finset (ℕ × ℕ) :=
  (weightedTriangle u v L).filter (fun e => e.1 = α)

/-- A row can contain at most the obvious number of second coordinates. -/
theorem weightedTriangleRow_card_cast_le
    {u v L : ℝ} (hu : 0 < u) (hv : 0 < v) (hL : 0 ≤ L)
    {α : ℕ} (hα : α ≤ ⌊L / u⌋₊) :
    ((weightedTriangleRow u v L α).card : ℝ) ≤
      (L - (α : ℝ) * u) / v + 1 := by
  classical
  have hLu : 0 ≤ L / u := div_nonneg hL hu.le
  have hαcast : (α : ℝ) ≤ L / u := by
    calc
      (α : ℝ) ≤ (⌊L / u⌋₊ : ℝ) := by exact_mod_cast hα
      _ ≤ L / u := Nat.floor_le hLu
  have hαmul : (α : ℝ) * u ≤ L := (le_div_iff₀ hu).mp hαcast
  have hres : 0 ≤ L - (α : ℝ) * u := sub_nonneg.mpr hαmul
  let F := weightedTriangleRow u v L α
  let R := Finset.range (⌊(L - (α : ℝ) * u) / v⌋₊ + 1)
  have hinj : Set.InjOn (fun e : ℕ × ℕ => e.2) (F : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    have hxf : x.1 = α := (Finset.mem_filter.mp hx).2
    have hyf : y.1 = α := (Finset.mem_filter.mp hy).2
    apply Prod.ext
    · simp [hxf, hyf]
    · exact hxy
  have himage : F.image (fun e : ℕ × ℕ => e.2) ⊆ R := by
    intro β hβ
    rcases Finset.mem_image.mp hβ with ⟨e, heF, rfl⟩
    have heRow := Finset.mem_filter.mp heF
    have heTri := Finset.mem_filter.mp heRow.1
    have heq : e.1 = α := heRow.2
    have hine : (e.1 : ℝ) * u + (e.2 : ℝ) * v ≤ L := heTri.2
    have hβmul : (e.2 : ℝ) * v ≤ L - (α : ℝ) * u := by
      rw [heq] at hine
      linarith
    have hβdiv : (e.2 : ℝ) ≤ (L - (α : ℝ) * u) / v :=
      (le_div_iff₀ hv).2 hβmul
    have hquot : 0 ≤ (L - (α : ℝ) * u) / v := div_nonneg hres hv.le
    have hfloor : e.2 ≤ ⌊(L - (α : ℝ) * u) / v⌋₊ :=
      (Nat.le_floor_iff hquot).2 hβdiv
    exact Finset.mem_range.mpr (by omega)
  have hcardImage :
      (F.image (fun e : ℕ × ℕ => e.2)).card = F.card :=
    Finset.card_image_of_injOn hinj
  have hcardNat : F.card ≤ R.card := by
    rw [← hcardImage]
    exact Finset.card_le_card himage
  have hcardNat' : F.card ≤ ⌊(L - (α : ℝ) * u) / v⌋₊ + 1 := by
    simpa [R] using hcardNat
  have hfloorle :
      (⌊(L - (α : ℝ) * u) / v⌋₊ : ℝ) ≤
        (L - (α : ℝ) * u) / v :=
    Nat.floor_le (div_nonneg hres hv.le)
  dsimp [F] at hcardNat' ⊢
  calc
    ((weightedTriangleRow u v L α).card : ℝ)
        ≤ ((⌊(L - (α : ℝ) * u) / v⌋₊ + 1 : ℕ) : ℝ) := by
          exact_mod_cast hcardNat'
    _ = (⌊(L - (α : ℝ) * u) / v⌋₊ : ℝ) + 1 := by norm_num
    _ ≤ (L - (α : ℝ) * u) / v + 1 := by linarith

/-- The whole weighted triangle is bounded by the sum of its real row-width
bounds.  This is the finite floor-sum reduction used for the area estimate. -/
theorem weightedTriangle_card_cast_le_row_sum
    {u v L : ℝ} (hu : 0 < u) (hv : 0 < v) (hL : 0 ≤ L) :
    ((weightedTriangle u v L).card : ℝ) ≤
      ∑ α ∈ Finset.range (⌊L / u⌋₊ + 1),
        ((L - (α : ℝ) * u) / v + 1) := by
  classical
  let S := weightedTriangle u v L
  let A := ⌊L / u⌋₊
  have hmaps : (S : Set (ℕ × ℕ)).MapsTo
      (fun e : ℕ × ℕ => e.1) (Finset.range (A + 1) : Set ℕ) := by
    intro e he
    have heTri := Finset.mem_filter.mp he
    have heProd := Finset.mem_product.mp heTri.1
    simpa [A] using heProd.1
  have hdecomp :
      S.card = ∑ α ∈ Finset.range (A + 1),
        (S.filter (fun e => e.1 = α)).card := by
    simpa using
      (Finset.card_eq_sum_card_fiberwise
        (s := S) (t := Finset.range (A + 1))
        (f := fun e : ℕ × ℕ => e.1) hmaps)
  calc
    ((weightedTriangle u v L).card : ℝ)
        = ∑ α ∈ Finset.range (A + 1),
            ((S.filter (fun e => e.1 = α)).card : ℝ) := by
          dsimp [S]
          exact_mod_cast hdecomp
    _ ≤ ∑ α ∈ Finset.range (A + 1),
          ((L - (α : ℝ) * u) / v + 1) := by
      apply Finset.sum_le_sum
      intro α hα
      have hαle : α ≤ A := by
        have := Finset.mem_range.mp hα
        omega
      simpa [S, A, weightedTriangleRow] using
        (weightedTriangleRow_card_cast_le hu hv hL hαle)
    _ = ∑ α ∈ Finset.range (⌊L / u⌋₊ + 1),
          ((L - (α : ℝ) * u) / v + 1) := by rfl

end PrimeGPF.Analytic
