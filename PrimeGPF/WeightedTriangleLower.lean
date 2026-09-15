import PrimeGPF.WeightedTriangleArea

/-!
# Lower area bound for weighted lattice triangles

The existing area theorem gives the upper estimate

`card ≤ area + O(L)`.

For Möbius inversion we also need control in the opposite direction, because
Möbius coefficients have both signs.  In dimension two there is a particularly
simple lower bound: each horizontal lattice row contains at least its real
width, and the resulting left-endpoint Riemann sum dominates the continuous
triangle area.  Consequently

`L^2 / (2*u*v) ≤ card`.

Together with `weightedTriangle_card_cast_le_area_boundary`, this gives a
one-sided absolute error of linear size without introducing measure theory.
-/
namespace PrimeGPF.Analytic

/-- A row contains at least its real width.  More precisely, for a valid first
coordinate `α`, its number of integer second coordinates is at least
`(L - α*u)/v`.
-/
theorem weightedTriangleRow_card_cast_ge_width
    {u v L : ℝ} (hu : 0 < u) (hv : 0 < v) (hL : 0 ≤ L)
    {α : ℕ} (hα : α ≤ ⌊L / u⌋₊) :
    (L - (α : ℝ) * u) / v ≤
      ((weightedTriangleRow u v L α).card : ℝ) := by
  classical
  have hLu : 0 ≤ L / u := div_nonneg hL hu.le
  have hαcast : (α : ℝ) ≤ L / u := by
    calc
      (α : ℝ) ≤ (⌊L / u⌋₊ : ℝ) := by exact_mod_cast hα
      _ ≤ L / u := Nat.floor_le hLu
  have hαmul : (α : ℝ) * u ≤ L := (le_div_iff₀ hu).mp hαcast
  have hres : 0 ≤ L - (α : ℝ) * u := sub_nonneg.mpr hαmul
  let w : ℝ := (L - (α : ℝ) * u) / v
  let R : Finset ℕ := Finset.range (⌊w⌋₊ + 1)
  let F : Finset (ℕ × ℕ) := weightedTriangleRow u v L α
  let embed : ℕ → ℕ × ℕ := fun β => (α, β)

  have himage : R.image embed ⊆ F := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨β, hβR, rfl⟩
    have hβle : β ≤ ⌊w⌋₊ := by
      have := Finset.mem_range.mp hβR
      omega
    have hw0 : 0 ≤ w := by
      dsimp [w]
      exact div_nonneg hres hv.le
    have hβw : (β : ℝ) ≤ w := by
      calc
        (β : ℝ) ≤ (⌊w⌋₊ : ℝ) := by exact_mod_cast hβle
        _ ≤ w := Nat.floor_le hw0
    have hβmul : (β : ℝ) * v ≤ L - (α : ℝ) * u := by
      dsimp [w] at hβw
      exact (le_div_iff₀ hv).mp hβw
    have hweighted : (α : ℝ) * u + (β : ℝ) * v ≤ L := by
      linarith
    apply Finset.mem_filter.mpr
    constructor
    · exact (mem_weightedTriangle_iff hu hv hL α β).2 hweighted
    · rfl

  have hembed : Function.Injective embed := by
    intro β γ h
    exact Prod.mk.inj_iff.mp h |>.2
  have hcardImage : (R.image embed).card = R.card :=
    Finset.card_image_of_injective _ hembed
  have hcardNat : R.card ≤ F.card := by
    rw [← hcardImage]
    exact Finset.card_le_card himage
  have hcardCast : ((R.card : ℕ) : ℝ) ≤ (F.card : ℝ) := by
    exact_mod_cast hcardNat
  have hRcard : R.card = ⌊w⌋₊ + 1 := by simp [R]
  have hwlt : w < ((⌊w⌋₊ + 1 : ℕ) : ℝ) := by
    exact Nat.lt_floor_add_one w
  dsimp [F]
  rw [hRcard] at hcardCast
  exact (le_of_lt hwlt).trans hcardCast

/-- The cardinality of the whole weighted triangle dominates the sum of the
real row widths. -/
theorem weightedTriangle_card_cast_ge_row_width_sum
    {u v L : ℝ} (hu : 0 < u) (hv : 0 < v) (hL : 0 ≤ L) :
    (∑ α ∈ Finset.range (⌊L / u⌋₊ + 1),
        (L - (α : ℝ) * u) / v) ≤
      ((weightedTriangle u v L).card : ℝ) := by
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
    ∑ α ∈ Finset.range (⌊L / u⌋₊ + 1),
        (L - (α : ℝ) * u) / v
        ≤ ∑ α ∈ Finset.range (A + 1),
            ((S.filter (fun e => e.1 = α)).card : ℝ) := by
          apply Finset.sum_le_sum
          intro α hα
          have hαle : α ≤ A := by
            have := Finset.mem_range.mp hα
            omega
          simpa [S, A, weightedTriangleRow] using
            (weightedTriangleRow_card_cast_ge_width hu hv hL hαle)
    _ = ((weightedTriangle u v L).card : ℝ) := by
      dsimp [S]
      exact_mod_cast hdecomp.symm

/-- Closed form for the sum of the real row widths (without the `+1` boundary
term appearing in the upper estimate). -/
theorem weighted_row_width_sum_closed_form (u v L : ℝ) (A : ℕ) :
    (∑ α ∈ Finset.range (A + 1), (L - (α : ℝ) * u) / v) =
      ((A : ℝ) + 1) * (L / v) -
        (u / v) * ((A : ℝ) * ((A : ℝ) + 1) / 2) := by
  have hfull := weighted_row_sum_closed_form u v L A
  have hones :
      (∑ _α ∈ Finset.range (A + 1), (1 : ℝ)) = (A : ℝ) + 1 := by
    simp
  calc
    (∑ α ∈ Finset.range (A + 1), (L - (α : ℝ) * u) / v)
        = (∑ α ∈ Finset.range (A + 1),
            ((L - (α : ℝ) * u) / v + 1)) -
          (∑ _α ∈ Finset.range (A + 1), (1 : ℝ)) := by
            rw [Finset.sum_sub_distrib]
            congr 1
            apply Finset.sum_congr rfl
            intro α hα
            ring
    _ = ((A : ℝ) + 1) * (L / v + 1) -
          (u / v) * ((A : ℝ) * ((A : ℝ) + 1) / 2) -
          ((A : ℝ) + 1) := by rw [hfull, hones]
    _ = ((A : ℝ) + 1) * (L / v) -
          (u / v) * ((A : ℝ) * ((A : ℝ) + 1) / 2) := by ring

/-- The continuous weighted-triangle area is a lower bound for the number of
nonnegative lattice points in the triangle. -/
theorem weightedTriangle_area_le_card_cast
    {u v L : ℝ} (hu : 0 < u) (hv : 0 < v) (hL : 0 ≤ L) :
    L ^ 2 / (2 * u * v) ≤ ((weightedTriangle u v L).card : ℝ) := by
  let A : ℕ := ⌊L / u⌋₊
  let a : ℝ := (A : ℝ)
  let t : ℝ := L / u
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg hL hu.le
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have hau : a ≤ t := by
    dsimp [a, A, t]
    exact Nat.floor_le ht0
  have hut : t < a + 1 := by
    dsimp [a, A, t]
    exact Nat.lt_floor_add_one (L / u)
  have hrow := weightedTriangle_card_cast_ge_row_width_sum hu hv hL
  have hclosed :
      (∑ α ∈ Finset.range (A + 1), (L - (α : ℝ) * u) / v) =
        (a + 1) * (L / v) -
          (u / v) * (a * (a + 1) / 2) := by
    simpa [a] using weighted_row_width_sum_closed_form u v L A
  have hsumArea :
      L ^ 2 / (2 * u * v) ≤
        (a + 1) * (L / v) -
          (u / v) * (a * (a + 1) / 2) := by
    have huv : 0 < u / v := div_pos hu hv
    have hdelta : 0 ≤ a + 2 * (t - a) - (t - a) ^ 2 := by
      have hδ0 : 0 ≤ t - a := sub_nonneg.mpr hau
      have hδ1 : t - a < 1 := by linarith
      nlinarith
    dsimp [t] at hdelta ⊢
    field_simp [ne_of_gt hu, ne_of_gt hv] at hdelta ⊢
    nlinarith
  rw [hclosed] at hrow
  exact hsumArea.trans hrow

/-- Two-sided error estimate: the lattice count differs from the geometric
area by a nonnegative quantity bounded by the same explicit linear boundary
term used in the upper theorem.  This is the form needed for signed Möbius
summation. -/
theorem weightedTriangle_card_sub_area_bounds
    {u v L : ℝ} (hu : 0 < u) (hv : 0 < v) (hL : 0 ≤ L) :
    0 ≤ ((weightedTriangle u v L).card : ℝ) - L ^ 2 / (2 * u * v) ∧
    ((weightedTriangle u v L).card : ℝ) - L ^ 2 / (2 * u * v) ≤
      L / u + 3 * L / (2 * v) + 1 := by
  constructor
  · linarith [weightedTriangle_area_le_card_cast hu hv hL]
  · linarith [weightedTriangle_card_cast_le_area_boundary hu hv hL]

end PrimeGPF.Analytic
