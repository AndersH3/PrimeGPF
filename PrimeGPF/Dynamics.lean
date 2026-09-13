import PrimeGPF.Elementary

namespace PrimeGPF
open Claims

/-- Determinism propagates a repeated state to every later time. -/
theorem orbit_repeat {α : Type*} (f : α → α) (x : α) {i j : ℕ}
    (h : orbit f x i = orbit f x j) (k : ℕ) :
    orbit f x (i + k) = orbit f x (j + k) := by
  induction k with
  | zero => simpa using h
  | succ k ih => simpa [Nat.add_assoc, orbit] using congrArg f ih

theorem eventuallyPeriodic_of_repeat {α : Type*} (f : α → α) (x : α)
    {i j : ℕ} (hij : i < j) (he : orbit f x i = orbit f x j) :
    EventuallyPeriodic f x := by
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  have h := orbit_repeat f x he (n - i)
  have h₁ : i + (n - i) = n := by omega
  have h₂ : j + (n - i) = n + (j - i) := by omega
  simpa [h₁, h₂] using h.symm

/-- Theorem 7.5, proved for the stated prime map (no GPF-specific assumption). -/
theorem proof_7_5 : t7_5 := by
  classical
  intro f x h
  obtain ⟨S, hS⟩ := h
  obtain ⟨i, _, j, _, hne, he⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (S.card + 1)) (t := S)
      (f := orbit f x) (by simp) (by intro n _; exact hS n)
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact eventuallyPeriodic_of_repeat f x hij he
  · exact eventuallyPeriodic_of_repeat f x hji he.symm

/-- Reusable implication for 5.3; Orders.lean supplies proof_5_2 and proof_5_3. -/
theorem proof_5_3_from_5_2 (H : t5_2) : t5_3 := by
  have step : ∀ p : Prime, (diagonal .mul p).val % 4 = 1 := by
    intro p; exact (H p.val p.property).1
  have allsteps : ∀ p : Prime, ∀ n, 0 < n →
      (orbit (diagonal .mul) p n).val % 4 = 1 := by
    intro p n hn
    cases n with
    | zero => omega
    | succ n => exact step (orbit (diagonal .mul) p n)
  refine ⟨allsteps, ?_⟩
  intro p h
  obtain ⟨d, hd, he⟩ := h
  simpa [he] using allsteps p d hd

/-- A general increasing-map lemma used by Corollary 8.5. -/
theorem increasing_orbit (f : Prime → Prime)
    (hf : ∀ x, x.val < (f x).val) (x : Prime) :
    StrictMono (fun n => (orbit f x n).val) ∧
    (∀ B, ∃ n, B < (orbit f x n).val) ∧ ¬ Periodic f x := by
  have hs : StrictMono (fun n => (orbit f x n).val) :=
    strictMono_nat_of_lt_succ (fun n => hf (orbit f x n))
  have hbound : ∀ n, n ≤ (orbit f x n).val := by
    intro n
    induction n with
    | zero => omega
    | succ n ih => have h := hf (orbit f x n); change n + 1 ≤ (f (orbit f x n)).val; omega
  refine ⟨hs, ?_, ?_⟩
  · intro B; exact ⟨B + 1, lt_of_lt_of_le (by omega) (hbound _)⟩
  · rintro ⟨d, hd, he⟩
    have hh := hs hd
    simpa [orbit, he] using hh

end PrimeGPF
