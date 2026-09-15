import PrimeGPF.Extensions

/-!
# Extension 10: dynamical separation

This file develops the dynamical part of extension 10.  It keeps the proof
independent of any asymptotic input: the homogeneous translation has bounded
orbits and hence eventually periodic orbits, whereas an anchored exponential
translation with anchor different from 2 moves every prime strictly upward.
-/
namespace PrimeGPF

/-- The anchored homogeneous translation fixes its anchor. -/
theorem homogeneous_left_fixed (c : Prime) :
    homogeneousOperate c c = c :=
  homogeneousOperate_idempotent c

/-- A composite integer greater than one has greatest prime factor at most
half of the integer. -/
theorem two_mul_gpf_le_of_composite {n : ℕ} (hn : 1 < n)
    (hcomp : ¬ Nat.Prime n) :
    2 * gpf n ≤ n := by
  have hg := gpf_spec hn
  obtain ⟨s, hs⟩ := hg.2.1
  have hspos : 0 < s := by
    by_contra h
    have hs0 : s = 0 := by omega
    rw [hs0, Nat.mul_zero] at hs
    omega
  have hsne : s ≠ 1 := by
    intro hs1
    apply hcomp
    have he : n = gpf n := by simpa [hs1] using hs
    exact (gpf_eq_self_iff hn).mp he.symm
  have hs2 : 2 ≤ s := by omega
  have hmul := Nat.mul_le_mul_left (gpf n) hs2
  calc
    2 * gpf n = gpf n * 2 := by ring
    _ ≤ gpf n * s := hmul
    _ = n := hs.symm

/-- For an odd prime anchor, one homogeneous step never exceeds the larger of
the current value and `c+2`.  The exceptional current value 2 is handled
separately; for odd current values the sum is an even composite integer. -/
theorem homogeneous_step_bound (c q : Prime) (hc2 : c.val ≠ 2) :
    (homogeneousOperate c q).val ≤ max q.val (c.val + 2) := by
  change gpf (c.val + q.val) ≤ max q.val (c.val + 2)
  by_cases hq2 : q.val = 2
  · rw [hq2]
    exact (gpf_le (c.val + 2)).trans (le_max_right _ _)
  · have hcodd : c.val % 2 = 1 := c.property.eq_two_or_odd.resolve_left hc2
    have hqodd : q.val % 2 = 1 := q.property.eq_two_or_odd.resolve_left hq2
    have hsumEven : (c.val + q.val) % 2 = 0 := by omega
    have hsum2 : 2 ∣ c.val + q.val := Nat.dvd_of_mod_eq_zero hsumEven
    have hc3 : 3 ≤ c.val := by have := c.property.two_le; omega
    have hq3 : 3 ≤ q.val := by have := q.property.two_le; omega
    have hsum : 1 < c.val + q.val := by omega
    have hcomp : ¬ Nat.Prime (c.val + q.val) := by
      intro hprime
      have htwoeq : 2 = c.val + q.val :=
        (Nat.dvd_prime hprime).mp hsum2 |>.resolve_left (by norm_num)
      omega
    have hhalf := two_mul_gpf_le_of_composite hsum hcomp
    have hcB : c.val ≤ max q.val (c.val + 2) :=
      le_trans (by omega) (le_max_right _ _)
    have hqB : q.val ≤ max q.val (c.val + 2) := le_max_left _ _
    omega

/-- Every homogeneous orbit at an odd prime anchor is bounded by the maximum
of its initial value and `c+2`. -/
theorem homogeneous_orbit_bounded (c x : Prime) (hc2 : c.val ≠ 2) :
    ∀ n, (orbit (homogeneousOperate c) x n).val ≤ max x.val (c.val + 2) := by
  intro n
  induction n with
  | zero =>
      simp only [orbit]
      exact le_max_left _ _
  | succ n ih =>
      simp only [orbit]
      have hstep := homogeneous_step_bound c (orbit (homogeneousOperate c) x n) hc2
      exact hstep.trans (max_le ih (le_max_right _ _))

/-- Every orbit of the homogeneous translation anchored at an odd prime is
eventually periodic.  This is the first dynamical statement in extension 10. -/
theorem extension10_homogeneous_eventuallyPeriodic
    (c x : Prime) (hc2 : c.val ≠ 2) :
    EventuallyPeriodic (homogeneousOperate c) x := by
  let B := max x.val (c.val + 2)
  obtain ⟨i, _, j, _, hne, heval⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (B + 2))
      (t := Finset.range (B + 1))
      (f := fun n => (orbit (homogeneousOperate c) x n).val)
      (by simp)
      (by
        intro n hn
        apply Finset.mem_range.mpr
        have hb := homogeneous_orbit_bounded c x hc2 n
        dsimp [B]
        omega)
  have he : orbit (homogeneousOperate c) x i =
      orbit (homogeneousOperate c) x j := by
    apply Subtype.ext
    exact heval
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact eventuallyPeriodic_of_repeat (homogeneousOperate c) x hij he
  · exact eventuallyPeriodic_of_repeat (homogeneousOperate c) x hji he.symm

/-- For an exponential anchor different from 2, every point moves strictly
upward. -/
theorem exp_left_strict_growth (a : Prime) (ha2 : a.val ≠ 2) (q : Prime) :
    q.val < (operate .exp a q).val :=
  (proof_8_5.1 a ha2).1 q

/-- There is no semiconjugacy from an anchored homogeneous translation to an
anchored exponential translation with odd prime anchor.

Equivalently, no map `h` can satisfy
`h (H_c(q)) = E_a(h(q))` for every prime `q` when `a ≠ 2`.
This is the second dynamical-separation bullet in extension 10 of the report. -/
theorem extension10_no_map_homogeneous_to_exp
    (a c : Prime) (ha2 : a.val ≠ 2) (h : Prime → Prime) :
    ¬ (∀ q : Prime,
      h (homogeneousOperate c q) = operate .exp a (h q)) := by
  intro hintertwine
  have hfix := hintertwine c
  rw [homogeneous_left_fixed] at hfix
  have hval := congrArg Subtype.val hfix
  have hgrow := exp_left_strict_growth a ha2 (h c)
  omega

end PrimeGPF
