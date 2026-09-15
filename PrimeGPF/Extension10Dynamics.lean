import PrimeGPF.Extensions

/-!
# Extension 10: easy dynamical separation

This file formalizes the direction that needs no finite-orbit argument:
for an odd prime exponential anchor `a`, there is no map intertwining the
homogeneous translation `H_c` with the exponential translation `E_a`.

The proof uses only the fixed point `H_c(c)=c` and the already proved strict
growth of every anchored exponential translation with anchor different from 2.
-/
namespace PrimeGPF

/-- The anchored homogeneous translation fixes its anchor. -/
theorem homogeneous_left_fixed (c : Prime) :
    homogeneousOperate c c = c :=
  homogeneousOperate_idempotent c

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
