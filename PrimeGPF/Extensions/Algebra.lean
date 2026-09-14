import PrimeGPF.Elementary

namespace PrimeGPF.Extensions

/-- The unshifted homogeneous additive GPF operation on the same prime carrier. -/
def homogeneous (p q : Prime) : Prime :=
  ⟨gpf (p.val + q.val), (gpf_spec (by have := p.property.two_le; omega)).1⟩

theorem homogeneous_idempotent (p : Prime) : homogeneous p p = p := by
  apply Subtype.ext
  change gpf (p.val + p.val) = p.val
  apply gpf_eq_of_spec (by have := p.property.two_le; omega)
  refine ⟨p.property, ?_, ?_⟩
  · exact ⟨2, by omega⟩
  · intro r hr hd
    have hd' : r ∣ 2 * p.val := by convert hd using 1 <;> omega
    rcases hr.dvd_mul.mp hd' with h2 | hp
    · have := Nat.le_of_dvd (by norm_num : 0 < 2) h2
      have := p.property.two_le
      omega
    · exact Nat.le_of_dvd p.property.pos hp

theorem operate_not_idempotent (o : Op) (p : Prime) : operate o p p ≠ p := by
  intro he
  have hv := congrArg Subtype.val he
  cases o with
  | add => exact add_not_idempotent p.property hv
  | mul => exact mul_ne_left p.property p.property hv
  | exp => exact exp_ne_left p.property p.property hv

/-- Homomorphism notion for binary operations, without assuming associativity. -/
def Preserves (f g : Prime → Prime → Prime) (h : Prime → Prime) : Prop :=
  ∀ p q, h (f p q) = g (h p) (h q)

/-- Extension 10(a): there is no homomorphism from the homogeneous magma
to any of the three shifted-kernel magmas. -/
theorem no_hom_from_homogeneous (o : Op) :
    ¬ ∃ h, Preserves homogeneous (operate o) h := by
  rintro ⟨h, hh⟩
  let p : Prime := ⟨2, Nat.prime_two⟩
  have he := hh p p
  rw [homogeneous_idempotent] at he
  exact operate_not_idempotent o (h p) he.symm

/-- Extension 10(a), reverse direction: no injective homomorphism exists. -/
theorem no_injective_hom_to_homogeneous (o : Op) :
    ¬ ∃ h, Function.Injective h ∧ Preserves (operate o) homogeneous h := by
  rintro ⟨h, hinj, hh⟩
  let p : Prime := ⟨2, Nat.prime_two⟩
  have he := hh p p
  rw [homogeneous_idempotent] at he
  exact operate_not_idempotent o p (hinj he)

end PrimeGPF.Extensions
