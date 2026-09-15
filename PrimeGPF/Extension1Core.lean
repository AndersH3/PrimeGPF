import PrimeGPF.Extensions

/-!
# Extension 1: elementary fixed-fiber core

This file isolates the easy exceptional case in extension 1.  When the fixed
output prime `r` divides `a+1`, any prime input in the additive fiber is forced
to be `r`; consequently the truncated fiber has cardinality at most one.

The sharp lattice-counting asymptotic for the complementary case is separate.
-/
namespace PrimeGPF
open Claims

/-- If `r ∣ a+1`, a prime input giving additive output `r` must itself be `r`. -/
theorem extension1_input_eq_output_of_dvd_anchor
    {a r q : ℕ} (ha : Nat.Prime a) (hr : Nat.Prime r) (hq : Nat.Prime q)
    (har : r ∣ a + 1) (hout : add a q = r) :
    q = r := by
  have hk : r ∣ a + q + 1 := by
    have h := (output_spec .add ha hq).2.1
    simpa [hout] using h
  have hk' : r ∣ (a + 1) + q := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk
  have hbase : (a + 1) % r = 0 := Nat.mod_eq_zero_of_dvd har
  have htot : ((a + 1) + q) % r = 0 := Nat.mod_eq_zero_of_dvd hk'
  rw [Nat.add_mod, hbase, zero_add, Nat.mod_mod] at htot
  have hqdiv : r ∣ q := Nat.dvd_of_mod_eq_zero htot
  rcases (Nat.dvd_prime hq).mp hqdiv with h1 | hrq
  · exact (hr.ne_one h1).elim
  · exact hrq.symm

/-- The exceptional additive fixed-output fiber has at most one prime input. -/
theorem extension1_dividing_anchor_fiberCount_le_one
    {a r x : ℕ} (ha : Nat.Prime a) (hr : Nat.Prime r)
    (har : r ∣ a + 1) :
    Claims.fiberCount .add a r x ≤ 1 := by
  classical
  unfold Claims.fiberCount
  let F := (Finset.range (x + 1)).filter
    (fun q => Nat.Prime q ∧ output .add a q = r)
  have hsub : F ⊆ ({r} : Finset ℕ) := by
    intro q hqF
    have hq := (Finset.mem_filter.mp hqF).2
    have hqr : q = r :=
      extension1_input_eq_output_of_dvd_anchor ha hr hq.1 har hq.2
    simp [hqr]
  have hc := Finset.card_le_card hsub
  simpa [F] using hc

end PrimeGPF
