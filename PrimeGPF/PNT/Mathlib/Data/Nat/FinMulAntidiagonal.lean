/-
Compatibility shim for the historical PrimeNumberTheoremAnd backport.

The upstream PNT development at the Lean-4.19-compatible commit used the old
`Nat.finMulAntidiagonal` API.  PrimeGPF's pinned mathlib already contains the
same mathematics under the subsequently standardized `Nat.finMulAntidiag`
API in `Mathlib.Algebra.Order.Antidiag.Nat`.

Keeping a second implementation causes duplicate declaration errors when
mathlib later imports the standardized file.  This module therefore only
re-exports the old names used by the vendored PNT sources as thin wrappers
around the pinned-mathlib declarations.
-/

import Mathlib.Algebra.Order.Antidiag.Nat

open Finset
open scoped BigOperators ArithmeticFunction

namespace Nat

abbrev finMulAntidiagonal (d n : ℕ) : Finset (Fin d → ℕ) :=
  finMulAntidiag d n

@[simp]
theorem mem_finMulAntidiagonal {d n : ℕ} {f : Fin d → ℕ} :
    f ∈ finMulAntidiagonal d n ↔ ∏ i, f i = n ∧ n ≠ 0 := by
  simpa [finMulAntidiagonal] using (mem_finMulAntidiag (d := d) (n := n) (f := f))

@[simp]
theorem finMulAntidiagonal_zero {d : ℕ} :
    finMulAntidiagonal d 0 = ∅ := by
  simpa [finMulAntidiagonal] using finMulAntidiag_zero_right d

theorem finMulAntidiagonal_one {d : ℕ} :
    finMulAntidiagonal d 1 = {fun _ => 1} := by
  simpa [finMulAntidiagonal] using (finMulAntidiag_one (d := d))

theorem finMulAntidiagonal_empty_of_ne_one {n : ℕ} (hn : n ≠ 1) :
    finMulAntidiagonal 0 n = ∅ := by
  simpa [finMulAntidiagonal] using (finMulAntidiag_zero_left (n := n) hn)

theorem dvd_of_mem_finMulAntidiagonal {n d : ℕ} {f : Fin d → ℕ}
    (hf : f ∈ finMulAntidiagonal d n) (i : Fin d) : f i ∣ n := by
  exact dvd_of_mem_finMulAntidiag hf i

theorem ne_zero_of_mem_finMulAntidiagonal {d n : ℕ} {f : Fin d → ℕ}
    (hf : f ∈ finMulAntidiagonal d n) (i : Fin d) : f i ≠ 0 := by
  exact ne_zero_of_mem_finMulAntidiag hf i

theorem prod_eq_of_mem_finMulAntidiagonal {d n : ℕ} {f : Fin d → ℕ}
    (hf : f ∈ finMulAntidiagonal d n) : ∏ i, f i = n := by
  exact prod_eq_of_mem_finMulAntidiag hf

theorem finMulAntidiagonal_univ_eq {d m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    finMulAntidiagonal d m =
      (Fintype.piFinset fun _ : Fin d => n.divisors).filter fun f => ∏ i, f i = m := by
  simpa [finMulAntidiagonal] using
    (finMulAntidiag_eq_piFinset_divisors_filter (d := d) (m := m) (n := n) hmn hn)

lemma image_apply_finMulAntidiagonal {d n : ℕ} {i : Fin d} (hd : d ≠ 1) :
    (finMulAntidiagonal d n).image (fun f => f i) = divisors n := by
  simpa [finMulAntidiagonal] using
    (image_apply_finMulAntidiag (d := d) (n := n) (i := i) hd)

lemma image_piFinTwoEquiv {n : ℕ} :
    (finMulAntidiagonal 2 n).image (piFinTwoEquiv fun _ => ℕ) = divisorsAntidiagonal n := by
  simpa [finMulAntidiagonal] using (image_piFinTwoEquiv_finMulAntidiag (n := n))

lemma finMulAntidiagonal_exists_unique_prime_dvd {d n p : ℕ} (hn : Squarefree n)
    (hp : p ∈ n.primeFactorsList) (f : Fin d → ℕ)
    (hf : f ∈ finMulAntidiagonal d n) : ∃! i, p ∣ f i := by
  exact finMulAntidiag_exists_unique_prime_dvd hn hp f hf

theorem card_finMulAntidiagonal {d n : ℕ} (hn : Squarefree n) :
    (finMulAntidiagonal d n).card = d ^ ArithmeticFunction.cardDistinctFactors n := by
  simpa [finMulAntidiagonal] using (card_finMulAntidiag_of_squarefree (d := d) hn)

theorem card_lcm_eq {n : ℕ} (hn : Squarefree n) :
    Finset.card ((n.divisors ×ˢ n.divisors).filter fun ⟨x, y⟩ => x.lcm y = n) =
      3 ^ ArithmeticFunction.cardDistinctFactors n := by
  simpa only [eq_comm] using (card_pair_lcm_eq hn).symm

end Nat
