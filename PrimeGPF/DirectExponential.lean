import PrimeGPF.Arithmetic

/-! Direct elementary replacement for the Zsigmondy dependency of 8.1.
New proof scripts, not compiler-verified in this environment. -/
namespace PrimeGPF
open Claims

/-- Positive alternating cofactor of p^(2*n+1)+1, written without
alternating signs to keep the arithmetic in natural numbers. -/
def oddCofactor (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => oddCofactor p n + (p - 1) * p ^ (2 * n + 1)

theorem oddCofactor_identity {p : ℕ} (hp : 1 ≤ p) (n : ℕ) :
    (p + 1) * oddCofactor p n = p ^ (2 * n + 1) + 1 := by
  have hsub : p - 1 + 1 = p := by omega
  induction n with
  | zero => simp [oddCofactor]
  | succ n ih =>
    have he : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
    have hcoef : 1 + (p + 1) * (p - 1) = p ^ 2 := by
      nlinarith
    calc
      (p + 1) * oddCofactor p (n + 1) =
          (p ^ (2 * n + 1) + 1) + (p + 1) * ((p - 1) * p ^ (2 * n + 1)) := by
        rw [oddCofactor, Nat.mul_add, ih]
      _ = p ^ (2 * n + 1) * (1 + (p + 1) * (p - 1)) + 1 := by ring
      _ = p ^ (2 * n + 1) * p ^ 2 + 1 := by rw [hcoef]
      _ = p ^ ((2 * n + 1) + 2) + 1 := by
        rw [pow_add p (2 * n + 1) 2]
      _ = p ^ (2 * (n + 1) + 1) + 1 := by rw [he]

theorem oddCofactor_odd {p : ℕ} (hp : 1 ≤ p) (ho : p % 2 = 1)
    (n : ℕ) : oddCofactor p n % 2 = 1 := by
  have hs : (p - 1) % 2 = 0 := by omega
  induction n with
  | zero => simp [oddCofactor]
  | succ n ih => simp [oddCofactor, Nat.add_mod, Nat.mul_mod, hs, ih]

theorem oddCofactor_pos (p n : ℕ) : 0 < oddCofactor p n := by
  induction n with
  | zero => simp [oddCofactor]
  | succ n ih => simp only [oddCofactor]; omega

theorem oddCofactor_gt_one {p n : ℕ} (hp : 2 ≤ p) (hn : 0 < n) :
    1 < oddCofactor p n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h₁ := oddCofactor_pos p j
  have h₂ : 0 < (p - 1) * p ^ (2 * j + 1) :=
    Nat.mul_pos (by omega) (pow_pos (by omega) _)
  simp only [oddCofactor]
  omega

/-- An odd divisor greater than one rules out GPF two. -/
theorem gpf_ne_two_of_odd_divisor {n d : ℕ} (hn : 1 < n)
    (hd : d ∣ n) (hd1 : 1 < d) (hodd : d % 2 = 1) : gpf n ≠ 2 := by
  intro he
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
  have hle := (gpf_spec hn).2.2 r hr (dvd_trans hrd hd)
  have hr2 : r = 2 := by have := hr.two_le; omega
  subst r
  have := Nat.mod_eq_zero_of_dvd hrd
  omega

/-- No primality is needed for odd bases and odd exponents greater than one. -/
theorem odd_base_odd_exp_ne_two {p q : ℕ}
    (hp : 2 ≤ p) (hpo : p % 2 = 1) (hq : 3 ≤ q) (hqo : q % 2 = 1) :
    gpf (p ^ q + 1) ≠ 2 := by
  let n := q / 2
  have hqeq : q = 2 * n + 1 := by dsimp [n]; omega
  have hn : 0 < n := by omega
  have hident := oddCofactor_identity (p := p) (by omega) n
  have hd : oddCofactor p n ∣ p ^ q + 1 := by
    rw [hqeq, ← hident]
    exact dvd_mul_left _ _
  apply gpf_ne_two_of_odd_divisor _ hd (oddCofactor_gt_one hp hn)
    (oddCofactor_odd (by omega) hpo n)
  have : 0 < p ^ q := pow_pos (by omega) _
  omega

theorem exp_ne_two_direct {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    exp p q ≠ 2 := by
  by_cases hq2 : q = 2
  · subst q; exact square_output_ne_two hp
  rcases hp.eq_two_or_odd with hp2 | hpo
  · subst p
    intro he
    have hd : 2 ∣ 2 ^ q + 1 := by
      simpa [he] using (output_spec .exp Nat.prime_two hq).2.1
    have hq0 : q ≠ 0 := hq.ne_zero
    have hz := Nat.mod_eq_zero_of_dvd hd
    simp [Nat.add_mod, Nat.pow_mod, hq0] at hz
  · exact odd_base_odd_exp_ne_two hp.two_le hpo
      (by have := hq.two_le; omega) (hq.eq_two_or_odd.resolve_left hq2)

theorem proof_8_1 : t8_1 := by
  refine ⟨fun _ _ hp hq => exp_ne_two_direct hp hq, ?_⟩
  intro hs
  obtain ⟨⟨p, q⟩, he⟩ := hs (⟨2, Nat.prime_two⟩ : Prime)
  exact exp_ne_two_direct p.property q.property (congrArg Subtype.val he)

theorem proof_3_5 : t3_5 :=
  ⟨odd_add_closed, fun _ _ hp hq _ _ => exp_ne_two_direct hp hq,
    odd_mul_not_closed⟩

end PrimeGPF
