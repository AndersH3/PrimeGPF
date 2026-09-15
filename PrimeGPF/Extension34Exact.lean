import PrimeGPF.Extension3Coprime
import PrimeGPF.Extension4Coprime
import PrimeGPF.Extension34Converse

/-!
# Extensions 3 and 4: exact arithmetic classifications

These theorems match the quotient-form classifications in the report.  The
separate asymptotic counts of the primitive exponent vectors remain outside
this file.
-/
namespace PrimeGPF

/-- Exact classification for the anchor-2 multiplicative fiber at output 5. -/
theorem extension3_exact_classification {q : ℕ} (hq : Nat.Prime q) :
    mul 2 q = 5 ↔
      q = 2 ∨
      ∃ α β : ℕ,
        0 < α ∧ 0 < β ∧ α % 2 = 1 ∧ Nat.Coprime α β ∧
        q = (3 ^ α * 5 ^ β - 1) / 2 := by
  constructor
  · intro hout
    by_cases hq2 : q = 2
    · exact Or.inl hq2
    · right
      obtain ⟨α, β, hα, hβ, hαodd, hfac⟩ :=
        extension3_exponent_structure hq hout hq2
      have hcop := extension3_exponents_coprime hq hα hβ hαodd hfac
      have hqform : q = (3 ^ α * 5 ^ β - 1) / 2 := by
        omega
      exact ⟨α, β, hα, hβ, hαodd, hcop, hqform⟩
  · rintro (hq2 | ⟨α, β, hα, hβ, hαodd, hcop, hqform⟩)
    · subst q
      norm_num [mul, output, kernel, gpf, scan]
    · let N := 3 ^ α * 5 ^ β
      have hNmod2 : N % 2 = 1 := by
        dsimp [N]
        norm_num [Nat.mul_mod, Nat.pow_mod]
      have hNpos : 0 < N := by
        dsimp [N]
        positivity
      have hN1 : 1 ≤ N := by omega
      have h2div : 2 ∣ N - 1 := by
        apply Nat.dvd_of_mod_eq_zero
        omega
      have hcancel : 2 * ((N - 1) / 2) = N - 1 :=
        Nat.mul_div_cancel' h2div
      have hsubadd : N - 1 + 1 = N := Nat.sub_add_cancel hN1
      have hfac : 2 * q + 1 = 3 ^ α * 5 ^ β := by
        dsimp [N] at hcancel hsubadd hNmod2 hNpos hN1 h2div ⊢
        rw [hqform]
        omega
      exact extension3_kernel_factorization_implies_output_five hq hβ hfac

/-- Exact classification for the anchor-3 multiplicative fiber at output 5. -/
theorem extension4_exact_classification {q : ℕ} (hq : Nat.Prime q) :
    mul 3 q = 5 ↔
      ∃ α β : ℕ,
        0 < α ∧ 0 < β ∧ α % 2 = 1 ∧ β % 2 = 1 ∧
        Nat.Coprime α β ∧
        q = (2 ^ α * 5 ^ β - 1) / 3 := by
  constructor
  · intro hout
    obtain ⟨α, β, hα, hβ, hαodd, hβodd, hcop, hfac⟩ :=
      extension4_output_five_primitive_structure hq hout
    have hqform : q = (2 ^ α * 5 ^ β - 1) / 3 := by
      omega
    exact ⟨α, β, hα, hβ, hαodd, hβodd, hcop, hqform⟩
  · rintro ⟨α, β, hα, hβ, hαodd, hβodd, hcop, hqform⟩
    let N := 2 ^ α * 5 ^ β
    have h2pow := extension_two_pow_mod_three_of_odd hαodd
    have h5pow := five_pow_mod_three_of_odd hβodd
    have hNmod3 : N % 3 = 1 := by
      dsimp [N]
      norm_num [Nat.mul_mod, h2pow, h5pow]
    have hNpos : 0 < N := by
      dsimp [N]
      positivity
    have hN1 : 1 ≤ N := by omega
    have h3div : 3 ∣ N - 1 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    have hcancel : 3 * ((N - 1) / 3) = N - 1 :=
      Nat.mul_div_cancel' h3div
    have hsubadd : N - 1 + 1 = N := Nat.sub_add_cancel hN1
    have hfac : 3 * q + 1 = 2 ^ α * 5 ^ β := by
      dsimp [N] at hcancel hsubadd hNmod3 hNpos hN1 h3div ⊢
      rw [hqform]
      omega
    exact extension4_kernel_factorization_implies_output_five hq hβ hfac

end PrimeGPF
