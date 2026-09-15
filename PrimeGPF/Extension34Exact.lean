import PrimeGPF.Extension3Coprime
import PrimeGPF.Extension4Coprime
import PrimeGPF.Extension34Converse
import PrimeGPF.Extension34ResidueHelpers

/-!
# Extensions 3 and 4: exact arithmetic classifications

These theorems match the quotient-form classifications in the report.  Their
proofs are intentionally split into two conceptual stages:

1. the structural/coprimality files produce a kernel factorisation and the
   required parity conditions;
2. this file packages that information into the exact quotient formulas, and
   conversely reconstructs the kernel equation from those formulas.

The elementary quotient reconstruction and residue facts are delegated to
`Extension34ResidueHelpers`, avoiding duplicated `Nat.mul_div_cancel'` blocks.
The separate asymptotic counts of primitive exponent vectors remain outside
this file.
-/
namespace PrimeGPF

/-- Exact classification for the anchor-2 multiplicative fiber at output 5.
The exceptional prime input `q = 2` is separated from the primitive exponent
family. -/
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
      have h3mod : 3 ^ α % 2 = 1 := by simp [Nat.pow_mod]
      have h5mod : 5 ^ β % 2 = 1 := by simp [Nat.pow_mod]
      have hNmod : N % 2 = 1 := by
        dsimp [N]
        exact odd_product_mod_two h3mod h5mod
      have hN1 : 1 ≤ N := by
        dsimp [N]
        exact one_le_mul
          (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3))
          (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 5))
      have hdiv : 2 ∣ N - 1 := by
        apply Nat.dvd_of_mod_eq_zero
        omega
      have hqformN : q = (N - 1) / 2 := by
        simpa [N] using hqform
      have hfacN : 2 * q + 1 = N :=
        quotient_sub_one_reconstruct hN1 hdiv hqformN
      have hfac : 2 * q + 1 = 3 ^ α * 5 ^ β := by
        simpa [N] using hfacN
      exact extension3_kernel_factorization_implies_output_five hq hβ hfac

/-- Exact classification for the anchor-3 multiplicative fiber at output 5.
Both primitive exponents are positive and odd. -/
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
    have h2mod : 2 ^ α % 3 = 2 :=
      extension_two_pow_mod_three_of_odd hαodd
    have h5mod : 5 ^ β % 3 = 2 := five_pow_mod_three_odd β hβodd
    have hNmod : N % 3 = 1 := by
      dsimp [N]
      norm_num [Nat.mul_mod, h2mod, h5mod]
    have hN1 : 1 ≤ N := by
      dsimp [N]
      exact one_le_mul
        (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2))
        (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 5))
    have hdiv : 3 ∣ N - 1 := by
      apply Nat.dvd_of_mod_eq_zero
      omega
    have hqformN : q = (N - 1) / 3 := by
      simpa [N] using hqform
    have hfacN : 3 * q + 1 = N :=
      quotient_sub_one_reconstruct hN1 hdiv hqformN
    have hfac : 3 * q + 1 = 2 ^ α * 5 ^ β := by
      simpa [N] using hfacN
    exact extension4_kernel_factorization_implies_output_five hq hβ hfac

end PrimeGPF
