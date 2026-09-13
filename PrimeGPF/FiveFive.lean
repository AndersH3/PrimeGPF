import PrimeGPF.Orders

/-!
Corrected official version of theorem 5.5.

The source statement without the odd-output hypothesis is false at the
exceptional output `r = 2`.  `Claims.t5_5_original` is retained in
`Statements.lean` only as a historical object for the verified counterexample
and refutation.  The numbered theorem 5.5 used by the formalization is the
corrected statement `Claims.t5_5`, definitionally equal to
`Claims.t5_5_corrected`.
-/
namespace PrimeGPF

namespace Claims

/--
Correct theorem 5.5: the dyadic-order conclusion requires the output
`r = mul p q` to be different from `2`.
-/
def t5_5 : Prop := t5_5_corrected

end Claims

open Claims

/-- Complete compiler-checkable proof of the corrected theorem 5.5. -/
theorem proof_5_5 : t5_5 := proof_5_5_corrected

end PrimeGPF
