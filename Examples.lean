import PrimeGPF

/-!
Executable counterparts of the computational appendix.
Use only modest bounds: the transparent GPF scan is intentionally slow.
These computations are demonstrations, not proofs of universal statements.
-/
namespace PrimeGPF

def primesUpTo (B : ℕ) : List ℕ :=
  (List.range (B + 1)).filter (fun p => decide (Nat.Prime p))

def operationTable (o : Op) (B : ℕ) : List (List ℕ) :=
  (primesUpTo B).map (fun p => (primesUpTo B).map (output o p))

def unorderedFiber (o : Op) (r B : ℕ) : List (ℕ × ℕ) :=
  (primesUpTo B).flatMap (fun p =>
    ((primesUpTo B).filter (fun q => decide (p ≤ q ∧ output o p q = r))).map
      (fun q => (p, q)))

def anchoredOrbit (o : Op) (a x steps : ℕ) : List ℕ :=
  (List.range (steps + 1)).map (orbit (output o a) x)

#eval operationTable .add 7
#eval operationTable .mul 7
#eval operationTable .exp 3
#eval unorderedFiber .add 2 13
#eval unorderedFiber .mul 2 13
#eval anchoredOrbit .add 2 2 8

end PrimeGPF
