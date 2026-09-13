import PrimeGPF.Core

/-!
Statement inventory for ALL 39 numbered results (3.1–9.8).
A `def ... : Prop` names a proposition; it DOES NOT prove or assume it.
See COVERAGE.md for proof-script coverage and explicit corrections.
No unproved proposition in this file is installed as an axiom.
-/
namespace PrimeGPF
namespace Claims

def Comm (o : Op) : Prop := ∀ p q, Nat.Prime p → Nat.Prime q →
  output o p q = output o q p

def Assoc (o : Op) : Prop := ∀ p q r,
  Nat.Prime p → Nat.Prime q → Nat.Prime r →
  output o (output o p q) r = output o p (output o q r)

def Identity (o : Op) : Prop := ∃ e, Nat.Prime e ∧
  ∀ p, Nat.Prime p → output o e p = p ∧ output o p e = p

def OddClosed (o : Op) : Prop := ∀ p q,
  Nat.Prime p → Nat.Prime q → p ≠ 2 → q ≠ 2 → output o p q ≠ 2

def LeftCancel (o : Op) : Prop := ∀ p q r,
  Nat.Prime p → Nat.Prime q → Nat.Prime r →
  output o p q = output o p r → q = r

def Distrib (o v : Op) : Prop := ∀ p q r,
  Nat.Prime p → Nat.Prime q → Nat.Prime r →
  output o p (output v q r) = output v (output o p q) (output o p r)

def MixedAssoc (o v : Op) : Prop := ∀ p q r,
  Nat.Prime p → Nat.Prime q → Nat.Prime r →
  output v (output o p q) r = output o p (output v q r)

def MonoLeft (o : Op) : Prop := ∀ p q r,
  Nat.Prime p → Nat.Prime q → Nat.Prime r → p ≤ q →
  output o p r ≤ output o q r

def MonoRight (o : Op) : Prop := ∀ p q r,
  Nat.Prime p → Nat.Prime q → Nat.Prime r → p ≤ q →
  output o r p ≤ output o r q

def t3_1 : Prop := ∀ o p q, Nat.Prime p → Nat.Prime q →
  Nat.Prime (output o p q) ∧ output o p q ∣ kernel o p q

def t3_2 : Prop := Comm .add ∧ Comm .mul ∧ ¬ Comm .exp

def t3_3 : Prop := ¬ Assoc .add ∧ ¬ Assoc .mul ∧ ¬ Assoc .exp

def t3_4 : Prop :=
  (∀ p q, Nat.Prime p → Nat.Prime q → mul p q ≠ p ∧ mul p q ≠ q) ∧
  (∀ p, Nat.Prime p → add p p ≠ p) ∧
  (∀ p q, Nat.Prime p → Nat.Prime q → exp p q ≠ p) ∧
  (∀ o, ¬ Identity o)

def t3_5 : Prop := OddClosed .add ∧ OddClosed .exp ∧ ¬ OddClosed .mul

def t3_6 : Prop := ¬ LeftCancel .add ∧ ¬ LeftCancel .mul ∧
  ¬ Distrib .mul .add ∧ ¬ Distrib .add .mul

def t3_7 : Prop := ¬ MixedAssoc .add .mul ∧
  ¬ MixedAssoc .add .exp ∧ ¬ MixedAssoc .mul .exp

def t3_8 : Prop := ∀ o, ¬ MonoLeft o ∧ ¬ MonoRight o

def t4_1 : Prop := ∀ o p q r,
  Nat.Prime p → Nat.Prime q → Nat.Prime r →
  (output o p q = r ↔ ∃ s, 0 < s ∧ kernel o p q = r * s ∧ Smooth r s)

def t4_2 : Prop := ∀ o p q, Nat.Prime p → Nat.Prime q →
  (output o p q = kernel o p q ↔ Nat.Prime (kernel o p q)) ∧
  (output o p q = 2 ↔ ∃ k, 0 < k ∧ kernel o p q = 2 ^ k)

def t4_3 : Prop :=
  (∀ p q, Nat.Prime p → Nat.Prime q →
    (add p q = 2 ↔ ∃ m, 3 ≤ m ∧
      ((p = 2 ∧ q + 3 = 2 ^ m) ∨ (q = 2 ∧ p + 3 = 2 ^ m)))) ∧
  (∀ p q, Nat.Prime p → Nat.Prime q →
    (mul p q = 2 ↔ ∃ m, 0 < m ∧ p * q + 1 = 2 ^ m)) ∧
  (∀ p q, Nat.Prime p → Nat.Prime q → mul p q = 2 →
    p ≠ 2 ∧ q ≠ 2 ∧ p % 4 ≠ q % 4) ∧
  (∀ p q, Nat.Prime p → Nat.Prime q → p ≠ 2 → q ≠ 2 →
    (add p q = 3 ↔ ∃ m, 2 ≤ m ∧ p + q + 1 = 3 ^ m)) ∧
  (∀ p q, Nat.Prime p → Nat.Prime q → 3 < p → 3 < q → add p q = 3 →
    p % 6 = 1 ∧ q % 6 = 1) ∧
  (∀ q, Nat.Prime q → (mul 2 q = 3 ↔ ∃ m, 2 ≤ m ∧ 2 * q + 1 = 3 ^ m))

/-- Modular inverse is represented by an explicit inverse witness. -/
def t5_1 : Prop := ∀ p q, Nat.Prime p → Nat.Prime q →
  let r := mul p q
  let s := add p q
  ((p * q + 1) % r = 0) ∧
  (∃ u, p * u % r = 1 ∧ (q + u) % r = 0) ∧
  (∃ v, q * v % r = 1 ∧ (p + v) % r = 0) ∧
  (p + q + 1) % s = 0

def t5_2 : Prop := ∀ p, Nat.Prime p →
  mul p p % 4 = 1 ∧ PrimitiveDivisor (mul p p) p 4

def t5_3 : Prop :=
  (∀ p : Prime, ∀ n, 0 < n → (orbit (diagonal .mul) p n).val % 4 = 1) ∧
  (∀ p : Prime, Periodic (diagonal .mul) p → p.val % 4 = 1)

/-- Finite, standard quadratic character, used to avoid API-specific symbols. -/
def quadraticCharacter (r a : ℕ) : ℤ :=
  if a % r = 0 then 0
  else if ∃ x : Fin r, x.val ^ 2 % r = a % r then 1 else -1

def t5_4 : Prop := ∀ p q, Nat.Prime p → Nat.Prime q →
  let r := mul p q
  r ≠ 2 →
  quadraticCharacter r p * quadraticCharacter r q = quadraticCharacter r (r - 1) ∧
  (r % 4 = 1 → quadraticCharacter r p = quadraticCharacter r q) ∧
  (r % 4 = 3 →
    ((quadraticCharacter r p = 1 ∧ quadraticCharacter r q = -1) ∨
     (quadraticCharacter r p = -1 ∧ quadraticCharacter r q = 1)))

/-- FALSE as printed: retained for explicit refutation, not silently repaired. -/
def t5_5_original : Prop := ∀ p q m,
  Nat.Prime p → Nat.Prime q → 1 ≤ m →
  let r := mul p q
  q % r = p ^ (2 ^ m - 1) % r →
  ExactOrder p r (2 ^ (m + 1)) ∧ r % (2 ^ (m + 1)) = 1 ∧
  PrimitiveDivisor r p (2 ^ (m + 1)) ∧ r ∣ p ^ (2 ^ m) + 1

/-- Proposed corrected theorem: adds r ≠ 2. -/
def t5_5_corrected : Prop := ∀ p q m,
  Nat.Prime p → Nat.Prime q → 1 ≤ m →
  let r := mul p q
  r ≠ 2 → q % r = p ^ (2 ^ m - 1) % r →
  ExactOrder p r (2 ^ (m + 1)) ∧ r % (2 ^ (m + 1)) = 1 ∧
  PrimitiveDivisor r p (2 ^ (m + 1)) ∧ r ∣ p ^ (2 ^ m) + 1

def t5_6 : Prop := ∀ p q, Nat.Prime p → Nat.Prime q → p ≠ 2 → q ≠ 2 →
  (p % 4 = q % 4 → mul p q ≠ 2) ∧ (mul p q = 2 → p % 4 ≠ q % 4)

noncomputable def primeCount (x : ℕ) : ℕ := by
  classical
  exact ((Finset.range (x + 1)).filter Nat.Prime).card

noncomputable def apCount (r c x : ℕ) : ℕ := by
  classical
  exact ((Finset.range (x + 1)).filter (fun q => Nat.Prime q ∧ q % r = c % r)).card

noncomputable def divisorCount (o : Op) (a r x : ℕ) : ℕ := by
  classical
  exact ((Finset.range (x + 1)).filter
    (fun q => Nat.Prime q ∧ r ∣ kernel o a q)).card

noncomputable def fiberCount (o : Op) (a r x : ℕ) : ℕ := by
  classical
  exact ((Finset.range (x + 1)).filter
    (fun q => Nat.Prime q ∧ output o a q = r)).card

noncomputable def pairCount (o : Op) (r x : ℕ) : ℕ := by
  classical
  exact (((Finset.range (x + 1)) ×ˢ (Finset.range (x + 1))).filter
    (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ output o pq.1 pq.2 = r)).card

noncomputable def smoothCount (r x : ℕ) : ℕ := by
  classical
  exact ((Finset.range (x + 1)).filter (Smooth r)).card

/-- PNT-AP as a ratio limit on natural cutoffs. -/
def APAsymptotic (r c : ℕ) : Prop :=
  Filter.Tendsto
    (fun x : ℕ => (apCount r c x : ℝ) /
      ((x : ℝ) / (((r : ℝ) - 1) * Real.log (x : ℝ))))
    Filter.atTop (nhds 1)

def t6_1 : Prop := ∀ a r, Nat.Prime a → Nat.Prime r → r ≠ 2 →
  (a ≠ r → ∃ c, 0 < c ∧ c < r ∧
    (∀ q, r ∣ a * q + 1 ↔ q % r = c) ∧
    (∀ x, divisorCount .mul a r x = apCount r c x) ∧ APAsymptotic r c) ∧
  ((a + 1) % r ≠ 0 → ∃ c, 0 < c ∧ c < r ∧
    (∀ q, r ∣ a + q + 1 ↔ q % r = c) ∧
    (∀ x, divisorCount .add a r x = apCount r c x) ∧ APAsymptotic r c) ∧
  ((a + 1) % r = 0 → ∀ q, Nat.Prime q → (r ∣ a + q + 1 ↔ q = r))

/-- Fixed-anchor interpretation: constants may depend on the fixed a and r. -/
def PolylogFiber (o : Op) (a r : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ x, N ≤ x →
    (fiberCount o a r x : ℝ) ≤ C * (Real.log (x : ℝ)) ^ primeCount r

noncomputable def smoothBoxBound (r x : ℕ) : ℕ := by
  classical
  exact ∏ l ∈ (Finset.range (r + 1)).filter Nat.Prime,
    (1 + ⌊Real.log (x : ℝ) / Real.log (l : ℝ)⌋₊)

/-- The displayed r-only implied constant: thresholds may depend on a. -/
def UniformPolylogFibers (r : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ a, Nat.Prime a → ∃ N : ℕ, ∀ x, N ≤ x →
    (fiberCount .add a r x : ℝ) ≤ C * (Real.log (x : ℝ)) ^ primeCount r ∧
    (fiberCount .mul a r x : ℝ) ≤ C * (Real.log (x : ℝ)) ^ primeCount r

def SmoothPolylog (r : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ x, N ≤ x →
    (smoothCount r x : ℝ) ≤ C * (Real.log (x : ℝ)) ^ primeCount r

def t6_2 : Prop :=
  (∀ r, Nat.Prime r → UniformPolylogFibers r ∧ SmoothPolylog r) ∧
  (∀ r x, 2 ≤ r → 1 ≤ x → smoothCount r x ≤ smoothBoxBound r x)

def RelativeZero (o : Op) (a r : ℕ) : Prop :=
  Filter.Tendsto (fun x : ℕ => (fiberCount o a r x : ℝ) / divisorCount o a r x)
    Filter.atTop (nhds 0)

def PairZero (o : Op) (r : ℕ) : Prop :=
  Filter.Tendsto (fun x : ℕ => (pairCount o r x : ℝ) / (primeCount x : ℝ) ^ 2)
    Filter.atTop (nhds 0)

def t6_3 : Prop := ∀ r, Nat.Prime r → r ≠ 2 →
  (∀ a, Nat.Prime a →
    (a ≠ r → RelativeZero .mul a r) ∧
    ((a + 1) % r ≠ 0 → RelativeZero .add a r)) ∧
  PairZero .mul r ∧ PairZero .add r

def t6_4 : Prop :=
  (∀ p, Nat.Prime p → ∀ B, ∃ q, Nat.Prime q ∧ B < add p q) ∧
  (∀ p, Nat.Prime p → ∀ B, ∃ q, Nat.Prime q ∧ B < mul p q) ∧
  (∀ q, Nat.Prime q → ∀ B, ∃ p, Nat.Prime p ∧ B < exp p q)

def t7_1 : Prop := ∀ a, Nat.Prime a →
  (∀ q, Nat.Prime q → (add a q = q ↔
    q ∣ a + 1 ∧ Smooth q ((a + 1) / q + 1))) ∧
  Set.Finite {q | Nat.Prime q ∧ add a q = q} ∧
  {q | Nat.Prime q ∧ add a q = q} ⊆ {q | Nat.Prime q ∧ q ∣ a + 1} ∧
  Set.ncard {q | Nat.Prime q ∧ add a q = q} ≤
    Set.ncard {q | Nat.Prime q ∧ q ∣ a + 1}

def t7_2 : Prop := ∀ a q, Nat.Prime a → Nat.Prime q →
  mul a q ≠ a ∧ mul a q ≠ q

def t7_3 : Prop :=
  (∀ q, Nat.Prime q → (add 2 q = q ↔ q = 3)) ∧
  (add 2 2 = 5 ∧ add 2 5 = 2) ∧
  (∀ q, Nat.Prime q → (∃ k, q + 3 = 2 ^ k) → add 2 q = 2)

def t7_4 : Prop := ∀ a q, Nat.Prime a → Nat.Prime q →
  (add a q = a ↔ a ∣ q + 1 ∧ Smooth a ((q + 1) / a + 1))

def t7_5 : Prop := ∀ (f : Prime → Prime) (x : Prime),
  (∃ S : Finset Prime, ∀ n, orbit f x n ∈ S) → EventuallyPeriodic f x

def t8_1 : Prop :=
  (∀ p q, Nat.Prime p → Nat.Prime q → exp p q ≠ 2) ∧
  ¬ Function.Surjective (fun pq : Prime × Prime => operate .exp pq.1 pq.2)

def t8_2 : Prop := ∀ p, Nat.Prime p → exp p 2 % 4 = 1

def t8_3 : Prop := ∀ p q, Nat.Prime p → Nat.Prime q → q ≠ 2 →
  (p, q) ≠ (2, 3) →
  (∃ r, Nat.Prime r ∧ r ∣ p ^ q + 1 ∧ r % (2 * q) = 1) ∧
  2 * q + 1 ≤ exp p q

def t8_4 : Prop := ∀ p q, Nat.Prime p → Nat.Prime q →
  exp p q ≠ p ∧ (exp p q = q ↔ p = 2 ∧ q = 3)

def t8_5 : Prop :=
  (∀ a : Prime, a.val ≠ 2 →
    (∀ q : Prime, q.val < (operate .exp a q).val) ∧
    (∀ x : Prime, StrictMono (fun n => (orbit (operate .exp a) x n).val)) ∧
    (∀ x : Prime, ∀ B, ∃ n, B < (orbit (operate .exp a) x n).val) ∧
    (∀ x : Prime, ¬ Periodic (operate .exp a) x)) ∧
  (exp 2 3 = 3) ∧
  (∀ q, Nat.Prime q → q ≠ 3 → q < exp 2 q) ∧
  (∀ x : Prime, Periodic (operate .exp ⟨2, Nat.prime_two⟩) x ↔ x.val = 3)

def t9_1 : Prop := ∀ p, Nat.Prime p → add p p = mul p 2 ∧ exp p 2 = mul p p

def t9_2 : Prop := ∀ p, Nat.Prime p →
  (add p 2 = mul p 2 → add p 2 = 5) ∧
  (add p 2 = exp p 2 → add p 2 = 5) ∧
  (mul p 2 = exp p 2 → mul p 2 = 5)

def t9_3 : Prop := ∀ q, Nat.Prime q → 3 < q →
  add 2 q < exp 2 q ∧ mul 2 q ≤ exp 2 q ∧
  (¬ Nat.Prime (2 * q + 1) → mul 2 q < exp 2 q)

/-- The unknown q is a residue, NOT required to be a prime here. -/
def t9_4 : Prop := ∀ p r, Nat.Prime p → Nat.Prime r → r ≠ p →
  ((∃ q : ℕ, r ∣ p + q + 1 ∧ r ∣ p * q + 1) ↔ r ∣ p ^ 2 + p - 1) ∧
  (∀ q₁ q₂ : ℕ, r ∣ p + q₁ + 1 → r ∣ p + q₂ + 1 → q₁ % r = q₂ % r) ∧
  (∀ q, Nat.Prime q → add p q = r → mul p q = r → r ∣ p ^ 2 + p - 1)

def commonOutputs (p : ℕ) : Set ℕ :=
  {r | Nat.Prime r ∧ ∃ q, Nat.Prime q ∧ add p q = r ∧ mul p q = r}

def tripleOutputs (p : ℕ) : Set ℕ :=
  {r | Nat.Prime r ∧ ∃ q, Nat.Prime q ∧ add p q = r ∧ mul p q = r ∧ exp p q = r}

def t9_5 : Prop := ∀ p, Nat.Prime p →
  Set.Finite (commonOutputs p) ∧
  commonOutputs p ⊆ {r | Nat.Prime r ∧ r ∣ p ^ 2 + p - 1} ∧
  Set.Finite (tripleOutputs p) ∧
  tripleOutputs p ⊆ {r | Nat.Prime r ∧ r ∣ p ^ 2 + p - 1}

def t9_6 : Prop := ∀ p q r, Nat.Prime p → Nat.Prime q → Nat.Prime r →
  r ∣ p + q + 1 → r ∣ p * q + 1 →
  r ∣ p ^ 2 + p - 1 ∧ r ∣ q ^ 2 + q - 1 ∧
  (r ≠ 2 → r ≠ 5 → (∃ x : ℕ, x ^ 2 % r = 5 % r) ∧
    (r % 5 = 1 ∨ r % 5 = 4))

def t9_7 : Prop := ∀ p q r, Nat.Prime p → Nat.Prime q →
  mul p q = r → exp p q = r → p ^ (q - 1) % r = q % r

def t9_8 : Prop := ∀ p q r, Nat.Prime p → Nat.Prime q →
  add p q = r → mul p q = r → exp p q = r →
  r ∣ p ^ 2 + p - 1 ∧ p ^ (q - 1) % r = q % r ∧ (p + q + 1) % r = 0 ∧
  (r ≠ 2 → r ≠ 5 → r % 5 = 1 ∨ r % 5 = 4)

end Claims
end PrimeGPF
