import Mathlib

/-!
Definitions 2.1–2.4 and elementary GPF infrastructure.
STATUS: proof scripts written, NOT compiled in the authoring environment.
The finite scan is deliberately simple, executable, and independent of a
particular mathlib greatest-prime-factor API. It is not a fast factorizer.
GPF(0)=GPF(1)=0 is a totalization only; substantive GPF lemmas require n>1.
-/
namespace PrimeGPF

abbrev Prime := {p : ℕ // Nat.Prime p}

def scan (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | b + 1 => if Nat.Prime (b + 1) ∧ b + 1 ∣ n then b + 1 else scan n b

def gpf (n : ℕ) : ℕ := scan n n

def IsGPF (n r : ℕ) : Prop :=
  Nat.Prime r ∧ r ∣ n ∧ ∀ s, Nat.Prime s → s ∣ n → s ≤ r

def Smooth (r n : ℕ) : Prop :=
  0 < n ∧ ∀ s, Nat.Prime s → s ∣ n → s ≤ r

theorem scan_le (n b : ℕ) : scan n b ≤ b := by
  induction b with
  | zero => simp [scan]
  | succ b ih =>
    simp only [scan]
    split_ifs <;> omega

theorem prime_le_scan {n s b : ℕ} (hs : Nat.Prime s)
    (hd : s ∣ n) (hb : s ≤ b) : s ≤ scan n b := by
  induction b with
  | zero => have := hs.two_le; omega
  | succ b ih =>
    simp only [scan]
    split_ifs with h
    · exact hb
    · apply ih
      by_contra hn
      have he : s = b + 1 := by omega
      exact h (he ▸ ⟨hs, hd⟩)

theorem scan_sound {n b : ℕ}
    (h : ∃ s, Nat.Prime s ∧ s ∣ n ∧ s ≤ b) :
    Nat.Prime (scan n b) ∧ scan n b ∣ n := by
  induction b with
  | zero =>
    obtain ⟨s, hs, _, hb⟩ := h
    have := hs.two_le
    omega
  | succ b ih =>
    simp only [scan]
    split_ifs with ht
    · exact ht
    · apply ih
      obtain ⟨s, hs, hd, hb⟩ := h
      refine ⟨s, hs, hd, ?_⟩
      by_contra hn
      have he : s = b + 1 := by omega
      exact ht (he ▸ ⟨hs, hd⟩)

theorem gpf_spec {n : ℕ} (hn : 1 < n) : IsGPF n (gpf n) := by
  obtain ⟨s, hs, hd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  have hle : s ≤ n := Nat.le_of_dvd (by omega) hd
  have hh := scan_sound (n := n) (b := n) ⟨s, hs, hd, hle⟩
  refine ⟨hh.1, hh.2, ?_⟩
  intro r hr hd'
  exact prime_le_scan hr hd' (Nat.le_of_dvd (by omega) hd')

theorem gpf_le (n : ℕ) : gpf n ≤ n := scan_le n n

theorem gpf_eq_of_spec {n r : ℕ} (hn : 1 < n) (h : IsGPF n r) :
    gpf n = r := by
  have hg := gpf_spec hn
  exact Nat.le_antisymm (h.2.2 _ hg.1 hg.2.1) (hg.2.2 _ h.1 h.2.1)

theorem gpf_eq_iff {n r : ℕ} (hn : 1 < n) :
    gpf n = r ↔ IsGPF n r := by
  constructor
  · intro h; simpa [h] using gpf_spec hn
  · exact gpf_eq_of_spec hn

theorem gpf_prime_self {n : ℕ} (hn : Nat.Prime n) : gpf n = n := by
  apply gpf_eq_of_spec hn.one_lt
  exact ⟨hn, dvd_refl n, fun _ _ hd => Nat.le_of_dvd hn.pos hd⟩

theorem gpf_eq_self_iff {n : ℕ} (hn : 1 < n) :
    gpf n = n ↔ Nat.Prime n := by
  constructor
  · intro h; simpa [h] using (gpf_spec hn).1
  · exact gpf_prime_self

theorem smooth_of_gpf {n : ℕ} (hn : 1 < n) : Smooth (gpf n) n :=
  ⟨by omega, (gpf_spec hn).2.2⟩

/-- Theorem 4.1 in its general arithmetic form; handles cofactor 1. -/
theorem gpf_fiber {n r : ℕ} (hn : 1 < n) (hr : Nat.Prime r) :
    gpf n = r ↔ ∃ s, 0 < s ∧ n = r * s ∧ Smooth r s := by
  constructor
  · intro h
    have hg : IsGPF n r := (gpf_eq_iff hn).mp h
    obtain ⟨s, hs⟩ := hg.2.1
    have hpos : 0 < s := by
      by_contra h
      have hs0 : s = 0 := by omega
      rw [hs0, Nat.mul_zero] at hs
      omega
    refine ⟨s, hpos, hs, hpos, ?_⟩
    intro t ht htd
    apply hg.2.2 t ht
    apply dvd_trans htd
    rw [hs]
    exact dvd_mul_left s r
  · rintro ⟨s, hs, he, hsm⟩
    apply gpf_eq_of_spec hn
    refine ⟨hr, ⟨s, he⟩, ?_⟩
    intro t ht hd
    rw [he] at hd
    rcases ht.dvd_mul.mp hd with htr | hts
    · exact Nat.le_of_dvd hr.pos htr
    · exact hsm.2 t ht hts

/-- Unique prime support implies a prime power, including the value 1. -/
theorem power_of_prime_support (r n : ℕ) (hr : Nat.Prime r)
    (hn : 0 < n) (h : ∀ s, Nat.Prime s → s ∣ n → s = r) :
    ∃ k, n = r ^ k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : n = 1
    · exact ⟨0, by simpa [he]⟩
    obtain ⟨s, hs, hd⟩ := Nat.exists_prime_and_dvd he
    have hsr := h s hs hd
    subst s
    obtain ⟨t, ht⟩ := hd
    have htpos : 0 < t := by
      by_contra hh
      have ht0 : t = 0 := by omega
      rw [ht0, Nat.mul_zero] at ht
      omega
    have htn : t < n := by have := hr.two_le; nlinarith
    obtain ⟨k, hk⟩ := ih t htn htpos (by
      intro s hs hd
      apply h s hs
      apply dvd_trans hd
      rw [ht]
      exact dvd_mul_left t r)
    exact ⟨k + 1, by rw [ht, hk, pow_succ]; ring⟩

theorem gpf_prime_power {r k : ℕ} (hr : Nat.Prime r) (hk : 0 < k) :
    gpf (r ^ k) = r := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hp : 0 < r ^ j := pow_pos hr.pos _
  have hn : 1 < r ^ (j + 1) := by rw [pow_succ]; have := hr.two_le; nlinarith
  apply gpf_eq_of_spec hn
  refine ⟨hr, ?_, ?_⟩
  · rw [pow_succ]; exact dvd_mul_left r (r ^ j)
  · intro s hs hd
    exact Nat.le_of_dvd hr.pos (hs.dvd_of_dvd_pow hd)

/-- Corollary 4.2, output two. -/
theorem gpf_eq_two_iff {n : ℕ} (hn : 1 < n) :
    gpf n = 2 ↔ ∃ k, 0 < k ∧ n = 2 ^ k := by
  constructor
  · intro he
    obtain ⟨k, hk⟩ := power_of_prime_support 2 n Nat.prime_two (by omega) (by
      intro s hs hd
      have hle := (gpf_spec hn).2.2 s hs hd
      have := hs.two_le
      omega)
    refine ⟨k, ?_, hk⟩
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero] at hk
    omega
  · rintro ⟨k, hk, rfl⟩; exact gpf_prime_power Nat.prime_two hk

inductive Op where
  | add | mul | exp
  deriving DecidableEq, Repr

def kernel : Op → ℕ → ℕ → ℕ
  | .add, p, q => p + q + 1
  | .mul, p, q => p * q + 1
  | .exp, p, q => p ^ q + 1

def output (o : Op) (p q : ℕ) : ℕ := gpf (kernel o p q)
abbrev add (p q : ℕ) := output .add p q
abbrev mul (p q : ℕ) := output .mul p q
abbrev exp (p q : ℕ) := output .exp p q

theorem kernel_gt_one (o : Op) {p q : ℕ} (hp : Nat.Prime p)
    (hq : Nat.Prime q) : 1 < kernel o p q := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  cases o with
  | add => simp only [kernel]; omega
  | mul => simp only [kernel]; nlinarith
  | exp => simp only [kernel]; have : 0 < p ^ q := pow_pos hp.pos q; omega

/-- Theorem 3.1, including maximality. -/
theorem output_spec (o : Op) {p q : ℕ} (hp : Nat.Prime p)
    (hq : Nat.Prime q) : IsGPF (kernel o p q) (output o p q) :=
  gpf_spec (kernel_gt_one o hp hq)

def operate (o : Op) (p q : Prime) : Prime :=
  ⟨output o p.val q.val, (output_spec o p.property q.property).1⟩

def leftTranslation (o : Op) (p : Prime) : Prime → Prime := operate o p
def diagonal (o : Op) (p : Prime) : Prime := operate o p p

def orbit {α : Type*} (f : α → α) (x : α) : ℕ → α
  | 0 => x
  | n + 1 => f (orbit f x n)

def EventuallyPeriodic {α : Type*} (f : α → α) (x : α) : Prop :=
  ∃ N d : ℕ, 0 < d ∧ ∀ n, N ≤ n → orbit f x (n + d) = orbit f x n

def Periodic {α : Type*} (f : α → α) (x : α) : Prop :=
  ∃ d : ℕ, 0 < d ∧ orbit f x d = x

def PrimitiveDivisor (r p k : ℕ) : Prop :=
  Nat.Prime r ∧ (p ^ k : ℕ) % r = 1 % r ∧
    ∀ j, 0 < j → j < k → p ^ j % r ≠ 1 % r

/-- Modular order specified without choosing a units representation. -/
def ExactOrder (p r k : ℕ) : Prop :=
  0 < k ∧ p ^ k % r = 1 % r ∧
    ∀ j, 0 < j → j < k → p ^ j % r ≠ 1 % r

end PrimeGPF
