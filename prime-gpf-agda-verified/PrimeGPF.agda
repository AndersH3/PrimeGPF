{-# OPTIONS --safe #-}

module PrimeGPF where

------------------------------------------------------------------------
-- A computational Agda translation of the PARI/GP prime-GPF routines.
--
-- Type hierarchy:
--
--     P  ⊆  N  ⊆  ℕ
--
-- where
--   N = natural numbers > 1
--   P = prime elements of N
--
-- The important consequence is that all three GPF magma operations have
-- type P → P → P.  Primality of results is therefore certified by the
-- type, not checked by callers after the fact.
------------------------------------------------------------------------

open import Data.Bool.Base using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; map; take; concatMap; upTo)
import Data.List.Relation.Unary.All as All
open import Data.Nat.Base
  using
    ( ℕ; zero; suc
    ; NonZero; NonTrivial
    ; _+_; _*_; _^_; _<_; _<ᵇ_
    ; n>1⇒nonTrivial
    ; nonTrivial⇒nonZero
    ; nonTrivial⇒≢1
    ; >-nonZero⁻¹
    )
open import Data.Nat.Primality
  using (Prime; prime?; prime⇒nonZero; prime⇒nonTrivial)
open import Data.Nat.Primality.Factorisation
  using (PrimeFactorisation; factorise)
open PrimeFactorisation
open import Data.Nat.Properties
  using
    ( _≟_
    ; +-comm
    ; m<m+n
    ; m*n≢0
    ; m^n≢0
    )
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; subst)
open import Relation.Nullary.Decidable using (yes; no)

------------------------------------------------------------------------
-- 1. Certified domains
------------------------------------------------------------------------

-- N is literally a subtype of the built-in naturals: the naturals > 1.
N : Set
N = Σ ℕ NonTrivial

-- Forget the certificate that an N is > 1.
N→ℕ : N → ℕ
N→ℕ = proj₁

-- Recover the NonTrivial certificate carried by N.
N-nonTrivial : (n : N) → NonTrivial (N→ℕ n)
N-nonTrivial = proj₂

-- Smart constructor for N.
mkN : (n : ℕ) → NonTrivial n → N
mkN n hn = n , hn

-- P is literally a subtype of N: those elements whose underlying natural
-- number is prime.
P : Set
P = Σ N (λ n → Prime (N→ℕ n))

-- Forget P's primality certificate but retain membership of N.
P→N : P → N
P→N = proj₁

-- Forget both certificates and expose the underlying natural number.
P→ℕ : P → ℕ
P→ℕ p = N→ℕ (P→N p)

-- Recover the primality certificate carried by P.
P-prime : (p : P) → Prime (P→ℕ p)
P-prime = proj₂

-- Smart constructor for P from a certified prime natural.  The N-layer
-- certificate is derived from the primality proof, so it cannot disagree
-- with the prime certificate.
mkP : (p : ℕ) → Prime p → P
mkP p hp = (p , prime⇒nonTrivial hp) , hp

-- Every P is non-zero.
P-nonZero : (p : P) → NonZero (P→ℕ p)
P-nonZero p = prime⇒nonZero (P-prime p)

------------------------------------------------------------------------
-- 2. Greatest prime factor, N → P
------------------------------------------------------------------------

-- Maximum of two certified primes, comparing their underlying naturals.
-- In the equality case the left argument is retained.
maxP : P → P → P
maxP p q with P→ℕ p <ᵇ P→ℕ q
... | true  = q
... | false = p

-- Select the greatest certified prime from a non-empty prime factor list.
-- The All proof supplies primality certificates for every list element.
maxPrimeNonEmpty :
  (p : ℕ) → (ps : List ℕ) →
  Prime p → All.All Prime ps → P
maxPrimeNonEmpty p [] hp _ = mkP p hp
maxPrimeNonEmpty p (q ∷ qs) hp hqs =
  maxP
    (mkP p hp)
    (maxPrimeNonEmpty
      q qs
      (All.head hqs)
      (All.tail hqs))

-- Extract the greatest prime from a certified factorisation.  The empty
-- factor list can only represent 1; n ≢ 1 therefore eliminates that case.
gpfFromFactorisation :
  ∀ {n : ℕ} → PrimeFactorisation n → n ≢ 1 → P
gpfFromFactorisation
  (record
    { factors = []
    ; isFactorisation = eq
    ; factorsPrime = _
    })
  n≢1 =
  ⊥-elim (n≢1 eq)
gpfFromFactorisation
  (record
    { factors = p ∷ ps
    ; isFactorisation = _
    ; factorsPrime = hps
    })
  _ =
  maxPrimeNonEmpty
    p ps
    (All.head hps)
    (All.tail hps)

-- PARI/GP:
--
-- greatestPrimeFactor(n) = {
--   my(F = factor(n));
--   F[matsize(F)[1], 1]
-- };
--
-- Here the input is N, not arbitrary ℕ, so 0 and 1 are impossible.  The
-- standard library factoriser produces prime certificates for all factors;
-- selecting their maximum therefore returns P directly.
greatestPrimeFactor : N → P
greatestPrimeFactor (n , hn) =
  gpfFromFactorisation (factorise n) nonTrivial⇒≢1
  where
  instance
    n-nonTrivial : NonTrivial n
    n-nonTrivial = hn

    n-nonZero : NonZero n
    n-nonZero = nonTrivial⇒nonZero n

------------------------------------------------------------------------
-- 3. Building N values of the form a + 1
------------------------------------------------------------------------

-- If a is non-zero, then a + 1 > 1, hence a + 1 belongs to N.
--
-- We prove this through the standard-library order lemmas rather than by
-- relying on normalization of addition, so the definition is stable for
-- symbolic a.
nonZeroPlusOne→N : (a : ℕ) → NonZero a → N
nonZeroPlusOne→N a ha =
  mkN
    (a + 1)
    (n>1⇒nonTrivial
      (subst
        (λ x → 1 < x)
        (+-comm 1 a)
        (m<m+n 1 (>-nonZero⁻¹ a))))
  where
  instance
    a-nonZero : NonZero a
    a-nonZero = ha


------------------------------------------------------------------------
-- 4. Certified non-zero intermediate expressions
------------------------------------------------------------------------

-- p + q is non-zero because p itself is non-zero.
plusBaseNonZero : (p q : P) → NonZero (P→ℕ p + P→ℕ q)
plusBaseNonZero ((zero , ()) , _) q
plusBaseNonZero ((suc p , _) , _) q = _

-- p * q is non-zero because both primes are non-zero.
timesBaseNonZero : (p q : P) → NonZero (P→ℕ p * P→ℕ q)
timesBaseNonZero p q =
  m*n≢0 (P→ℕ p) (P→ℕ q)
  where
  instance
    p-nonZero : NonZero (P→ℕ p)
    p-nonZero = P-nonZero p

    q-nonZero : NonZero (P→ℕ q)
    q-nonZero = P-nonZero q

-- p ^ q is non-zero because the prime base p is non-zero.
powerBaseNonZero : (p q : P) → NonZero (P→ℕ p ^ P→ℕ q)
powerBaseNonZero p q =
  m^n≢0 (P→ℕ p) (P→ℕ q)
  where
  instance
    p-nonZero : NonZero (P→ℕ p)
    p-nonZero = P-nonZero p

------------------------------------------------------------------------
-- 5. The three GPF operations, each closed on P
------------------------------------------------------------------------

-- PARI/GP:
--   gpfPlus(p,q) = greatestPrimeFactor(p + q + 1);
gpfPlus : P → P → P
gpfPlus p q =
  greatestPrimeFactor
    (nonZeroPlusOne→N
      (P→ℕ p + P→ℕ q)
      (plusBaseNonZero p q))

-- PARI/GP:
--   gpfTimes(p,q) = greatestPrimeFactor(p*q + 1);
gpfTimes : P → P → P
gpfTimes p q =
  greatestPrimeFactor
    (nonZeroPlusOne→N
      (P→ℕ p * P→ℕ q)
      (timesBaseNonZero p q))

-- PARI/GP:
--   gpfPower(p,q) = greatestPrimeFactor(p^q + 1);
gpfPower : P → P → P
gpfPower p q =
  greatestPrimeFactor
    (nonZeroPlusOne→N
      (P→ℕ p ^ P→ℕ q)
      (powerBaseNonZero p q))

------------------------------------------------------------------------
-- 6. Certified prime enumeration
------------------------------------------------------------------------

-- Turn one natural into either a singleton certified-prime list or the
-- empty list.  No primality proof is manufactured: it comes directly from
-- the standard library's decision procedure prime?.
certifyPrime : ℕ → List P
certifyPrime n with prime? n
... | yes hn = mkP n hn ∷ []
... | no  _  = []

-- All certified primes p with p ≤ B, in increasing order.
--
-- Data.List.Base.upTo (suc B) enumerates 0,1,...,B.
primesUpTo : ℕ → List P
primesUpTo B = concatMap certifyPrime (upTo (suc B))

-- PARI/GP:
--   primePrefix(k) = vector(k, i, prime(i));
--
-- Bertrand's postulate implies p_k ≤ 2^k for k ≥ 1.  Therefore all of the
-- first k primes occur in primesUpTo (2^k); taking k entries reproduces the
-- PARI prime prefix.  For k = 0 the result is [] as expected.
--
-- The return type is List P rather than Vec P k.  The entries themselves
-- are fully certified primes; a future theorem proving the Bertrand bound
-- inside Agda can strengthen the container type to Vec P k without changing
-- the computational content.
primePrefix : ℕ → List P
primePrefix k = take k (primesUpTo (2 ^ k))

------------------------------------------------------------------------
-- 7. Power table
------------------------------------------------------------------------

-- PARI/GP:
--
-- gpfPowerTable(k) = {
--   my(P = primePrefix(k));
--   matrix(k,k,i,j,gpfPower(P[i],P[j]))
-- };
--
-- A matrix is represented by a list of rows.  Every cell has type P.
gpfPowerTable : ℕ → List (List P)
gpfPowerTable k =
  let ps = primePrefix k
  in map (λ p → map (gpfPower p) ps) ps

------------------------------------------------------------------------
-- 8. Multiplicative fibers
------------------------------------------------------------------------

-- Compare certified primes extensionally by their underlying natural
-- values.  Proof components are intentionally irrelevant to this test.
pairIfInTimesFiber : P → P → P → List (P × P)
pairIfInTimesFiber r p q with P→ℕ (gpfTimes p q) ≟ P→ℕ r
... | yes _ = (p , q) ∷ []
... | no  _ = []

-- PARI/GP:
--
-- fiberTimes(r,B) = {
--   my(P=listcreate(), out=List());
--   forprime(p=2,B,listput(P,p));
--   for(i=1,#P, for(j=1,#P,
--     if(gpfTimes(P[i],P[j])==r, listput(out,[P[i],P[j]]))
--   ));
--   Vec(out)
-- };
--
-- As in the PARI code, these are ORDERED pairs.  Thus (p,q) and (q,p)
-- are separate entries whenever p ≠ q and both satisfy the fiber equation.
fiberTimes : P → ℕ → List (P × P)
fiberTimes r B =
  let ps = primesUpTo B
  in concatMap
       (λ p → concatMap (λ q → pairIfInTimesFiber r p q) ps)
       ps

------------------------------------------------------------------------
-- 9. Value-only views (useful at the REPL / for comparison with PARI)
------------------------------------------------------------------------

-- These functions erase certificates only for presentation.  The core
-- computations above remain certificate-preserving.
primePrefixValues : ℕ → List ℕ
primePrefixValues k = map P→ℕ (primePrefix k)

gpfPowerTableValues : ℕ → List (List ℕ)
gpfPowerTableValues k = map (map P→ℕ) (gpfPowerTable k)

fiberTimesValues : P → ℕ → List (ℕ × ℕ)
fiberTimesValues r B =
  map (λ pq → P→ℕ (proj₁ pq) , P→ℕ (proj₂ pq)) (fiberTimes r B)
