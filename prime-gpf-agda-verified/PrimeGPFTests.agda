{-# OPTIONS --safe #-}

module PrimeGPFTests where

------------------------------------------------------------------------
-- Compile-time regression tests for PrimeGPF.
--
-- Run:
--
--     agda PrimeGPFTests.agda
--
-- Every theorem below is proved by `refl`, so Agda must actually reduce
-- the corresponding PrimeGPF computation to the expected result.  A
-- computational change that produces a different value will therefore
-- make this module fail to type-check.
------------------------------------------------------------------------

open import PrimeGPF

open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

------------------------------------------------------------------------
-- 1. Prime enumeration
------------------------------------------------------------------------

-- PARI/GP: primePrefix(5) = [2, 3, 5, 7, 11]
test-primePrefix-5 :
  primePrefixValues 5 ≡ 2 ∷ 3 ∷ 5 ∷ 7 ∷ 11 ∷ []
test-primePrefix-5 = refl

------------------------------------------------------------------------
-- 2. Concrete inputs for the three GPF operations
------------------------------------------------------------------------

-- Extract the required certified primes from primePrefix.  The fallback
-- branches make these helper functions total.  The tests below force the
-- actual primePrefix computations and therefore also check that these
-- branches are not taken.

gpfPlus-2-3-value : ℕ
gpfPlus-2-3-value with primePrefix 2
... | p2 ∷ p3 ∷ _ = P→ℕ (gpfPlus p2 p3)
... | _            = 0

-- PARI/GP: greatestPrimeFactor(2 + 3 + 1) = gpf(6) = 3
test-gpfPlus-2-3 : gpfPlus-2-3-value ≡ 3
test-gpfPlus-2-3 = refl


gpfTimes-3-5-value : ℕ
gpfTimes-3-5-value with primePrefix 3
... | p2 ∷ p3 ∷ p5 ∷ _ = P→ℕ (gpfTimes p3 p5)
... | _                 = 0

-- PARI/GP: greatestPrimeFactor(3 * 5 + 1) = gpf(16) = 2
test-gpfTimes-3-5 : gpfTimes-3-5-value ≡ 2
test-gpfTimes-3-5 = refl


gpfPower-2-3-value : ℕ
gpfPower-2-3-value with primePrefix 2
... | p2 ∷ p3 ∷ _ = P→ℕ (gpfPower p2 p3)
... | _            = 0

-- PARI/GP: greatestPrimeFactor(2 ^ 3 + 1) = gpf(9) = 3
test-gpfPower-2-3 : gpfPower-2-3-value ≡ 3
test-gpfPower-2-3 = refl

------------------------------------------------------------------------
-- 3. Power table
------------------------------------------------------------------------

-- A deliberately small table is used as a compile-time regression test;
-- this keeps type-checking fast while testing every row/column mechanism.
-- For primePrefix(3) = [2,3,5], PARI/GP gives:
--
--   [  5, 3,  11 ]
--   [  5, 7,  61 ]
--   [ 13, 7, 521 ]

test-gpfPowerTable-3 :
  gpfPowerTableValues 3 ≡
    (5  ∷ 3 ∷ 11  ∷ []) ∷
    (5  ∷ 7 ∷ 61  ∷ []) ∷
    (13 ∷ 7 ∷ 521 ∷ []) ∷
    []
test-gpfPowerTable-3 = refl

-- The originally suggested k = 5 example is exposed as a normal value.
-- It can be normalized interactively in Emacs with C-c C-n, or queried
-- from another Agda module, without forcing the larger factorisations on
-- every compilation of this regression-test module.
powerTable5Values : List (List ℕ)
powerTable5Values = gpfPowerTableValues 5

------------------------------------------------------------------------
-- 4. Multiplicative fiber
------------------------------------------------------------------------

fiberTimes-2-7-values : List (ℕ × ℕ)
fiberTimes-2-7-values with primePrefix 1
... | p2 ∷ _ = fiberTimesValues p2 7
... | _      = []

-- With p,q among the primes <= 7, gpf(p*q+1)=2 exactly for the ordered
-- pairs (3,5) and (5,3).
test-fiberTimes-2-7 :
  fiberTimes-2-7-values ≡ (3 , 5) ∷ (5 , 3) ∷ []
test-fiberTimes-2-7 = refl

------------------------------------------------------------------------
-- 5. Additional boundary checks
------------------------------------------------------------------------

test-primePrefix-0 : primePrefixValues 0 ≡ []
test-primePrefix-0 = refl

test-gpfPowerTable-0 : gpfPowerTableValues 0 ≡ []
test-gpfPowerTable-0 = refl
