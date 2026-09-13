{-# OPTIONS --safe #-}

module PrimeGPFHeavyTests where

------------------------------------------------------------------------
-- Optional heavier regression tests for PrimeGPF.
--
-- Run explicitly with:
--
--     agda PrimeGPFHeavyTests.agda
--
-- This checks the complete 5 x 5 gpfPower table.  It is separate from
-- PrimeGPFTests.agda because normalization requires substantially larger
-- factorizations (for example 11^11 + 1).
------------------------------------------------------------------------

open import PrimeGPF

open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

-- primePrefix(5) = [2,3,5,7,11]
--
-- PARI/GP / direct integer factorisation gives the table
--
--   [       5,      3,    11,      43,      683 ]
--   [       5,      7,    61,     547,      661 ]
--   [      13,      7,   521,     449,     5281 ]
--   [       5,     43,   191,     911, 10746341 ]
--   [      61,     37, 13421, 1623931,    58367 ]
--
-- The theorem is proved by refl, forcing Agda to normalize the complete
-- certified computation to exactly these values.

test-gpfPowerTable-5 :
  gpfPowerTableValues 5 ≡
    (5  ∷ 3  ∷ 11    ∷ 43      ∷ 683      ∷ []) ∷
    (5  ∷ 7  ∷ 61    ∷ 547     ∷ 661      ∷ []) ∷
    (13 ∷ 7  ∷ 521   ∷ 449     ∷ 5281     ∷ []) ∷
    (5  ∷ 43 ∷ 191   ∷ 911     ∷ 10746341 ∷ []) ∷
    (61 ∷ 37 ∷ 13421 ∷ 1623931 ∷ 58367    ∷ []) ∷
    []
test-gpfPowerTable-5 = refl
