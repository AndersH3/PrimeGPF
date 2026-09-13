module PrimeGPFRuntimeTestsMinimal where

------------------------------------------------------------------------
-- Minimal compiled runtime regression test for the 5 x 5 GPF power table.
--
-- This deliberately avoids importing the standard-library IO module,
-- because that module pulls in a large dependency graph.  Instead it uses
-- Agda's built-in IO type plus a tiny GHC FFI binding for putStrLn.
------------------------------------------------------------------------

open import PrimeGPF

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤)
open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; _≡ᵇ_)

------------------------------------------------------------------------
-- Minimal output primitive for the GHC backend.
------------------------------------------------------------------------

postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}

------------------------------------------------------------------------
-- Expected result, independently copied from the PARI/GP calculation.
------------------------------------------------------------------------

expectedPowerTable5 : List (List ℕ)
expectedPowerTable5 =
  (5  ∷ 3  ∷ 11    ∷ 43      ∷ 683      ∷ []) ∷
  (5  ∷ 7  ∷ 61    ∷ 547     ∷ 661      ∷ []) ∷
  (13 ∷ 7  ∷ 521   ∷ 449     ∷ 5281     ∷ []) ∷
  (5  ∷ 43 ∷ 191   ∷ 911     ∷ 10746341 ∷ []) ∷
  (61 ∷ 37 ∷ 13421 ∷ 1623931 ∷ 58367    ∷ []) ∷
  []

------------------------------------------------------------------------
-- Executable structural equality for lists/matrices of naturals.
------------------------------------------------------------------------

natListEq : List ℕ → List ℕ → Bool
natListEq []       []       = true
natListEq []       (_ ∷ _)  = false
natListEq (_ ∷ _)  []       = false
natListEq (x ∷ xs) (y ∷ ys) = (x ≡ᵇ y) ∧ natListEq xs ys

natMatrixEq : List (List ℕ) → List (List ℕ) → Bool
natMatrixEq []       []       = true
natMatrixEq []       (_ ∷ _)  = false
natMatrixEq (_ ∷ _)  []       = false
natMatrixEq (r ∷ rs) (s ∷ ss) = natListEq r s ∧ natMatrixEq rs ss

------------------------------------------------------------------------
-- Runtime test.  This is executable code, not a proof by refl.
------------------------------------------------------------------------

powerTable5OK : Bool
powerTable5OK = natMatrixEq (gpfPowerTableValues 5) expectedPowerTable5

resultMessage : Bool → String
resultMessage true  = "PASS: gpfPowerTableValues 5 matches the expected PARI/GP table."
resultMessage false = "FAIL: gpfPowerTableValues 5 differs from the expected PARI/GP table."

main : IO ⊤
main = putStrLn (resultMessage powerTable5OK)
