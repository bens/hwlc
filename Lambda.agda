module Lambda where

open import Data.Bool   using    (true; false)
open import Data.Nat    renaming (_≟_ to _≟N_)
import      Data.Stream as S
open import Data.Vec    using    ([]; _∷_)

open import Check
open import Eval
open import Operations
open import Types
open import Utils
