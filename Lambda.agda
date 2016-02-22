module Lambda where

open import Data.Bool
open import Data.Fin hiding (_+_; fromℕ)
open import Data.Nat renaming (_≟_ to _≟N_)
open import Data.Product
open import Data.Vec hiding (head; tail)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Check
open import Eval
open import Types
open import Utils

Closed : Type → Set
Closed = Term []

bnot : Closed (𝔹 ⇒ 𝔹)
bnot = lam 𝔹 ((var zero refl) nand (var zero refl))
