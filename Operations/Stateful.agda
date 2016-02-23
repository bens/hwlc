module Operations.Stateful where

import      Data.Bool as B
open import Data.Fin
open import Data.Nat
open import Data.Vec hiding (head; tail)
open import Function
open import Relation.Binary.PropositionalEquality

open import Eval
open import Operations.Combinatorial
open import Types

alternator : Closed 𝔹 → Closed (ℂ 𝔹)
alternator x = reg x (lam (pair (not ∙ var zero refl) (var zero refl)))

constant : ∀ {τ} → Closed τ → Closed (ℂ τ)
constant x = reg x (lam (pair (var zero refl) (var zero refl)))
