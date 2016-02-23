module Lambda where

open import Data.Bool   using    (true; false)
open import Data.Nat    renaming (_≟_ to _≟N_)
import      Data.Stream as S
open import Data.Vec    using    ([]; _∷_)
open import Relation.Binary.PropositionalEquality

open import Check
open import Eval
open import Operations.Combinatorial
open import Operations.Stateful
open import Types
open import Utils

ex₀ : S.take 5 ([] ⟦ alternator bitO ⟧) ≡ false ∷ true ∷ false ∷ true ∷ false ∷ []
ex₀ = refl

ex₁ : S.take 5 ([] ⟦ constant bitI ⟧) ≡ true ∷ true ∷ true ∷ true ∷ true ∷ []
ex₁ = refl
