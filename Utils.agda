module Utils where

open import Data.Fin hiding (_+_; fromℕ)
open import Data.Nat

data Fromℕ (n : ℕ) : ℕ → Set where
  yes : (m : Fin n) → Fromℕ n (toℕ m)
  no  : (m : ℕ)     → Fromℕ n (n + m)

fromℕ : ∀ n m → Fromℕ n m
fromℕ zero m = no m
fromℕ (suc n) zero = yes zero
fromℕ (suc n) (suc m) with fromℕ n m
fromℕ (suc n) (suc .(toℕ m)) | yes m = yes (suc m)
fromℕ (suc n) (suc .(n + m)) | no m = no m
