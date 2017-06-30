open import Data.Nat

module exercise_altenkirch where

data Fin : ℕ → Set
zero : {n : ℕ} → Fin (suc n)
suc : {n : ℕ} → Fin n → Fin (suc n)

max : n → Fin (suc n)
max n = ?
