open import Data.Nat
open import Data.Unit
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
import Level

module _ {α}{A : Set α} where

Unique : ∀ {n} → Vec A n → Set α
Unique []       = Level.Lift ⊤
Unique (x ∷ xs) = ¬ (x ∈ xs) × Unique xs
