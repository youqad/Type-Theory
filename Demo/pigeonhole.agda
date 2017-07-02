open import Data.Nat
open import Relation.Nullary
open import Data.Vec
open import Data.Product

open import Relation.Binary.PropositionalEquality


-- adapted from https://github.com/youqad/Coq_Project/blob/master/pigeonhole.v

module pigeonhole {X : Set} where

  data not-repeats : ∀ {n} → Vec X n → Set where
    base-not-repeats : not-repeats []
    rec-not-repeats : ∀ {x n} → {l : Vec X n} → not-repeats l → ¬ (x ∈ l) → not-repeats (x ∷ l)


  repeats : ∀ {n} → Vec X n → Set
  repeats l = ¬ not-repeats l

  _↪_ : ∀ {n m} → Vec X n → Vec X m → Set
  l ↪ l' = ∀ {x} → x ∈ l → x ∈ l'

  ∈-delete : ∀ {n} → (x : X) → (l : Vec X (suc n)) → x ∈ l
             → Σ[ l' ∈ Vec X n ] (∀ {y} → y ≢ x → y ∈ l → y ∈ l')
  ∈-delete x (x₁ ∷ []) = λ x₂ → [] , (λ x₃ x₄ → {!!})
  ∈-delete x (x₁ ∷ x₂ ∷ l) = {!!}

 f
