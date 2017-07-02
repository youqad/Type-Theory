module _ where

  open import Data.Nat

  open import Relation.Binary.PropositionalEquality using (_≡_ ; sym ; refl ; cong)

  data Fin : ℕ → Set where
    zero : {n : ℕ} → Fin (suc n)
    suc : {n : ℕ} → Fin n → Fin (suc n)

  max : (n : ℕ) → Fin (suc n)
  max zero = zero {0}
  max (suc n) = suc (max n)

  emb : {n : ℕ} → Fin n → Fin (suc n)
  emb {n} zero = zero {n}
  emb (suc s) = suc (emb s)

  suc-sym : ∀ m n → suc (m + n) ≡ m + suc n
  suc-sym zero n = refl
  suc-sym (suc m) n = cong suc (suc-sym m n)


  0-right-unit : ∀ n → n + 0 ≡ n
  0-right-unit zero = refl
  0-right-unit (suc n) = cong suc (0-right-unit n)

  0-right-unit₂ : ∀ n → n ≡ n + 0
  0-right-unit₂ n = sym (0-right-unit n)

  inv₀ : {n : ℕ} → Fin n → _
  inv₀ {n} = invCount {n} 0
    where
      iterateS : (n : ℕ) → (k : ℕ) → Fin (suc (n + k))
      iterateS 0 k = zero {k}
      iterateS (suc n) k = suc (iterateS n k)

      invCount : {n : ℕ} → (k : ℕ) → Fin n → Fin (n + k)
      invCount k (zero {n}) rewrite suc-sym k n = iterateS n k
      invCount k (suc {n} s) rewrite suc-sym n k = invCount (suc k) s

