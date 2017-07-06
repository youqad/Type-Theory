module LearnYouAn where
  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

  data _even : ℕ → Set where
    ZERO : zero even
    STEP : ∀ {x} → x even → suc (suc x) even

  _+_ : ℕ → ℕ → ℕ
  zero + m = m
  suc n + m = suc (n + m)

  proof₁ : suc (suc (suc (suc zero))) even
  proof₁ = STEP (STEP ZERO)

  proof₂ : (A : Set) → A → A
  proof₂ _ ν = ν

  proof₂' : ℕ → ℕ
  proof₂' = proof₂ ℕ

  data _∧_ (P Q : Set) : Set where
    ∧-intro : P → Q → (P ∧ Q)

  p₁ : {P Q : Set} → (P ∧ Q) → P
  p₁ (∧-intro p q) = p

  _⇔_ : (P : Set) → (Q : Set) → Set
  a ⇔ b = (a → b) ∧ (b → a)

  ∧-comm : {P Q : Set} → (P ∧ Q) ⇔ (Q ∧ P)
  ∧-comm = ∧-intro pqqp pqqp
    where
      pqqp : {P Q : Set} → (P ∧ Q) → _
      pqqp (∧-intro p q) = ∧-intro q p

  data _∨_ (P Q : Set) : Set where
    ∨-l : P → P ∨ Q
    ∨-r : Q → P ∨ Q

  ∨-elim : {P Q R : Set} → (P ∨ Q) → (P → R) → (Q → R) → R
  ∨-elim (∨-l p) pr qr = pr p
  ∨-elim (∨-r q) pr qr = qr q


