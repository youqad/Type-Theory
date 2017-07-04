open import Data.Nat
open import Data.Nat.Base
open import Relation.Nullary
open import Data.Vec
open import Data.Product
open import Data.Empty

open import Relation.Binary.PropositionalEquality


-- inspired by https://github.com/youqad/Coq_Project/blob/master/pigeonhole.v

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
  ∈-delete x (.x ∷ []) here = [] , lemma {x}
    where
      lemma : {x y : X} → y ≢ x → y ∈ x ∷ [] → y ∈ []
      lemma y≢x here = ⊥-elim (y≢x refl)
      lemma y≢x (there ())
  ∈-delete x (x₁ ∷ []) (there ())
  ∈-delete x (.x ∷ x₂ ∷ l) here = (x₂ ∷ l) , lemma₂ {x}
    where
      lemma₂ : {x y : X} → y ≢ x → y ∈ x ∷ x₂ ∷ l → y ∈ x₂ ∷ l
      lemma₂ y≢x here = ⊥-elim (y≢x refl)
      lemma₂ y≢x (there y∈x∷x₂∷l) = y∈x∷x₂∷l
  ∈-delete x (x₁ ∷ x₂ ∷ l) (there x∈l) = let l' , p = ∈-delete x (x₂ ∷ l) x∈l
                                         in (x₁ ∷ l') , lemma₃ {p}
                                           where
                                             lemma₃ : {p : ∀ {y'} → y' ≢ x → y' ∈ (x₂ ∷ l) → y' ∈ proj₁ (∈-delete x (x₂ ∷ l) x∈l)}
                                                      → {y : X}
                                                      → y ≢ x → y ∈ x₁ ∷ x₂ ∷ l
                                                      → y ∈ x₁ ∷ proj₁ (∈-delete x (x₂ ∷ l) x∈l)
                                             lemma₃ y≢x here = here
                                             lemma₃ {p} y≢x (there y∈x₁∷x₂∷l) = there (p y≢x y∈x₁∷x₂∷l)


  pigeonhole : ∀ {n m} (l₁ : Vec X n) (l₂ : Vec X m) → l₁ ↪ l₂ → m < n → repeats l₁
  pigeonhole [] l₂ l₁↪l₂ ()
  pigeonhole (x ∷ l₁) [] x∷l₁↪l₂ m<n _ with (x∷l₁↪l₂ {x} here)
  ... | ()
  pigeonhole {suc n} {suc m} l₁@(x ∷ l₁') l₂@(_ ∷ _) x∷l₁↪l₂ suc-m<suc-n
             (rec-not-repeats not-repeats-l₁' x∉l₁') with (x∷l₁↪l₂ {x} here)
  ... | x∈l₂ with (∈-delete x l₂ x∈l₂)
  ...           | (l₂' , p) = ⊥-elim ((pigeonhole l₁' l₂' l₁'↪l₂' (m<n suc-m<suc-n)) not-repeats-l₁') -- p : (∀ {y} → y ≢ x → y ∈ l₂ → y ∈ l₂')
    where
      l₁'↪l₂' : ∀ {x'} → x' ∈ l₁' → x' ∈ l₂'
      l₁'↪l₂' {x'} x'∈l₁' = let x'∈l₂ = (x∷l₁↪l₂ (there x'∈l₁')) -- x' ∈ l₂ ≡ l₂' ∪ x
                            in p (not-in-not-equal x'∈l₁' x∉l₁') x'∈l₂
                              where
                                not-in-not-equal : ∀ {k} {y x' : X} {l : Vec X k} → (y ∈ l) → ¬ (x' ∈ l) → y ≢ x'
                                not-in-not-equal y∈l x'∉l y≡x rewrite y≡x = ⊥-elim (x'∉l y∈l)

      m<n : ∀ {m' n'} → suc m' < suc n' → m' < n'
      m<n (s≤s suc-m<suc-n₁) = suc-m<suc-n₁

