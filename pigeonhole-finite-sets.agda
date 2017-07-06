open import Data.Fin hiding (_<_ ; _≤_)
open import Data.Nat.Base using (ℕ; zero; suc; z≤n; s≤s; _<_ ; _≤_)
open import Relation.Nullary
open import Relation.Binary
open import Data.Vec
open import Data.Product
open import Data.Sum using ([_,_]′; inj₁; inj₂; _⊎_)
open import Data.Empty
open import Data.Maybe


open import Relation.Binary.PropositionalEquality
import Relation.Nullary.Decidable as Dec


module pigeonhole-finite-sets where

data repeats : ∀ {X : Set} {n} → Vec X n → Set where
  base-repeats : ∀ {X : Set} {x : X} {n : ℕ} {l : Vec X n} → x ∈ l → repeats (x ∷ l)
  rec-repeats : ∀ {X : Set} {x : X} {n : ℕ} {l : Vec X n} → repeats l → repeats (x ∷ l)

lookup-nat : ∀  {n : ℕ} → (k : ℕ) → Vec ℕ n → k < n → ℕ
lookup-nat _ [] ()
lookup-nat zero (x ∷ xs) k<sucn = x
lookup-nat (suc k) (x ∷ xs) suck<sucn with suck<sucn
...                                      | (s≤s k<n) = lookup-nat k xs k<n


index : ∀ {n : ℕ} → ℕ → Vec ℕ n → Maybe ℕ
index _ [] = nothing
index x (y ∷ ys) with Data.Nat.Base._≟_ x y
... | yes _ = just zero
... | no _  with index x ys
...            | just n = just (suc n)
...            | nothin = nothing

index-sure : ∀ {n : ℕ} → (x : ℕ) → (l : Vec ℕ n) → x ∈ l → Σ[ m ∈ ℕ ] (Σ[ m<n ∈ m < n ] (lookup-nat m l m<n ≡ x))
index-sure _ [] ()
index-sure x (y ∷ ys) x∈y∷ys with Data.Nat.Base._≟_ x y
... | yes x≡y = zero , ( s≤s z≤n , sym x≡y )
... | no x≢y with index x ys | x∈y∷ys
...             | _ | here = ⊥-elim (x≢y refl)
...             | n | there x∈ys with index-sure x ys x∈ys
index-sure .(lookup-nat m ys m<n) (y ∷ ys) x∈y∷ys | no x≢y | n₁ | (there x∈ys) | (m , m<n , refl) = suc m , (s≤s m<n , refl)

_∈?_ : ∀ {n} (x : ℕ) (l : Vec ℕ n) → Dec (x ∈ l)
x  ∈? [] = no λ()
x  ∈? (y ∷ l) with Data.Nat.Base._≟_ x y
x  ∈? (.x ∷ l)   | yes refl = yes here
x  ∈? (y ∷ l)    | no x≠y with x ∈? l
...                        | yes x∈l = yes (there x∈l)
...                        | no  x∉l = no  (λ x∈y∷l → [ x≠y , x∉l ]′ (∈-to-∪ x∈y∷l))
  where
    ∈-to-∪ : ∀ {x' y' : ℕ} {l'} → x' ∈ (y' ∷ l') → (x' ≡ y') ⊎ (x' ∈ l')
    ∈-to-∪ here = inj₁ refl
    ∈-to-∪ (there x'∈l') = inj₂ x'∈l'


clash-indices : ∀ {n} → (l : Vec ℕ n) → repeats l
                → Σ[ ij ∈ (ℕ × ℕ) ]
                     (Σ[ i<n-j<n ∈ (proj₁ ij < n × proj₂ ij < n) ]
                       (lookup-nat (proj₁ ij) l (proj₁ i<n-j<n) ≡ lookup-nat (proj₂ ij) l (proj₂ i<n-j<n)))
clash-indices [] ()
clash-indices (x ∷ l) (base-repeats x∈l) = ({!!} , {!!}) , {!!} , {!!} -- suc (index-sure x l x∈l)
clash-indices (x ∷ l) (rec-repeats r) = let n , m = clash-indices l r in {!!} -- suc n , suc m



_↪_ : ∀ {X : Set} {n m} → Vec X n → Vec X m → Set
l ↪ l' = ∀ {x} → x ∈ l → x ∈ l'

∈-delete : ∀ {n} → (x : ℕ) → (l : Vec ℕ (suc n)) → x ∈ l
            → Σ[ l' ∈ Vec ℕ n ] (∀ {y} → y ≢ x → y ∈ l → y ∈ l')
∈-delete x (.x ∷ []) here = [] , lemma {x}
  where
    lemma : {x y : ℕ} → y ≢ x → y ∈ x ∷ [] → y ∈ []
    lemma y≢x here = ⊥-elim (y≢x refl)
    lemma y≢x (there ())
∈-delete x (x₁ ∷ []) (there ())
∈-delete x (.x ∷ x₂ ∷ l) here = (x₂ ∷ l) , lemma₂ {x}
  where
    lemma₂ : {x y : ℕ} → y ≢ x → y ∈ x ∷ x₂ ∷ l → y ∈ x₂ ∷ l
    lemma₂ y≢x here = ⊥-elim (y≢x refl)
    lemma₂ y≢x (there y∈x∷x₂∷l) = y∈x∷x₂∷l
∈-delete x (x₁ ∷ x₂ ∷ l) (there x∈l) = let l' , p = ∈-delete x (x₂ ∷ l) x∈l
                                        in (x₁ ∷ l') , lemma₃ {p}
                                          where
                                            lemma₃ : {p : ∀ {y'} → y' ≢ x → y' ∈ (x₂ ∷ l) → y' ∈ proj₁ (∈-delete x (x₂ ∷ l) x∈l)}
                                                    → {y : ℕ}
                                                    → y ≢ x → y ∈ x₁ ∷ x₂ ∷ l
                                                    → y ∈ x₁ ∷ proj₁ (∈-delete x (x₂ ∷ l) x∈l)
                                            lemma₃ y≢x here = here
                                            lemma₃ {p} y≢x (there y∈x₁∷x₂∷l) = there (p y≢x y∈x₁∷x₂∷l)



pigeonhole-vec : ∀ {n m : ℕ} (l₁ : Vec ℕ n) (l₂ : Vec ℕ m) → l₁ ↪ l₂ → m < n → repeats l₁
pigeonhole-vec [] l₂ l₁↪l₂ ()
pigeonhole-vec (x ∷ l₁) [] x∷l₁↪l₂ m<n with (x∷l₁↪l₂ {x} here)
... | ()
pigeonhole-vec {suc n} {suc m} l₁@(x ∷ l₁') l₂@(_ ∷ _) x∷l₁↪l₂ suc-m<suc-n
  with (x∷l₁↪l₂ {x} here)
... | x∈l₂ with (∈-delete x l₂ x∈l₂) | x ∈? l₁'
...           | _         | yes x∈l₁' = base-repeats x∈l₁'
...           | (l₂' , p) | no x∉l₁' = rec-repeats (pigeonhole-vec l₁' l₂' l₁'↪l₂' (m<n suc-m<suc-n))
  where
    l₁'↪l₂' : ∀ {x'} → x' ∈ l₁' → x' ∈ l₂'
    l₁'↪l₂' {x'} x'∈l₁' = let x'∈l₂ = (x∷l₁↪l₂ (there x'∈l₁')) -- x' ∈ l₂ ≡ l₂' ∪ x
                          in p (not-in-not-equal x'∈l₁' x∉l₁') x'∈l₂
                            where
                              not-in-not-equal : ∀ {k} {y x' : ℕ} {l : Vec ℕ k} → (y ∈ l) → ¬ (x' ∈ l) → y ≢ x'
                              not-in-not-equal y∈l x'∉l y≡x rewrite y≡x = ⊥-elim (x'∉l y∈l)

    m<n : ∀ {m' n'} → suc m' < suc n' → m' < n'
    m<n (s≤s suc-m<suc-n₁) = suc-m<suc-n₁


record PigeonClash {m n : ℕ} (f : Fin m → Fin n) : Set where
  field
    i j : ℕ
    i<m : i < m
    j<m : j < m
    nonEq : i ≢ j
    nonInj : f (fromℕ≤ {i} i<m) ≡ f (fromℕ≤ {j} j<m)

tabulate-↪ : {m n : ℕ} → (f : Fin m → Fin n) → (tabulate f) ↪ allFin n
tabulate-↪ f {.(f zero)} here = {!!}
tabulate-↪ f {x} (there x∈tabulatef) = {!!}


tabulate-clash : {m n : ℕ} → (f : Fin m → Fin n) → repeats (tabulate f) → PigeonClash f
tabulate-clash f (base-repeats fzero∈tabulatef∘suc) = {!!}
tabulate-clash f (rec-repeats x) = {!!}

php : {m n : ℕ} → n < m → (f : Fin m → Fin n) → PigeonClash f
php = {!!}

