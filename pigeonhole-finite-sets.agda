open import Data.Fin
open import Data.Fin.Properties
open import Data.Nat.Base using (ℕ; zero; suc; z≤n; s≤s; _<_ ; _≤_)
open import Relation.Nullary
open import Relation.Binary
open import Data.Vec
open import Data.Vec.Properties
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


index : ∀ {N n : ℕ} → (Fin N) → Vec (Fin N) n → Maybe (Fin n)
index {zero} {_} ()
index _ [] = nothing
index {suc N} x (y ∷ ys) with Data.Fin.Properties._≟_ x y
... | yes _ = just zero
... | no _  with index x ys
...            | just n = just (suc n)
...            | nothing = nothing

index-sure : ∀ {N n : ℕ} → (x : (Fin N)) → (l : Vec (Fin N) n) → x ∈ l → Σ[ m ∈ (Fin n) ] (lookup {A = Fin N} m l ≡ x)
index-sure _ [] ()
index-sure x (y ∷ ys) x∈y∷ys with Data.Fin.Properties._≟_ x y
... | yes x≡y = zero , sym x≡y
... | no x≢y with index x ys | x∈y∷ys
...             | _ | here = ⊥-elim (x≢y refl)
...             | n | there x∈ys with index-sure x ys x∈ys
index-sure .(lookup m ys) (y ∷ ys) x∈y∷ys | no x≢y | n₁ | (there x∈ys) | (m , refl) = suc m , refl

_∈?_ : ∀ {n m} (x : Fin n) (l : Vec (Fin n) m) → Dec (x ∈ l)
x  ∈? [] = no λ()
x  ∈? (y ∷ l) with Data.Fin.Properties._≟_ x y
x  ∈? (.x ∷ l)   | yes refl = yes here
x  ∈? (y ∷ l)    | no x≠y with x ∈? l
...                        | yes x∈l = yes (there x∈l)
...                        | no  x∉l = no  (λ x∈y∷l → [ x≠y , x∉l ]′ (∈-to-∪ x∈y∷l))
  where
    ∈-to-∪ : ∀ {n : ℕ} {x' y' : Fin n} {l'} → x' ∈ (y' ∷ l') → (x' ≡ y') ⊎ (x' ∈ l')
    ∈-to-∪ here = inj₁ refl
    ∈-to-∪ (there x'∈l') = inj₂ x'∈l'


clash-indices : ∀ {N n} → (l : Vec (Fin N) n) → repeats l
                → Σ[ ij ∈ (Fin n × Fin n) ] ((proj₁ ij ≢ proj₂ ij) × (lookup (proj₁ ij) l ≡ lookup (proj₂ ij) l))
clash-indices [] ()
clash-indices (x ∷ l) (base-repeats x∈l) with index-sure x l x∈l
...                                         | m , lookup-nat-m-l≡x =
                                              (zero , suc m) , ( (λ ()) , sym lookup-nat-m-l≡x)
clash-indices (x ∷ l) (rec-repeats r) = let (i , j) , (i≢j , lookup-nat-i-l≡lookup-nat-j-l) = clash-indices l r
                                        in (suc i , suc j) , ((λ suc-i≡suc-j → i≢j (suc-injective suc-i≡suc-j)) , lookup-nat-i-l≡lookup-nat-j-l)



_↪_ : ∀ {X : Set} {n m} → Vec X n → Vec X m → Set
l ↪ l' = ∀ {x} → x ∈ l → x ∈ l'

∈-delete : ∀ {N n} → (x : Fin N) → (l : Vec (Fin N) (suc n)) → x ∈ l
            → Σ[ l' ∈ Vec (Fin N) n ] (∀ {y : Fin N} → y ≢ x → y ∈ l → y ∈ l')
∈-delete x (.x ∷ []) here = [] , lemma {x = x}
  where
    lemma : {N : ℕ} → {x y : Fin N} → y ≢ x → y ∈ x ∷ [] → y ∈ []
    lemma y≢x here = ⊥-elim (y≢x refl)
    lemma y≢x (there ())
∈-delete x (x₁ ∷ []) (there ())
∈-delete {N} x (.x ∷ x₂ ∷ l) here = (x₂ ∷ l) , lemma₂ {N} {x}
  where
    lemma₂ : ∀ {N} {x y x₂ : Fin N} {l : Vec (Fin N) _} → y ≢ x → y ∈ x ∷ x₂ ∷ l → y ∈ x₂ ∷ l
    lemma₂ y≢x here = ⊥-elim (y≢x refl)
    lemma₂ y≢x (there y∈x∷x₂∷l) = y∈x∷x₂∷l
∈-delete {N} x (x₁ ∷ x₂ ∷ l) (there x∈l) = let l' , p = ∈-delete x (x₂ ∷ l) x∈l
                                        in (x₁ ∷ l') , lemma₃ {N} {l} {p = p}
                                          where
                                            lemma₃ : ∀ {N : ℕ} {l : Vec (Fin N) _} {x x₁ x₂ : Fin N} {x∈l : x ∈ x₂ ∷ l}
                                                     {p : ∀ {y' : Fin N} → y' ≢ x → y' ∈ (x₂ ∷ l)
                                                     → y' ∈ proj₁ (∈-delete x (x₂ ∷ l) x∈l)}
                                                     → {y : Fin N}
                                                     → y ≢ x → y ∈ x₁ ∷ x₂ ∷ l
                                                     → y ∈ x₁ ∷ proj₁ (∈-delete x (x₂ ∷ l) x∈l)
                                            lemma₃ y≢x here = here
                                            lemma₃ {N} {l} {p = p} y≢x (there y∈x₁∷x₂∷l) = there (p y≢x y∈x₁∷x₂∷l)



pigeonhole-vec : ∀ {N n m : ℕ} (l₁ : Vec (Fin N) n) (l₂ : Vec (Fin N) m) → l₁ ↪ l₂ → Data.Nat.Base._<_ m n → repeats l₁
pigeonhole-vec {zero} {.0} {m} [] l₂ l₁↪l₂ ()
pigeonhole-vec {zero} {.(suc _)} {m} (x ∷ l₁) l₂ l₁↪l₂ m<n with x
... | ()
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
                              not-in-not-equal : ∀ {N k : ℕ} {y x' : Fin N} {l : Vec (Fin N) k} → (y ∈ l) → ¬ (x' ∈ l) → y ≢ x'
                              not-in-not-equal y∈l x'∉l y≡x rewrite y≡x = ⊥-elim (x'∉l y∈l)

    m<n : ∀ {m' n'} → Data.Nat.Base._<_ (suc m') (suc n') → Data.Nat.Base._<_ m' n'
    m<n (s≤s suc-m<suc-n₁) = suc-m<suc-n₁


record PigeonClash {m n : ℕ} (f : Fin m → Fin n) : Set where
  field
    i j : Fin m
    nonEq : i ≢ j
    nonInj : f i ≡ f j

tabulate-↪ : {m n : ℕ} → (f : Fin m → Fin n) → (tabulate f) ↪ allFin n
tabulate-↪ f {x} _ = ∈-allFin x


tabulate-clash : {m n : ℕ} → (f : Fin m → Fin n) → repeats (tabulate f) → PigeonClash f
tabulate-clash f repeats-tabulate = let (i , j) , (i≢j , lookup-i≡lookup-j) = clash-indices (tabulate f) repeats-tabulate
                                    in let fi = lookup∘tabulate f (proj₁ (proj₁ (clash-indices (tabulate f) repeats-tabulate)))
                                    in let fj = lookup∘tabulate f (proj₂ (proj₁ (clash-indices (tabulate f) repeats-tabulate)))
                                    in record
                                       { i = i ; j = j ; nonEq = i≢j ;
                                         nonInj = trans (trans (sym fi) lookup-i≡lookup-j) fj }

php : {m n : ℕ} → Data.Nat.Base._<_ n m → (f : Fin m → Fin n) → PigeonClash f
php = {!!}


