-- test

module basics_intro where

data Bool : Set where
  true : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

!_ : Bool → Bool
! true = false
! false = true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

add : Nat → Nat → Nat
add zero y = y
add (suc x) y = suc (add x y)

_+_ : Nat → Nat → Nat
a + b = add a b

low = suc zero
high = low + (low + low)



data List (A : Set) : Set where
  Nil : List A
  Cons : A → List A → List A

length : {A : Set} → List A → Nat
length Nil = zero
length (Cons y y') = suc (length y')


map : {A B : Set} → (A → B) → List A → List B

map f Nil = Nil
map f (Cons x l) = Cons (f x) (map f l)

concat : {A : Set} → List A → List A → List A

concat Nil l' = l'
concat (Cons x l) l' = Cons x (concat l l')

data Vector (A : Set) : Nat → Set where
  ε : Vector A zero
  _►_ : {n : Nat} → A → Vector A n → Vector A (suc n)

vLength : {A : Set} → {n : Nat} → Vector A n → Nat
vLength {_} {n} v = n

vMap : {A B : Set} → {n : Nat} → (A → B) → Vector A n → Vector B n
vMap f ε = ε
vMap f (x ► v) = (f x) ► vMap f v

vConcat : {A : Set} → {n m : Nat} → Vector A n → Vector A m → Vector A (n + m)
vConcat ε v' = v'
vConcat (x ► v) v' = x ► (vConcat v v')
