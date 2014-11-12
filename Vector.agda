module Vector where

open import Data.Bool using (Bool; true; false; _∨_; _∧_; if_then_else_)
open import Data.Nat using (zero; suc; _+_) renaming (ℕ to Nat)

-- Vec A n is the type of lists of A of length n
data Vec (A : Set) : Nat → Set where
  []  : Vec A 0
  _∷_ : {n : Nat} → A → Vec A n → Vec A (suc n)
  -- Note: type \:: to write ∷

-- If we know that the length of a vector is at least 1,
-- we can safely take its head and tail.
head : {A : Set} {n : Nat} → Vec A (suc n) → A
head v = {!!}

tail : {A : Set} {n : Nat} → Vec A (suc n) → Vec A n
tail v = {!!}

-- Concatenation of vectors adds their length together
_++_ : {A : Set} {m n : Nat} → Vec A m → Vec A n → Vec A (m + n)
v ++ w = {!!}

-- Zipping two lists of length n results in another list of length  n
zip : {A B C : Set} {n : Nat} → (f : A → B → C) → Vec A n → Vec B n → Vec C n
zip f v w = {!!} 

-- Fin n is the type of natural numbers smaller than n
data Fin : Nat → Set where
  zero : {n : Nat} → Fin (suc n)
  suc  : {n : Nat} → Fin n → Fin (suc n)

-- We can use Fin to safely look up an element in a vector
-- (without risk of IndexOutOfBoundsExceptions)
_!_ : {A : Set} {n : Nat} → Vec A n → Fin n → A
v ! i = {!!}  
