-- Quick guide to Agda input:
-- C-c C-l     Load file
-- C-c C-d     (after load) Deduce (infer) type of term
-- C-c C-n     (after load) Normalize (evaluate) term
-- ?           Insert new hole
-- C-c C-c     (inside hole) Case split
-- C-c C-space (inside hole) Give solution
-- C-c C-a     (inside hole) Auto
-- C-c C-r     (inside hole) Refine

-- Unicode characters:
-- \to         →
-- \forall     ∀
-- \not        ¬
-- \or         ∨
-- \and        ∧
-- \_1, ...    ₁, ₂, ₃, ...

module Intro where
open import Level using ()

-- Infix declarations (ignore these for now)
infix 7 ¬_
infixl 6 _∧_
infixl 5 _∨_
infix 4 if_then_else_
infixl 10 _+_
infix 2 _≡_

-- The type of booleans: true and false
data Bool : Set where
  true  : Bool
  false : Bool

-- Boolean negation
-- Note: the underscores say where the arguments should go
¬_ : Bool → Bool
¬ x = {!!}

_∧_ : Bool → Bool → Bool
x ∧ y = {!!}

_∨_ : Bool → Bool → Bool
x ∨ y = {!!}

if_then_else_ : ∀ {ℓ} {A : Set ℓ} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

-- You can use functions inside types!
example₁ : (b : Bool) → if b then Bool else (Bool → Bool)
example₁ true  = false
example₁ false = ¬_

-- x ≡ y is the type of proofs that x is equal to y
-- The basic way to prove equality is to use refl : x ≡ x
data _≡_ {ℓ} {A : Set ℓ} : A → A → Set ℓ where
  refl : {x : A} → x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

-- Try to prove this by case splitting on b
¬¬-elim : (b : Bool) → ¬ ¬ b ≡ b
¬¬-elim b = {!!}

∧-same : (b : Bool) → b ∧ b ≡ b
∧-same b = {!!}

-- Hint: you can also case split on an equality proof
≡-sym : (b1 b2 : Bool) → b1 ≡ b2 → b2 ≡ b1
≡-sym b1 b2 eq = {!!}

∨-first : (b : Bool) → b ∨ false ≡ true → b ≡ true
∨-first b eq = {!!} 


-- Natural numbers (in unary notation)
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

is-zero : Nat → Bool
is-zero n = {!!}

_+_ : Nat → Nat → Nat
zero + n = n
suc m + n = suc (m + n)

min : Nat → Nat → Nat
min m n = {!!}

_*_ : Nat → Nat → Nat
m * n = {!!}

-- As people, we know that 0 + n = n = n + 0.
-- The first equality is easy to prove ...
plus0-left : (n : Nat) → 0 + n ≡ n
plus0-left n = refl

-- ... but the second one is a bit harder.
-- Can you guess why?
plus0-right : (n : Nat) → n + 0 ≡ n
plus0-right zero = refl
plus0-right (suc n) rewrite (plus0-right n) = refl

plus-assoc : (k l m : Nat) → k + (l + m) ≡ (k + l) + m
plus-assoc k l m = {!!}

-- You might need a helper function for this one
plus-comm : (m n : Nat) → m + n ≡ n + m
plus-comm m n = {!!}
