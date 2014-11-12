module Expr where

open import Data.Bool using (Bool; true; false; _∨_; _∧_; if_then_else_)
open import Data.Nat using (zero; suc; _+_) renaming (ℕ to Nat)
open import Data.Empty using (⊥; ⊥-elim)

-- A basic language of boolean expressions
data Term : Set where
  TmTrue  : Term
  TmFalse : Term
  TmNot   : (t : Term) → Term
  TmAnd   : (t₁ t₂ : Term) → Term
  TmOr    : (t₁ t₂ : Term) → Term
  TmIf    : (t₁ t₂ t₃ : Term) → Term
  
-- Warm-up exercise: calculate the size of a term
size : Term → Nat
size _ = suc zero

-- Define a predicate that says when a term is a value
data Value : Term → Set where
  V-True : Value TmTrue
  V-False : Value TmFalse

-- Define a relatio that says when a term evaluates to another term (in one step)
data _EvaluatesTo_ : Term → Term → Set where
  E-NotTrue : (TmNot TmTrue) EvaluatesTo (TmFalse)
  E-NotFalse : (TmNot TmFalse) EvaluatesTo (TmTrue)
  E-AndTrueTrue : (TmAnd TmTrue TmTrue) EvaluatesTo (TmTrue)
  E-AndTrueFalse : (TmAnd TmTrue TmFalse) EvaluatesTo (TmFalse)
  E-AndFalseTrue : (TmAnd TmFalse TmTrue) EvaluatesTo (TmFalse)
  E-AndFalseFalse : (TmAnd TmFalse TmFalse) EvaluatesTo (TmFalse)

-- Logical negation of a type can be expressed as a function to the empty type
Not : Set → Set
Not A = A → ⊥

-- Define a term to be normal if it doesn't evaluate to any other term
Normal : Term → Set
Normal TmTrue = Term
Normal TmFalse = {!!}
Normal (TmNot t) = {!!}
Normal (TmAnd t t₁) = {!!}
Normal (TmOr t t₁) = {!!}
Normal (TmIf t t₁ t₂) = {!!}

-- Prove that all values are normal
values-normal : {t : Term} → Value t → Normal t
values-normal = {!!}

-- Prove that an if-expression is never normal
if-not-normal : (t₁ t₂ t₃ : Term) → Not (Normal (TmIf t₁ t₂ t₃))
if-not-normal t₁ t₂ t₃ ifTerm-normal = {!!}

-- Prove that all normal terms are values
normal-value : (t : Term) → Normal t → Value t
normal-value t n-t = {!!}

