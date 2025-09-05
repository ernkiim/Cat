{-# OPTIONS --safe #-}

module Minicat where

open import Data.Char using (Char) renaming (_≟_ to _≟Char_)
open import Data.String using (String) renaming (_≟_ to _≟String_)
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
import MetaCat as S
open S using (+_; +[1+_]; -[1+_]) renaming (true to t; false to f)

open import Data.Product

-- precedence
infix 0 if_then_else_
infixl 1 _==_
infixl 2 _or_
infixl 3 _and_
infix  4 not_

infixl 5 _+_
infixl 6 _*_
infixl 7 _mod_
infix  8 -_
infix  9 int_

infix 10 `_

infixl 2 _⊢_
infixl 3 _∋_ _∋?_

infixl 4 _,_↦_

-- infixl 3 _—↠_


--- Types

data Type : Set where
  ℤ    : Type
  Bool : Type

-- Types go to Agda Sets
⟦_⟧T : Type → Set
⟦ ℤ    ⟧T = S.ℤ
⟦ Bool ⟧T = S.Bool

private variable
  A B : Type
  v w : ⟦ A ⟧T


--- Variables
Variable = String
private variable x y : Variable


--- Memories
data Memory : Set where
  ϵ     : Memory
  _,_↦_ : Memory → Variable → ⟦ A ⟧T → Memory

private variable M M′ M″ : Memory

-- References are to in-scope variables.

data _∋_ : Memory → Variable → Set where

  here : {v : ⟦ A ⟧T} →

    -------------------
    M , x ↦ v ∋ x

  there : {w : ⟦ B ⟧T} →

    x ≢ y → M ∋ x →
    ---------------
    M , y ↦ w ∋ x

private variable r : M ∋ x

-- Look up reference
lookup : M ∋ x → ∃[ A ] ⟦ A ⟧T
lookup (here {A = A} {v = v}) = A , v
lookup (there _ r)            = lookup r

type : M ∋ x → Type
type r = proj₁ (lookup r)

-- Variable's well-scopedness is decidable
_∋?_ : ∀ M x → Dec (M ∋ x)
ϵ ∋? x = no λ ()
M , y ↦ v ∋? x with x ≟String y
... | yes refl = yes here
... | no  x≢y with M ∋? x
... | yes M∋x = yes (there x≢y M∋x)
... | no ¬M∋x = no λ { here → x≢y refl ; (there _ M∋x) → ¬M∋x M∋x }


--- Typing and evaluation are mutually recursive

data _⊢_ (M : Memory) : Type → Set
⟦_⟧    : M ⊢ A → ⟦ A ⟧T

-- Expressions are type judgments over a Memory
data _⊢_ M where

  -- variables
  `_ : ∀ x →

    {t : True (M ∋? x)} →
    ---------
    M ⊢ type (toWitness t)

  -- integers
  int_          : S.ℤ → M ⊢ ℤ
  -_            : M ⊢ ℤ → M ⊢ ℤ
  _+_ _*_ _mod_ : M ⊢ ℤ → M ⊢ ℤ → M ⊢ ℤ

  -- booleans
  true       : M ⊢ Bool
  false      : M ⊢ Bool
  not_       : M ⊢ Bool → M ⊢ Bool
  _and_ _or_ : M ⊢ Bool → M ⊢ Bool → M ⊢ Bool

  -- boolean equality (polymorphic)
  _==_ : M ⊢ A → M ⊢ A → M ⊢ Bool

  -- ternary (dependent)
  if_then_else_ : (b : M ⊢ Bool) → M ⊢ A → M ⊢ B →

    M ⊢ (S.if ⟦ b ⟧ then A else B)

private variable e e₁ e₂ : M ⊢ A


-- Evaluation

-- -- variables
⟦ `_ _ {tt} ⟧ = proj₂ (lookup (toWitness tt))

-- integers
⟦ int k     ⟧ = k
⟦ - e       ⟧ = S.- ⟦ e ⟧
⟦ e₁  +  e₂ ⟧ = ⟦ e₁ ⟧ S.+   ⟦ e₂ ⟧
⟦ e₁  *  e₂ ⟧ = ⟦ e₁ ⟧ S.*   ⟦ e₂ ⟧
⟦ e₁ mod e₂ ⟧ = ⟦ e₁ ⟧ S.mod ⟦ e₂ ⟧

-- booleans
⟦ true      ⟧ = t
⟦ false     ⟧ = f
⟦ not e     ⟧ = S.not ⟦ e ⟧
⟦ e₁ and e₂ ⟧ = ⟦ e₁ ⟧ S.∧ ⟦ e₂ ⟧
⟦ e₁ or  e₂ ⟧ = ⟦ e₁ ⟧ S.∨ ⟦ e₂ ⟧

-- boolean equality
⟦ _==_ {A = ℤ}    e₁ e₂ ⟧ = ⟦ e₁ ⟧ S.==ℤ ⟦ e₂ ⟧
⟦ _==_ {A = Bool} e₁ e₂ ⟧ = ⟦ e₁ ⟧ S.==B ⟦ e₂ ⟧

-- ternary
⟦ if e₁ then e₂ else e₃ ⟧ with ⟦ e₁ ⟧
... | t = ⟦ e₂ ⟧
... | f = ⟦ e₃ ⟧


-- A program is a function on memories
data _—→_ (M : Memory) : Memory → Set where

  ∅ :

    -----
    M —→ M

  _⨾_≔_ :

    (M —→ M′) → ∀ x (e : M′ ⊢ A) →
    ---------------------------
        M —→ (M′ , x ↦ ⟦ e ⟧)
