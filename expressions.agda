module Expressions where

open import Data.String using (String) renaming (_≟_ to _≟String_)
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality
import MetaCat as S
open S using (+_; +[1+_]; -[1+_])

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
infixl 3 _∋_⦂_ _∋?_⦂_
infixl 4 _,_⦂_↦_


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

-- Decidable equality of types
_≟Type_ : (A B : Type) → Dec (A ≡ B)
ℤ    ≟Type ℤ    = yes refl
Bool ≟Type Bool = yes refl
ℤ    ≟Type Bool = no λ ()
Bool ≟Type ℤ    = no λ ()


--- Memories

Variable = String
private variable x y : Variable

data Memory : Set where
  ϵ       : Memory
  _,_⦂_↦_ : Memory → Variable → (A : Type) → ⟦ A ⟧T → Memory

private variable M M′ : Memory


--- References to are in-scope variables.

data _∋_⦂_ : Memory → Variable → Type → Set where

  here :

    ---------------------
    M , x ⦂ A ↦ v ∋ x ⦂ A

  there :

    x ≢ y   →   M ∋ x ⦂ A →
    ---------------------
    M , y ⦂ B ↦ w ∋ x ⦂ A

private variable r : M ∋ x ⦂ A

-- Access fields from reference
name : M ∋ x ⦂ A → Variable
name {x = x} _ = x

type : M ∋ x ⦂ A → Type
type {A = A} _ = A

value : M ∋ x ⦂ A → ⟦ A ⟧T
value (here {v = v}) = v
value (there _ r)    = value r

-- Decidable membership
_∋?_⦂_ : ∀ M x A → Dec (M ∋ x ⦂ A)
ϵ ∋? x ⦂ A                  = no λ ()
M , y ⦂ B ↦ w ∋? x ⦂ A
  with x ≟String y | A ≟Type B
...  | yes refl    | yes refl = yes here
...  | yes refl    | no  A≢B  = no λ { here          → A≢B refl
                                     ; (there x≢y _) → x≢y refl }
...  | no x≢y      | _
     with M ∋? x ⦂ A
...     | yes M∋x⦂A = yes (there x≢y M∋x⦂A)
...     | no ¬M∋x⦂A = no λ { here            → x≢y refl
                           ; (there x M∋x⦂A) → ¬M∋x⦂A M∋x⦂A }


--- Typing and evaluation are mutually recursive
data _⊢_ : Memory → Type → Set
⟦_⟧e     : M ⊢ A → ⟦ A ⟧T

-- Expressions are type judgments over a Memory
data _⊢_ where

  -- variables
  `_ : ∀ x →

    {True (M ∋? x ⦂ A)} →
    ---------
    M ⊢ A

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

    M ⊢ (S.if ⟦ b ⟧e then A else B)

private variable e e′ : M ⊢ A


-- Evaluation

-- variables
⟦ `_ _ {t} ⟧e = value (toWitness t)

-- integers
⟦ int k    ⟧e = k
⟦ - e      ⟧e = S.- ⟦ e ⟧e
⟦ e + e′   ⟧e = ⟦ e ⟧e S.+   ⟦ e′ ⟧e
⟦ e * e′   ⟧e = ⟦ e ⟧e S.*   ⟦ e′ ⟧e
⟦ e mod e′ ⟧e = ⟦ e ⟧e S.mod ⟦ e′ ⟧e

-- booleans
⟦ true     ⟧e = S.true
⟦ false    ⟧e = S.false
⟦ not e    ⟧e = S.not ⟦ e ⟧e
⟦ e and e′ ⟧e = ⟦ e ⟧e S.∧ ⟦ e′ ⟧e
⟦ e or e′  ⟧e = ⟦ e ⟧e S.∨ ⟦ e′ ⟧e

-- boolean equality
⟦ _==_ {A = ℤ}    e e′ ⟧e = ⟦ e ⟧e S.==ℤ ⟦ e′ ⟧e
⟦ _==_ {A = Bool} e e′ ⟧e = ⟦ e ⟧e S.==B ⟦ e′ ⟧e

-- ternary
⟦ if e then e′ else e″ ⟧e with ⟦ e ⟧e
... | S.true  = ⟦ e′ ⟧e
... | S.false = ⟦ e″ ⟧e
