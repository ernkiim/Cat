------------------------------------------------------------------------
-- Typed MiniCat formalized without security semantics
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MiniCat where

open import Data.Char using (Char) renaming (_≟_ to _≟Char_)
open import Data.String using (String) renaming (_≟_ to _≟String_)
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable hiding (⌊_⌋)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions
import MetaCat as S
open S using (+_; +[1+_]; -[1+_]) renaming (true to t; false to f)

open import Data.Product


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
_≟Type_ : DecidableEquality Type
ℤ    ≟Type ℤ    = yes refl
ℤ    ≟Type Bool = no λ ()
Bool ≟Type ℤ    = no λ ()
Bool ≟Type Bool = yes refl


--- Variables
Variable = String

record VariableTyping : Set where
  constructor _⦂_
  field
    var : Variable
    type : Type

private variable x y : Variable


--- Memories
data Memory : Set where
  ϵ     : Memory
  _,_↦_ : Memory → Variable → ⟦ A ⟧T → Memory

private variable M M′ M″ : Memory

-- References are to in-scope variables
data _∋_ : Memory → VariableTyping → Set where
  here : {v : ⟦ A ⟧T} → M , x ↦ v ∋ x ⦂ A
  there : {w : ⟦ B ⟧T} → x ≢ y → M ∋ x ⦂ A → M , y ↦ w ∋ x ⦂ A

private variable r : M ∋ x ⦂ A

-- Look up reference
lookup : M ∋ x ⦂ A → ⟦ A ⟧T
lookup (here {v = v}) = v
lookup (there _ r)    = lookup r

-- Variable's well-scropedness is decidable
_∋?_ : ∀ M x⦂A → Dec (M ∋ x⦂A)
ϵ ∋? x ⦂ A = no λ ()
(_,_↦_ {A = B} M y w) ∋? x ⦂ A with x ≟String y | B  ≟Type A
... | yes refl | yes refl = yes here
... | yes refl | no ¬A≢B  = no λ { here → ¬A≢B refl ; (there x≢y _) → x≢y refl }
... | no ¬x≢y  | _ with M ∋? x ⦂ A
...   | yes M∋x⦂A = yes (there ¬x≢y M∋x⦂A)
...   | no ¬M∋x⦂A = no λ { here → ¬x≢y refl ; (there x≢y M∋x⦂A) → ¬M∋x⦂A M∋x⦂A }

-- Try to synthesize proof of scope
_∋!_ : Memory → VariableTyping → Set
M ∋! (x ⦂ A) = True (M ∋? x ⦂ A)


--- Typing and evaluation are mutually recursive

data _⊢_ (M : Memory) : Type → Set
⟦_⟧ : M ⊢ A → ⟦ A ⟧T

-- Expressions are type judgments over a Memory
data _⊢_ M where

  `_ : ∀ x → {M ∋! x ⦂ A} → M ⊢ A

  int_          : S.ℤ → M ⊢ ℤ
  -_            : M ⊢ ℤ → M ⊢ ℤ
  _+_ _*_ _mod_ : M ⊢ ℤ → M ⊢ ℤ → M ⊢ ℤ

  true       : M ⊢ Bool
  false      : M ⊢ Bool
  not_       : M ⊢ Bool → M ⊢ Bool
  _and_ _or_ : M ⊢ Bool → M ⊢ Bool → M ⊢ Bool

  _==_ : M ⊢ A → M ⊢ A → M ⊢ Bool

  if_then_else_ :

    (b : M ⊢ Bool) → M ⊢ A → M ⊢ B →
    ------------------------------
    M ⊢ (S.if ⟦ b ⟧ then A else B)

private variable e e₁ e₂ : M ⊢ A

-- Evaluation
⟦ `_ _ {tt} ⟧ = lookup (toWitness tt)

⟦ int k     ⟧ = k
⟦ - e       ⟧ = S.- ⟦ e ⟧
⟦ e₁  +  e₂ ⟧ = ⟦ e₁ ⟧ S.+   ⟦ e₂ ⟧
⟦ e₁  *  e₂ ⟧ = ⟦ e₁ ⟧ S.*   ⟦ e₂ ⟧
⟦ e₁ mod e₂ ⟧ = ⟦ e₁ ⟧ S.mod ⟦ e₂ ⟧

⟦ true      ⟧ = t
⟦ false     ⟧ = f
⟦ not e     ⟧ = S.not ⟦ e ⟧
⟦ e₁ and e₂ ⟧ = ⟦ e₁ ⟧ S.∧ ⟦ e₂ ⟧
⟦ e₁ or  e₂ ⟧ = ⟦ e₁ ⟧ S.∨ ⟦ e₂ ⟧

⟦ _==_ {A = ℤ}    e₁ e₂ ⟧ = ⟦ e₁ ⟧ S.==ℤ ⟦ e₂ ⟧
⟦ _==_ {A = Bool} e₁ e₂ ⟧ = ⟦ e₁ ⟧ S.==B ⟦ e₂ ⟧

⟦ if e₁ then e₂ else e₃ ⟧ with ⟦ e₁ ⟧
... | t = ⟦ e₂ ⟧
... | f = ⟦ e₃ ⟧


--- Precedence declarations

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
infixl 3 _∋_ _∋?_ _∋!_
infixl 4 _⦂_

infixl 4 _,_↦_
