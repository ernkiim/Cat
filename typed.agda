------------------------------------------------------------------------
-- Security Typed Minicat
------------------------------------------------------------------------

module Typed where

open import Data.Product
open import Data.String using (_≟_)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality
open import MiniCat hiding (Memory; Configuration)

open import MetaCat as M using (Variable) renaming (true to t; false to f)

-- Contexts take variables to types
data Context : Set where
  ∅     : Context
  _,_∶_ : Context → Variable → Type → Context
variable Γ : Context

data _∋_∶_ : Context → Variable → Type → Set where
  zero : Γ , x ∶ τ ∋ x ∶ τ
  suc  : {x ≢ y} → Γ ∋ x ∶ τ₁ → Γ , y ∶ τ₂ ∋ x ∶ τ₁

-- Type judgments
data _⊢_∶_ : Context → Expression → Type → Set where
  Tval : ∀ {v : ⟦ τ ⟧τ} → Γ ⊢ val (τ , v) ∶ τ
  Tvar : Γ ∋ x ∶ τ → Γ ⊢ var x ∶ τ
  Tnot : Γ ⊢ e ∶ bool → Γ ⊢ not e ∶ bool

--- Precedence
infixl 0 _∋_∶_ _⊢_∶_·_ _—→_

infixl 1 _,_∶_
