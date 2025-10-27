{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Typed Minicat (without security types)
------------------------------------------------------------------------

module Cat.Typed.Base where

open import Data.Product
open import Data.String using (_≟_)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality

open import Cat.MiniCat.Base
open import Cat.Meta as M using (Variable) renaming (true to t; false to f)

data Context : Set where
  ∅ : Context
  _,_∶_ : Context → Variable → Type → Context
variable Γ Γ₁ Γ₂ Γ′ : Context  

⌊_⌋ : Memory → Context
⌊ ∅ ⌋ = ∅
⌊ ℳ , x ↦ (τ , _) ⌋ = ⌊ ℳ ⌋ , x ∶ τ

data _∋_∶_ : Context → Variable → Type → Set where
  zero : Γ , x ∶ τ ∋ x ∶ τ
  suc  : x ≢ y → Γ ∋ x ∶ τ₁ → Γ , y ∶ τ₂ ∋ x ∶ τ₁

-- Type judgments are made directly over a memory
data _⊢_∶_ : Context → Expression → Type → Set where
  Tval : Γ ⊢ val (τ , V) ∶ τ
  Tvar : Γ ∋ x ∶ τ → Γ ⊢ var x ∶ τ

  Tnot_  : Γ ⊢ e ∶ bool → Γ ⊢ not e ∶ bool
  _Tand_ : Γ ⊢ e₁ ∶ bool → Γ ⊢ e₂ ∶ bool → Γ ⊢ e₁ and e₂ ∶ bool
  _Tor_  : Γ ⊢ e₁ ∶ bool → Γ ⊢ e₂ ∶ bool → Γ ⊢ e₁ or  e₂ ∶ bool
  _T==_  : Γ ⊢ e₁ ∶ int  → Γ ⊢ e₂ ∶ int  → Γ ⊢ e₁ ==  e₂ ∶ bool

  T-_    : Γ ⊢ e ∶ int → Γ ⊢ - e ∶ int
  _T+_   : Γ ⊢ e₁ ∶ int → Γ ⊢ e₂ ∶ int → Γ ⊢ e₁ + e₂ ∶ int
  _T-_   : Γ ⊢ e₁ ∶ int → Γ ⊢ e₂ ∶ int → Γ ⊢ e₁ - e₂ ∶ int
  _T*_   : Γ ⊢ e₁ ∶ int → Γ ⊢ e₂ ∶ int → Γ ⊢ e₁ * e₂ ∶ int
  _Tmod_ : Γ ⊢ e₁ ∶ int → Γ ⊢ e₂ ∶ int → Γ ⊢ e₁ mod e₂ ∶ int

  Tcond : Γ ⊢ e₁ ∶ bool → Γ ⊢ e₂ ∶ τ → Γ ⊢ e₃ ∶ τ →
    Γ ⊢ if e₁ then e₂ else e₃ ∶ τ

-- Program typing
data _⊢_OK : Context → Program → Set where
  TProgEmpty : Γ ⊢ ∅ OK
  TProg : Γ ⊢ e ∶ τ → (Γ , x ∶ τ) ⊢ 𝒫 OK → Γ ⊢ x ≔ e ⨾ 𝒫 OK

data _OK : Configuration → Set where
  TConfig : ⌊ ℳ ⌋ ⊢ 𝒫 OK → (ℳ , 𝒫) OK

--- Precedence
infixl 0 _∋_∶_
