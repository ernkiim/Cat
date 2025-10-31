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

-- Contexts take variables to types
data Context : Set where
  ∅ : Context
  _,_∶_ : Context → Variable → Type → Context
variable Γ Γ₁ Γ₂ Γ′ : Context  

-- Lowering from Memory to Context (\rightsquigarrow)
⌊_⌋ : Memory → Context
⌊ ∅ ⌋ = ∅
⌊ ℳ , x ↦ (τ , _) ⌋ = ⌊ ℳ ⌋ , x ∶ τ

-- Expression type judgments: TUnop, TBinop are split into Tand, Tor, etc. to
-- avoid the partial function δ. TvarZero, Suc are rules for variable scoping
data _⊢_∶_ : Context → Expression → Type → Set where

  Tval : Γ ⊢ val (τ , V) ∶ τ

  TvarZero : (Γ , x ∶ τ) ⊢ var x ∶ τ
  TvarSuc : x ≢ y → Γ ⊢ var x ∶ τ → (Γ , y ∶ τ′) ⊢ var x ∶ τ

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

-- Program type judgments
data _⊢_OK : Context → Program → Set where
  TProgEmpty : Γ ⊢ ∅ OK
  TProg : Γ ⊢ e ∶ τ → (Γ , x ∶ τ) ⊢ 𝒫 OK → Γ ⊢ x ≔ e ⨾ 𝒫 OK

-- Configuration type judgments
data _OK : Configuration → Set where
  TConfig : ⌊ ℳ ⌋ ⊢ 𝒫 OK → (ℳ , 𝒫) OK
