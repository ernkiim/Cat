{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Security typed MiniCat
------------------------------------------------------------------------

module Cat.SecurityTyped.Base where

open import Data.Product using (_,_)
open import Cat.Typed
open import Cat.SecurityLevels

-- The security level ς is a total function of expressions
σ : Expression → 𝟚
σ (val v) = L
σ (var x) = ℒ x
σ (not e) = σ e
σ (e₁ and e₂) = σ e₁ ∨ σ e₂
σ (e₁ or e₂) = σ e₁ ∨ σ e₂
σ (e₁ == e₂) = σ e₂ ∨ σ e₂
σ (- e) = σ e
σ (e₁ + e₂) = σ e₂ ∨ σ e₂
σ (e₁ - e₂) = σ e₂ ∨ σ e₂
σ (e₁ * e₂) = σ e₂ ∨ σ e₂
σ (e₁ mod e₂) = σ e₂ ∨ σ e₂
σ (if e₁ then e₂ else e₃) = σ e₁ ∨ σ e₂ ∨ σ e₃

data _⊢_OKₛ : Context → Program → Set where

  STProgEmpty : Γ ⊢ ∅ OKₛ

  STProg :

    Γ ⊢ e ∶ τ  →  σ e ≼ ℒ x  →  (Γ , x ∶ τ) ⊢ 𝒫 OKₛ → 
    -----------------------------------------------
                 Γ ⊢ x ≔ e ⨾ 𝒫 OKₛ

data _OKₛ : Configuration → Set where
  STConfig : ⌊ ℳ ⌋ ⊢ 𝒫 OKₛ → (ℳ , 𝒫) OKₛ
