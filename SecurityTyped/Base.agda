{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- Security typed MiniCat
------------------------------------------------------------------------

module Cat.SecurityTyped.Base where

open import Data.Product using (_,_)
open import Cat.Typed
open import Cat.SecurityLevels

-- The security level ς is a total function of expressions,
-- independent of ℳ.
σ : Expression → 𝟚
σ (val v) = L
σ (var x) = ℒ x
σ (not e) = σ e
σ (e₁ and e₂) = σ e₁ ∨ σ e₂
σ (e₁ or e₂) = σ e₁ ∨ σ e₂
σ (e₁ == e₂) = σ e₁ ∨ σ e₂
σ (- e) = σ e
σ (e₁ + e₂) = σ e₁ ∨ σ e₂
σ (e₁ - e₂) = σ e₁ ∨ σ e₂
σ (e₁ * e₂) = σ e₁ ∨ σ e₂
σ (e₁ mod e₂) = σ e₁ ∨ σ e₂
σ (if e₁ then e₂ else e₃) = σ e₁ ∨ σ e₂ ∨ σ e₃

data _⊢_OKₛ : Context → Program → Set where

  STProgEmpty : Γ ⊢ ∅ OKₛ

  -- Can reuse the typing judgment from Cat.Typed
  STProg :

    Γ ⊢ e ∶ τ  →  σ e ≼ ℒ x  →  (Γ , x ∶ τ) ⊢ 𝒫 OKₛ → 
    -----------------------------------------------
                   Γ ⊢ x ≔ e ⨾ 𝒫 OKₛ

data _OKₛ : Configuration → Set where
  STConfig : ⌊ ℳ ⌋ ⊢ 𝒫 OKₛ → (ℳ , 𝒫) OKₛ


-- Memory equivalence
record _=[_]_ (ℳ₁ : Memory) (ς : 𝟚) (ℳ₂ : Memory) : Set where
  constructor _&_&_
  field
    =dom   : ℳ₁ =dom ℳ₂
    ⊆ς : ℒ x ≡ ς → ℳ₁ ⊢ var x ⇓ v → ℳ₂ ⊢ var x ⇓ v
    ⊇ς : ℒ x ≡ ς → ℳ₂ ⊢ var x ⇓ v → ℳ₁ ⊢ var x ⇓ v
  open _=dom_

-- Equivalence of traces (we use derivation trees of reduction as traces)
data _=[_]ₙ_ : 𝒞₁ —→* 𝒞₁′ —̸→ → 𝟚 → 𝒞₂ —→* 𝒞₂′ —̸→ → Set where
  [_] : {n₁ : Normal (ℳ₁ , 𝒫)} {n₂ : Normal (ℳ₂ , 𝒫)} →
    ℳ₁ =[ ς ] ℳ₂ → refl n₁ =[ ς ]ₙ refl n₂
  _∷_ : {s₁ : (ℳ₁ , 𝒫) —→ 𝒞₁′} {s₂ : (ℳ₂ , 𝒫) —→ 𝒞₂′} →
    ℳ₁ =[ ς ] ℳ₂ → θ₁ =[ ς ]ₙ θ₂ → step s₁ θ₁ =[ ς ]ₙ step s₂ θ₂
