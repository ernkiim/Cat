{-# OPTIONS --safe #-}

module Cat.SecurityLevels.Base where

open import Data.Empty
open import Data.Unit
open import Data.String using () renaming (String to Variable)
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Cat.MiniCat

--- Binary confidentiality lattice operations
data 𝟚 : Set where
  L H : 𝟚
variable ς ς′ ς₁ ς₂ ς₃ : 𝟚

data _≼_ : 𝟚 → 𝟚 → Set where
  refl : ς ≼ ς
  L≼H  : L ≼ H

_≽_ : 𝟚 → 𝟚 → Set
ς₁ ≽ ς₂ = ς₂ ≼ ς₁

_∨_ : 𝟚 → 𝟚 → 𝟚
L ∨ L = L
_ ∨ H = H
H ∨ _ = H

-- Assumed labeling of variables is fixed
ℒ : Variable → 𝟚
ℒ "lo"   = L
ℒ "lo₁"  = L
ℒ "lo₂"  = L
ℒ "low"  = L
ℒ "low₁" = L
ℒ "low₂" = L
ℒ _      = H

-- Memory equivalence
record _=[_]_ (ℳ₁ : Memory) (ς : 𝟚) (ℳ₂ : Memory) : Set where
  constructor _&_&_
  field
    =dom   : ℳ₁ =dom ℳ₂
    ⊆ς : ℒ x ≡ ς → ℳ₁ ⊢ var x ⇓ v → ℳ₂ ⊢ var x ⇓ v
    ⊇ς : ℒ x ≡ ς → ℳ₂ ⊢ var x ⇓ v → ℳ₁ ⊢ var x ⇓ v
  open _=dom_

-- Configuration trace equivalence, with proofs that the
-- final configurations are normal
data _=[_]ₙ_ : 𝒞₁ —→* 𝒞₁′ ↛ → 𝟚 → 𝒞₂ —→* 𝒞₂′ ↛ → Set where
  [_] : {n₁ : Normal (ℳ₁ , 𝒫)} {n₂ : Normal (ℳ₂ , 𝒫)} →
    ℳ₁ =[ ς ] ℳ₂ → refl n₁ =[ ς ]ₙ refl n₂
  _∷_ : {s₁ : (ℳ₁ , 𝒫) —→ 𝒞₁′} {s₂ : (ℳ₂ , 𝒫) —→ 𝒞₂′} →
        
    ℳ₁ =[ ς ] ℳ₂ → θ₁ =[ ς ]ₙ θ₂ → step s₁ θ₁ =[ ς ]ₙ step s₂ θ₂
-- Precedence
infixl 8 _≼_
infixl 9 _∨_
