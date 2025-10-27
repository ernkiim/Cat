{-# OPTIONS --safe #-}

module Cat.SecurityLevels.Base where

open import Data.List.NonEmpty
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
  constructor _,_
  field
    =dom   : ℳ₁ =dom ℳ₂
    =level : ℒ x ≡ ς → ℳ₁ ⊢ var x ⇓ v₁ → ℳ₂ ⊢ var x ⇓ v₂ → v₁ ≡ v₂
  open _=dom_

-- ctrace—→ : 𝒞 —→* 𝒞′ → List⁺ Configuration
-- ctrace—→ {𝒞} refl = [ 𝒞 ]
-- ctrace—→ {𝒞} (step ⇓ xs) = {!𝒞 ∷ rec xs!} where
--   rec : 

-- Precedence
infixl 8 _≼_
infixl 9 _∨_
