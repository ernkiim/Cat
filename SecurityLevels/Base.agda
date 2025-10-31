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



-- Precedence
infixl 8 _≼_
infixl 9 _∨_
