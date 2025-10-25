{-# OPTIONS --safe #-}

module Levels where

open import Data.String using () renaming (String to Variable)
open import Relation.Binary.PropositionalEquality

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

ℒ : Variable → 𝟚
ℒ "lo"   = L
ℒ "lo₁"  = L
ℒ "lo₂"  = L
ℒ "low"  = L
ℒ "low₁" = L
ℒ "low₂" = L
ℒ _      = H

-- Proofs
L≼ς : L ≼ ς
L≼ς {L} = refl
L≼ς {H} = L≼H

ς≼H : ς ≼ H
ς≼H {L} = L≼H
ς≼H {H} = refl

∨-comm : ς₁ ∨ ς₂ ≡ ς₂ ∨ ς₁
∨-comm {L} {L} = refl
∨-comm {L} {H} = refl
∨-comm {H} {L} = refl
∨-comm {H} {H} = refl

H∨ς≡H : H ∨ ς ≡ H
H∨ς≡H {L} = refl
H∨ς≡H {H} = refl

ς∨H≡H : ς ∨ H ≡ H
ς∨H≡H {ς} = trans ∨-comm H∨ς≡H

≼-∨ₗ : ς₁ ≼ ς₁ ∨ ς₂
≼-∨ₗ {L} {ς₂} = L≼ς
≼-∨ₗ {H} {L} = refl
≼-∨ₗ {H} {H} = refl

≼-∨ᵣ : ς₂ ≼ ς₁ ∨ ς₂
≼-∨ᵣ {ς₁} {ς₂} with ς₂ ∨ ς₁ | ∨-comm {ς₁} {ς₂}
...               | _       | refl = ≼-∨ₗ


-- Precedence
infixl 8 _≼_
infixl 9 _∨_
