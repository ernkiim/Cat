{-# OPTIONS --safe #-}

module Cat.SecurityLevels.Properties where

open import Relation.Binary.PropositionalEquality

open import Cat.SecurityLevels.Base

-- Properties of the lattice
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
