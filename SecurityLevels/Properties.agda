{-# OPTIONS --safe #-}

module Cat.SecurityLevels.Properties where

open import Function

open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

open import Cat.SecurityLevels.Base

-- Properties of the lattice
≡-≼ : ς ≡ ς′ → ς ≼ ς′
≡-≼ refl = refl 

L≼ς : L ≼ ς
L≼ς {L} = refl
L≼ς {H} = L≼H

L-⊥ : ς ≼ L → ς ≡ L
L-⊥ refl = refl

ς≼H : ς ≼ H
ς≼H {L} = L≼H
ς≼H {H} = refl

L≢H : L ≢ H
L≢H = λ ()

H≢L : H ≢ L
H≢L = λ ()

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

≼-trans : ς₁ ≼ ς₂ → ς₂ ≼ ς₃ → ς₁ ≼ ς₃
≼-trans refl refl = refl
≼-trans refl L≼H = L≼H
≼-trans L≼H refl = L≼H

≼-∨ₗ : ς₁ ≼ ς₁ ∨ ς₂
≼-∨ₗ {L} {ς₂} = L≼ς
≼-∨ₗ {H} {L} = refl
≼-∨ₗ {H} {H} = refl

≼-∨ᵣ : ς₂ ≼ ς₁ ∨ ς₂
≼-∨ᵣ {ς₁} {ς₂} with ς₂ ∨ ς₁ | ∨-comm {ς₁} {ς₂}
...               | _       | refl = ≼-∨ₗ

∨-≼ₗ : ς₁ ∨ ς₂ ≼ ς₃ → ς₁ ≼ ς₃
∨-≼ₗ ∨≼ = ≼-trans ≼-∨ₗ ∨≼

∨-≼ᵣ : ς₁ ∨ ς₂ ≼ ς₃ → ς₂ ≼ ς₃
∨-≼ᵣ ∨≼ = ≼-trans ≼-∨ᵣ ∨≼

≼-decidable : ∀ ς₁ ς₂ → Dec (ς₁ ≼ ς₂)
≼-decidable L L = yes refl
≼-decidable L H = yes L≼H
≼-decidable H L = no λ ()
≼-decidable H H = yes refl
