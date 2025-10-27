{-# OPTIONS --safe #-}

module Cat.SecurityTyped.Properties where

open import Data.Product

open import Cat.MiniCat
open import Cat.SecurityLevels
open import Cat.SecurityTyped.Base

—→OKₛ-preserves-=L :
  (ℳ₁ , 𝒫) OKₛ → (ℳ₂ , 𝒫) OKₛ →
  (ℳ₁ , 𝒫) —→ (ℳ₁′ , 𝒫′) →
  (ℳ₂ , 𝒫) —→ (ℳ₂′ , 𝒫′) →
  ℳ₁ =[ L ] ℳ₂ → ℳ₁′ =[ L ] ℳ₂′
—→OKₛ-preserves-=L (STConfig (STProg x x₁ x₂)) (STConfig (STProg x₃ x₄ x₅)) (assign e⇓v₁) (assign e⇓v₂) (=dom , =level) = {!!}
