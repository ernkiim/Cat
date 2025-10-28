{-# OPTIONS --safe #-}

module Cat.SecurityTyped.Properties where

open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Cat.MiniCat
open import Cat.Typed
open import Cat.SecurityLevels

open import Cat.SecurityTyped.Base

=[ς]-sym : ℳ₁ =[ ς ] ℳ₂ → ℳ₂ =[ ς ] ℳ₁
=[ς]-sym ((⊆dom & ⊇dom) & ⊆ς & ⊇ς) = (⊇dom & ⊆dom) & ⊇ς & ⊆ς

=[L]-τ-wf : ℳ₁ =[ L ] ℳ₂ → σ e ≡ L → ⌊ ℳ₁ ⌋ ⊢ e ∶ τ → ⌊ ℳ₂ ⌋ ⊢ e ∶ τ
=[L]-τ-wf {ℳ₁ , y ↦ (τ , w)} {e = var x} (=dom & ⊆ς & ⊇ς) ℒx≡L 𝒟 = var-⇓-τ (⊆ς ℒx≡L (proj₂ (τ-⇓ 𝒟)))
=[L]-τ-wf =[L] σe≡L Tval = Tval
=[L]-τ-wf =[L] σe≡L (Tnot 𝒟) = Tnot =[L]-τ-wf =[L] σe≡L 𝒟
=[L]-τ-wf =[L] σe≡L (T- 𝒟)   = T- =[L]-τ-wf =[L] σe≡L 𝒟
=[L]-τ-wf =[L] σe≡L (𝒟₁ Tand 𝒟₂) = =[L]-τ-wf =[L] (L-⊥ (∨-≼ₗ (≡-≼ σe≡L))) 𝒟₁ Tand =[L]-τ-wf =[L] (L-⊥ (∨-≼ᵣ (≡-≼ σe≡L))) 𝒟₂
=[L]-τ-wf =[L] σe≡L (𝒟₁ Tor 𝒟₂)  = =[L]-τ-wf =[L] (L-⊥ (∨-≼ₗ (≡-≼ σe≡L))) 𝒟₁ Tor  =[L]-τ-wf =[L] (L-⊥ (∨-≼ᵣ (≡-≼ σe≡L))) 𝒟₂
=[L]-τ-wf =[L] σe≡L (𝒟₁ T== 𝒟₂)  = =[L]-τ-wf =[L] (L-⊥ (∨-≼ₗ (≡-≼ σe≡L))) 𝒟₁ T==  =[L]-τ-wf =[L] (L-⊥ (∨-≼ᵣ (≡-≼ σe≡L))) 𝒟₂
=[L]-τ-wf =[L] σe≡L (𝒟₁ T+ 𝒟₂)   = =[L]-τ-wf =[L] (L-⊥ (∨-≼ₗ (≡-≼ σe≡L))) 𝒟₁ T+   =[L]-τ-wf =[L] (L-⊥ (∨-≼ᵣ (≡-≼ σe≡L))) 𝒟₂
=[L]-τ-wf =[L] σe≡L (𝒟₁ T- 𝒟₂)   = =[L]-τ-wf =[L] (L-⊥ (∨-≼ₗ (≡-≼ σe≡L))) 𝒟₁ T-   =[L]-τ-wf =[L] (L-⊥ (∨-≼ᵣ (≡-≼ σe≡L))) 𝒟₂
=[L]-τ-wf =[L] σe≡L (𝒟₁ T* 𝒟₂)   = =[L]-τ-wf =[L] (L-⊥ (∨-≼ₗ (≡-≼ σe≡L))) 𝒟₁ T*   =[L]-τ-wf =[L] (L-⊥ (∨-≼ᵣ (≡-≼ σe≡L))) 𝒟₂
=[L]-τ-wf =[L] σe≡L (𝒟₁ Tmod 𝒟₂) = =[L]-τ-wf =[L] (L-⊥ (∨-≼ₗ (≡-≼ σe≡L))) 𝒟₁ Tmod =[L]-τ-wf =[L] (L-⊥ (∨-≼ᵣ (≡-≼ σe≡L))) 𝒟₂
=[L]-τ-wf =[L] σe≡L (Tcond 𝒟₁ 𝒟₂ 𝒟₃) = Tcond
  (=[L]-τ-wf =[L] (L-⊥ (∨-≼ₗ (∨-≼ₗ (≡-≼ σe≡L)))) 𝒟₁)
  (=[L]-τ-wf =[L] (L-⊥ (∨-≼ᵣ (∨-≼ₗ (≡-≼ σe≡L)))) 𝒟₂)
  (=[L]-τ-wf =[L] (L-⊥ (∨-≼ᵣ (≡-≼ σe≡L))) 𝒟₃)

=[L]-⇓-wf : ℳ₁ =[ L ] ℳ₂ → σ e ≡ L → ℳ₁ ⊢ e ⇓ v → ℳ₂ ⊢ e ⇓ v
=[L]-⇓-wf {e = var x} (=dom & ⊆ς & ⊇ς) σe≡L x⇓v = ⊆ς σe≡L x⇓v
=[L]-⇓-wf =[L] σe≡L val⇓ = val⇓
=[L]-⇓-wf =[L] σe≡L (not⇓ 𝒟₁) = not⇓ =[L]-⇓-wf =[L] σe≡L 𝒟₁
=[L]-⇓-wf =[L] σe≡L (𝒟₁ f-and⇓) = (=[L]-⇓-wf =[L] (L-⊥ (∨-≼ₗ (≡-≼ σe≡L))) 𝒟₁) f-and⇓
=[L]-⇓-wf =[L] σe≡L (𝒟₁ t-or⇓)  = (=[L]-⇓-wf =[L] (L-⊥ (∨-≼ₗ (≡-≼ σe≡L))) 𝒟₁) t-or⇓
=[L]-⇓-wf =[L] σe≡L (𝒟₁ t-and⇓ 𝒟₂) = =[L]-⇓-wf =[L] (L-⊥ (∨-≼ₗ (≡-≼ σe≡L))) 𝒟₁ t-and⇓ =[L]-⇓-wf =[L] (L-⊥ (∨-≼ᵣ (≡-≼ σe≡L))) 𝒟₂
=[L]-⇓-wf =[L] σe≡L (𝒟₁ f-or⇓  𝒟₂) = =[L]-⇓-wf =[L] (L-⊥ (∨-≼ₗ (≡-≼ σe≡L))) 𝒟₁ f-or⇓ =[L]-⇓-wf =[L] (L-⊥ (∨-≼ᵣ (≡-≼ σe≡L))) 𝒟₂
=[L]-⇓-wf =[L] σe≡L (𝒟₁ ==⇓    𝒟₂) = =[L]-⇓-wf =[L] (L-⊥ (∨-≼ₗ (≡-≼ σe≡L))) 𝒟₁ ==⇓ =[L]-⇓-wf =[L] (L-⊥ (∨-≼ᵣ (≡-≼ σe≡L))) 𝒟₂
=[L]-⇓-wf =[L] σe≡L (-⇓ 𝒟₁)      = -⇓ =[L]-⇓-wf =[L] σe≡L 𝒟₁
=[L]-⇓-wf =[L] σe≡L (𝒟₁ +⇓ 𝒟₂)   = =[L]-⇓-wf =[L] (L-⊥ (∨-≼ₗ (≡-≼ σe≡L))) 𝒟₁ +⇓ =[L]-⇓-wf =[L] (L-⊥ (∨-≼ᵣ (≡-≼ σe≡L))) 𝒟₂
=[L]-⇓-wf =[L] σe≡L (𝒟₁ -⇓ 𝒟₂)   = =[L]-⇓-wf =[L] (L-⊥ (∨-≼ₗ (≡-≼ σe≡L))) 𝒟₁ -⇓ =[L]-⇓-wf =[L] (L-⊥ (∨-≼ᵣ (≡-≼ σe≡L))) 𝒟₂
=[L]-⇓-wf =[L] σe≡L (𝒟₁ *⇓ 𝒟₂)   = =[L]-⇓-wf =[L] (L-⊥ (∨-≼ₗ (≡-≼ σe≡L))) 𝒟₁ *⇓ =[L]-⇓-wf =[L] (L-⊥ (∨-≼ᵣ (≡-≼ σe≡L))) 𝒟₂
=[L]-⇓-wf =[L] σe≡L (𝒟₁ mod⇓ 𝒟₂) = =[L]-⇓-wf =[L] (L-⊥ (∨-≼ₗ (≡-≼ σe≡L))) 𝒟₁ mod⇓ =[L]-⇓-wf =[L] (L-⊥ (∨-≼ᵣ (≡-≼ σe≡L))) 𝒟₂
=[L]-⇓-wf =[L] σe≡L (then⇓ 𝒟₁ 𝒟₂) = then⇓ (=[L]-⇓-wf =[L] (L-⊥ (∨-≼ₗ (∨-≼ₗ (≡-≼ σe≡L)))) 𝒟₁) (=[L]-⇓-wf =[L] (L-⊥ (∨-≼ᵣ (∨-≼ₗ (≡-≼ σe≡L)))) 𝒟₂)
=[L]-⇓-wf =[L] σe≡L (else⇓ 𝒟₁ 𝒟₃) = else⇓ (=[L]-⇓-wf =[L] (L-⊥ (∨-≼ₗ (∨-≼ₗ (≡-≼ σe≡L)))) 𝒟₁) (=[L]-⇓-wf =[L] (L-⊥ (∨-≼ᵣ (≡-≼ σe≡L))) 𝒟₃)

=[L]-preservation :
  (ℳ₁ , 𝒫) —→ (ℳ₁′ , 𝒫′) →
  (ℳ₂ , 𝒫) —→ (ℳ₂′ , 𝒫′) →
  ℳ₁ =[ L ] ℳ₂ → ℳ₁′ =[ L ] ℳ₂′
=[L]-preservation {𝒫 = 𝒫} {𝒫′ = 𝒫′} (assign {e = e} e⇓v₁) (assign e⇓v₂) ((⊆dom & ⊇dom) & ⊆ς & ⊇ς) = record
  { =dom = =dom-preservation {𝒫 = 𝒫} {𝒫′ = 𝒫′} (assign e⇓v₁) (assign e⇓v₂) (⊆dom & ⊇dom)
  ; ⊆ς = {!!}
  ; ⊇ς = {!!}
  } where

  incl₁ : {!!}
  
  
