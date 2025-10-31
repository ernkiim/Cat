{-# OPTIONS --safe #-}

module Cat.SecurityTyped.Properties where

open import Data.Product
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
open import Function

open import Cat.MiniCat
open import Cat.Typed
open import Cat.SecurityLevels

open import Cat.SecurityTyped.Base

=[ς]-ext : ℳ₁ =[ ς ] ℳ₂ → (ℳ₁ , x ↦ v) =[ ς ] (ℳ₂ , x ↦ v)
=[ς]-ext (=dom & ⊆ς & ⊇ς) = =dom-ext =dom &
  (λ { refl here⇓ → here⇓ ; refl (there⇓ x≢y rest) → there⇓ x≢y (⊆ς refl rest) }) &
   λ { refl here⇓ → here⇓ ; refl (there⇓ x≢y rest) → there⇓ x≢y (⊇ς refl rest) }

=[ς]-ext-≢ : ℳ₁ =[ ς ] ℳ₂ → ℒ x ≢ ς → (ℳ₁ , x ↦ v₁) =[ ς ] (ℳ₂ , x ↦ v₂)
=[ς]-ext-≢ (=dom & ⊆ς & ⊇ς) ℒx≢ς = =dom-ext =dom &
  (λ { refl here⇓ → contradiction refl ℒx≢ς ; refl (there⇓ x≢y rest) → there⇓ x≢y (⊆ς refl rest) }) &
   λ { refl here⇓ → contradiction refl ℒx≢ς ; refl (there⇓ x≢y rest) → there⇓ x≢y (⊇ς refl rest) }

-- Well-definedness a low-security expression (independent of ℳ) evaluates
-- the same over low-equivalent memories
=[L]-⇓-wf : ℳ₁ =[ L ] ℳ₂ → σ e ≡ L → ℳ₁ ⊢ e ⇓ v → ℳ₂ ⊢ e ⇓ v
=[L]-⇓-wf {e = var x} (=dom & ⊆ς & ⊇ς) σe≡L x⇓v = ⊆ς σe≡L x⇓v
=[L]-⇓-wf =[L] σe≡L val⇓ = val⇓
=[L]-⇓-wf =[L] σe≡L (not⇓ 𝒟₁) = not⇓ =[L]-⇓-wf =[L] σe≡L 𝒟₁
=[L]-⇓-wf =[L] σe≡L (𝒟₁ f-and⇓)    = =[L]-⇓-wf =[L] (L-⊥ (∨-≼ₗ (≡-≼ σe≡L))) 𝒟₁ f-and⇓
=[L]-⇓-wf =[L] σe≡L (𝒟₁ t-or⇓)     = =[L]-⇓-wf =[L] (L-⊥ (∨-≼ₗ (≡-≼ σe≡L))) 𝒟₁ t-or⇓
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

--- OKₛ typing properties

⌊_⌋ₛ : 𝒞 OKₛ → 𝒞 OK
⌊ STConfig ok ⌋ₛ = TConfig (lemma ok) where
  lemma : Γ ⊢ 𝒫 OKₛ → Γ ⊢ 𝒫 OK
  lemma STProgEmpty = TProgEmpty
  lemma (STProg {τ = τ} e∶τ ≼ℒx ok) = TProg e∶τ (lemma ok)

-- Lemma: —→ preserves OKₛ
OKₛ-preservation : 𝒞 OKₛ → 𝒞 —→ 𝒞′ → 𝒞′ OKₛ
OKₛ-preservation (STConfig (STProg e∶τ ≼ ok)) (assign e⇓v)
  with refl ← ⇓-functional e⇓v (proj₂ (τ-⇓ e∶τ)) = STConfig ok

-- Lemma: —→ preserves low-equivalence for OKₛ configurations
=[L]-preservation : (ℳ₁ , 𝒫) OKₛ → (ℳ₂ , 𝒫) OKₛ →
 (ℳ₁ , 𝒫) —→ (ℳ₁′ , 𝒫₁′) → (ℳ₂ , 𝒫) —→ (ℳ₂′ , 𝒫₂′) →
  ℳ₁ =[ L ] ℳ₂ → ℳ₁′ =[ L ] ℳ₂′
=[L]-preservation (STConfig (STProg {e = e} {x = x} _ _ _)) _ (assign ℳ₁⊢e⇓v) (assign ℳ₂⊢e⇓v′) =[L]
  with σ e in σe≡ | ℒ x in ℒx≡
... | _ | H = =[ς]-ext-≢ =[L] (H≢L ∘ trans (sym ℒx≡))
... | L | L with refl ← ⇓-functional (=[L]-⇓-wf =[L] σe≡ ℳ₁⊢e⇓v) ℳ₂⊢e⇓v′ = =[ς]-ext =[L]

-- Main Theorem. Traces θ are derivation trees of evaluation, with proofs
-- that the final configurations are normal (see Cat/MiniCat/Base.agda)
OKₛ-noninterference : (ℳ₁ , 𝒫) OKₛ → (ℳ₂ , 𝒫) OKₛ →
  (θ₁ : (ℳ₁ , 𝒫) —→* 𝒞₁ —̸→) (θ₂ : (ℳ₂ , 𝒫) —→* 𝒞₂ —̸→) →
  head θ₁ =[ L ] head θ₂ → θ₁ =[ L ]ₙ θ₂
OKₛ-noninterference ok₁ ok₂ [ —̸→₁ ] [ —̸→₂ ] =[L] = [ =[L] ]
OKₛ-noninterference ok₁ ok₂ [ —̸→₁ ] ((assign e⇓v) ∷ θ₂) =[L] = contradiction (OK-normal-∅ ⌊ ok₁ ⌋ₛ —̸→₁) λ ()
OKₛ-noninterference ok₁ ok₂ ((assign e⇓v) ∷ θ₂) [ —̸→₂ ] =[L] = contradiction (OK-normal-∅ ⌊ ok₂ ⌋ₛ —̸→₂) λ ()
OKₛ-noninterference ok₁ ok₂ ((assign e⇓v) ∷ θ₁) ((assign e⇓v′) ∷ θ₂) =[L] = 
  =[L] ∷ OKₛ-noninterference (OKₛ-preservation ok₁ (assign e⇓v))
                             (OKₛ-preservation ok₂ (assign e⇓v′))
                             θ₁ θ₂ (=[L]-preservation ok₁ ok₂ (assign e⇓v) (assign e⇓v′) =[L])


--- Decidability

_⊢OKₛ-decidable_ : ∀ Γ 𝒫 → Dec (Γ ⊢ 𝒫 OKₛ)
Γ ⊢OKₛ-decidable ∅ = yes STProgEmpty
Γ ⊢OKₛ-decidable (x ≔ e ⨾ 𝒫) with τ-decidable Γ e
... | no  ¬∃τ = no λ { (STProg 𝒟′ _ _) → ¬∃τ (_ , 𝒟′) }
... | yes (τ , 𝒟) with ≼-decidable (σ e) (ℒ x)
... | no  σe≻ℒx = no λ { (STProg _ σe≼ℒx _) → σe≻ℒx σe≼ℒx }
... | yes σe≼ℒx with (Γ , x ∶ τ) ⊢OKₛ-decidable 𝒫
... | yes rest = yes (STProg 𝒟 σe≼ℒx rest)
... | no ¬rest = no lemma where
  lemma : ¬ (Γ ⊢ x ≔ e ⨾ 𝒫 OKₛ)
  lemma (STProg 𝒟′ _ rest′) with refl ← τ-functional 𝒟 𝒟′ = ¬rest rest′

OKₛ-decidable : ∀ 𝒞 → Dec (𝒞 OKₛ)
OKₛ-decidable (ℳ , 𝒫) with ⌊ ℳ ⌋ ⊢OKₛ-decidable 𝒫
... | yes ok = yes (STConfig ok)
... | no ¬ok = no λ { (STConfig ok) → ¬ok ok }

