{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Properties of Typed MiniCat
------------------------------------------------------------------------

module Cat.Typed.Properties where

open import Data.Bool using (Bool; true; false)
open import Data.Product

open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable hiding (⌊_⌋)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality

import Cat.Meta as M
open import Cat.MiniCat

open import Cat.Typed.Base

--- Expression typing properties

∋-functional : Γ ∋ x ∶ τ₁ → Γ ∋ x ∶ τ₂ → τ₁ ≡ τ₂
∋-functional zero zero = refl
∋-functional zero (suc x≢x _) = contradiction refl x≢x
∋-functional (suc x≢x _) zero = contradiction refl x≢x
∋-functional (suc _ ∋₁) (suc _ ∋₂) = ∋-functional ∋₁ ∋₂

∋-decidable : ∀ ℳ x → Dec (∃[ τ ] (ℳ ∋ x ∶ τ))
∋-decidable ∅ _ = no λ ()
∋-decidable (ℳ , y ∶ τ) x with x M.≟S y
... | yes refl = yes (τ , zero)
... | no  ¬x≡y with ∋-decidable ℳ x
... | yes (τ , ℳ∋x) = yes (τ , suc ¬x≡y ℳ∋x)
... | no  ¬∃ℳ∋x      = no λ { (_ , zero) → ¬x≡y refl
                           ; (_ , suc _ ℳ∋x) → ¬∃ℳ∋x (_ , ℳ∋x) }

τ-functional : Γ ⊢ e ∶ τ₁ → Γ ⊢ e ∶ τ₂ → τ₁ ≡ τ₂
τ-functional Tval Tval = refl
τ-functional (Tvar ∋₁) (Tvar ∋₂) = ∋-functional ∋₁ ∋₂
τ-functional (Tnot 𝒟₁) (Tnot 𝒟₂) = refl
τ-functional (𝒟₁ Tand 𝒟₂) (𝒟₃ Tand 𝒟₄) = refl
τ-functional (𝒟₁ Tor 𝒟₂) (𝒟₃ Tor 𝒟₄) = refl
τ-functional (𝒟₁ T== 𝒟₂) (𝒟₃ T== 𝒟₄) = refl
τ-functional (T- 𝒟₁) (T- 𝒟₂) = refl
τ-functional (𝒟₁ T+ 𝒟₂) (𝒟₃ T+ 𝒟₄) = refl
τ-functional (𝒟₁ T- 𝒟₂) (𝒟₃ T- 𝒟₄) = refl
τ-functional (𝒟₁ T* 𝒟₂) (𝒟₃ T* 𝒟₄) = refl
τ-functional (𝒟₁ Tmod 𝒟₂) (𝒟₃ Tmod 𝒟₄) = refl
τ-functional (Tcond 𝒟₁ 𝒟₂ 𝒟₃) (Tcond 𝒟₄ 𝒟₅ 𝒟₆) = τ-functional 𝒟₂ 𝒟₅

τ-decidable : ∀ ℳ e → Dec (∃[ τ ] (ℳ ⊢ e ∶ τ))
τ-decidable ℳ (val (τ , _)) = yes (τ , Tval)
τ-decidable ℳ (var x) with ∋-decidable ℳ x
... | yes (τ , ℳ∋x) = yes (τ , Tvar ℳ∋x)
... | no  ¬∃ℳ∋x     = no λ { (_ , Tvar ℳ∋x) → ¬∃ℳ∋x (_ , ℳ∋x) }
τ-decidable ℳ (not e) with τ-decidable ℳ e
... | yes (int , 𝒟)  = no λ { (bool , (Tnot 𝒟′)) → contradiction (τ-functional 𝒟 𝒟′) λ () }
... | yes (bool , 𝒟) = yes (bool , (Tnot 𝒟))
... | no  ¬𝒟 = no λ { (bool , (Tnot 𝒟)) → ¬𝒟 (bool , 𝒟) }
τ-decidable ℳ (e₁ and e₂) with τ-decidable ℳ e₁ | τ-decidable ℳ e₂
... | yes (bool , 𝒟₁) | yes (bool , 𝒟₂) = yes (bool , (𝒟₁ Tand 𝒟₂))
... | yes (int , 𝒟₁)  | _ = no λ { (bool , (𝒟₁′ Tand 𝒟₂′)) → contradiction (τ-functional 𝒟₁ 𝒟₁′) λ () }
... | _  | yes (int , 𝒟₂) = no λ { (bool , (𝓓₁′ Tand 𝒟₂′)) → contradiction (τ-functional 𝒟₂ 𝒟₂′) λ () }
... | no ¬∃τ₁ | _ = no λ { (bool , (𝒟₁ Tand 𝒟₂)) → ¬∃τ₁ (bool , 𝒟₁) }
... | _ | no ¬∃τ₂ = no λ { (bool , (𝒟₁ Tand 𝒟₂)) → ¬∃τ₂ (bool , 𝒟₂) }
τ-decidable ℳ (e₁ or e₂) with τ-decidable ℳ e₁ | τ-decidable ℳ e₂
... | yes (bool , 𝒟₁) | yes (bool , 𝒟₂) = yes (bool , (𝒟₁ Tor 𝒟₂))
... | yes (int , 𝒟₁)  | _ = no λ { (bool , (𝒟₁′ Tor 𝒟₂′)) → contradiction (τ-functional 𝒟₁ 𝒟₁′) λ () }
... | _  | yes (int , 𝒟₂) = no λ { (bool , (𝓓₁′ Tor 𝒟₂′)) → contradiction (τ-functional 𝒟₂ 𝒟₂′) λ () }
... | no ¬∃τ₁ | _ = no λ { (bool , (𝒟₁ Tor 𝒟₂)) → ¬∃τ₁ (bool , 𝒟₁) }
... | _ | no ¬∃τ₂ = no λ { (bool , (𝒟₁ Tor 𝒟₂)) → ¬∃τ₂ (bool , 𝒟₂) }
τ-decidable ℳ (e₁ == e₂) with τ-decidable ℳ e₁ | τ-decidable ℳ e₂
... | yes (int , 𝒟₁) | yes (int , 𝒟₂) = yes (bool , (𝒟₁ T== 𝒟₂))
... | yes (bool , 𝒟₁) | _ = no λ { (bool , (𝒟₁′ T== 𝒟₂′)) → contradiction (τ-functional 𝒟₁ 𝒟₁′) λ () }
... | _ | yes (bool , 𝒟₂) = no λ { (bool , (𝒟₁′ T== 𝒟₂′)) → contradiction (τ-functional 𝒟₂ 𝒟₂′) λ () }
... | no ¬∃τ₁ | _ = no λ {(bool , (𝒟₁ T== 𝒟₂)) → ¬∃τ₁ (int , 𝒟₁) }
... | _ | no ¬∃τ₂ = no λ {(bool , (𝒟₁ T== 𝒟₂)) → ¬∃τ₂ (int , 𝒟₂) }
τ-decidable ℳ (- e) with τ-decidable ℳ e
... | yes (int , 𝒟)  = yes (int , (T- 𝒟))
... | yes (bool , 𝒟) = no λ { (int , (T- 𝒟′)) → contradiction (τ-functional 𝒟 𝒟′) λ () }
... | no  ¬∃τ        = no λ { (int , (T- 𝒟′)) → ¬∃τ (int , 𝒟′) }
τ-decidable ℳ (e₁ + e₂) with τ-decidable ℳ e₁ | τ-decidable ℳ e₂
... | yes (int , 𝒟₁) | yes (int , 𝒟₂) = yes (int , (𝒟₁ T+ 𝒟₂))
... | yes (bool , 𝒟₁) | _ = no λ { (int , (𝒟₁′ T+ 𝒟₂′)) → contradiction (τ-functional 𝒟₁ 𝒟₁′) λ () }
... | _ | yes (bool , 𝒟₂) = no λ { (int , (𝒟₁′ T+ 𝒟₂′)) → contradiction (τ-functional 𝒟₂ 𝒟₂′) λ () }
... | no ¬∃τ₁ | _ = no λ {(int , (𝒟₁ T+ 𝒟₂)) → ¬∃τ₁ (int , 𝒟₁) }
... | _ | no ¬∃τ₂ = no λ {(int , (𝒟₁ T+ 𝒟₂)) → ¬∃τ₂ (int , 𝒟₂) }
τ-decidable ℳ (e₁ - e₂) with τ-decidable ℳ e₁ | τ-decidable ℳ e₂
... | yes (int , 𝒟₁) | yes (int , 𝒟₂) = yes (int , (𝒟₁ T- 𝒟₂))
... | yes (bool , 𝒟₁) | _ = no λ { (int , (𝒟₁′ T- 𝒟₂′)) → contradiction (τ-functional 𝒟₁ 𝒟₁′) λ () }
... | _ | yes (bool , 𝒟₂) = no λ { (int , (𝒟₁′ T- 𝒟₂′)) → contradiction (τ-functional 𝒟₂ 𝒟₂′) λ () }
... | no ¬∃τ₁ | _ = no λ {(int , (𝒟₁ T- 𝒟₂)) → ¬∃τ₁ (int , 𝒟₁) }
... | _ | no ¬∃τ₂ = no λ {(int , (𝒟₁ T- 𝒟₂)) → ¬∃τ₂ (int , 𝒟₂) }
τ-decidable ℳ (e₁ * e₂) with τ-decidable ℳ e₁ | τ-decidable ℳ e₂
... | yes (int , 𝒟₁) | yes (int , 𝒟₂) = yes (int , (𝒟₁ T* 𝒟₂))
... | yes (bool , 𝒟₁) | _ = no λ { (int , (𝒟₁′ T* 𝒟₂′)) → contradiction (τ-functional 𝒟₁ 𝒟₁′) λ () }
... | _ | yes (bool , 𝒟₂) = no λ { (int , (𝒟₁′ T* 𝒟₂′)) → contradiction (τ-functional 𝒟₂ 𝒟₂′) λ () }
... | no ¬∃τ₁ | _ = no λ {(int , (𝒟₁ T* 𝒟₂)) → ¬∃τ₁ (int , 𝒟₁) }
... | _ | no ¬∃τ₂ = no λ {(int , (𝒟₁ T* 𝒟₂)) → ¬∃τ₂ (int , 𝒟₂) }
τ-decidable ℳ (e₁ mod e₂) with τ-decidable ℳ e₁ | τ-decidable ℳ e₂
... | yes (int , 𝒟₁) | yes (int , 𝒟₂) = yes (int , (𝒟₁ Tmod 𝒟₂))
... | yes (bool , 𝒟₁) | _ = no λ { (int , (𝒟₁′ Tmod 𝒟₂′)) → contradiction (τ-functional 𝒟₁ 𝒟₁′) λ () }
... | _ | yes (bool , 𝒟₂) = no λ { (int , (𝒟₁′ Tmod 𝒟₂′)) → contradiction (τ-functional 𝒟₂ 𝒟₂′) λ () }
... | no ¬∃τ₁ | _ = no λ {(int , (𝒟₁ Tmod 𝒟₂)) → ¬∃τ₁ (int , 𝒟₁) }
... | _ | no ¬∃τ₂ = no λ {(int , (𝒟₁ Tmod 𝒟₂)) → ¬∃τ₂ (int , 𝒟₂) }
τ-decidable ℳ (if e₁ then e₂ else e₃) with τ-decidable ℳ e₁ | τ-decidable ℳ e₂ | τ-decidable ℳ e₃
... | yes (int , 𝒟₁) | _ | _ = no λ { (_ , Tcond 𝒟₁′ 𝒟₂′ 𝒟₃′) → contradiction (τ-functional 𝒟₁ 𝒟₁′) λ () }
... | no ¬∃τ₁ | _ | _ = no λ { (τ , Tcond 𝒟₁′ 𝒟₂′ 𝒟₃′) → ¬∃τ₁ (bool , 𝒟₁′)  }
... | _ | no ¬∃τ₂ | _ = no λ { (τ , Tcond 𝒟₁′ 𝒟₂′ 𝒟₃′) → ¬∃τ₂ (_    , 𝒟₂′)  }
... | _ | _ | no ¬∃τ₃ = no λ { (τ , Tcond 𝒟₁′ 𝒟₂′ 𝒟₃′) → ¬∃τ₃ (_    , 𝒟₃′)  }
... | yes (bool , 𝒟₁) | yes (τ₂ , 𝒟₂) | yes (τ₃ , 𝒟₃) with τ₂ ≟τ τ₃
...   | yes refl  = yes (_ , Tcond 𝒟₁ 𝒟₂ 𝒟₃)
...   | no ¬τ₂≡τ₃ = no λ { (τ′ , Tcond 𝒟₁′ 𝒟₂′ 𝒟₃′) → ¬τ₂≡τ₃ (trans (τ-functional 𝒟₂ 𝒟₂′) (τ-functional 𝒟₃′ 𝒟₃)) }


-- Lemma 1.2: Typing predicts and guarantees evaluation of expressions
type-⇓ : ⌊ ℳ ⌋ ⊢ e ∶ τ → ∃[ v ] ℳ ⊢ e ⇓ (τ , v)
type-⇓ Tval = _ , val⇓
type-⇓ {ℳ , x ↦ V} (Tvar zero) = _ , here⇓
type-⇓ {ℳ , y ↦ W} (Tvar (suc y≢x ∋)) with type-⇓ (Tvar ∋)
... | v , ⇓v = v , there⇓ y≢x ⇓v
type-⇓ (Tnot 𝒟) with type-⇓ 𝒟
... | b , ⇓b = M.not b , (not⇓ ⇓b)
type-⇓ (𝒟₁ Tand 𝒟₂) with type-⇓ 𝒟₁
... | false , ⇓f = false , f-and⇓ ⇓f
... | true  , ⇓t with type-⇓ 𝒟₂
... | b , ⇓b = b , t-and⇓ ⇓t ⇓b
type-⇓ (𝒟₁ Tor 𝒟₂) with type-⇓ 𝒟₁
... | true , ⇓t = true , t-or⇓ ⇓t
... | false , ⇓f with type-⇓ 𝒟₂
... | b , ⇓b  = b , f-or⇓ ⇓f ⇓b
type-⇓ (𝒟₁ T== 𝒟₂) with type-⇓ 𝒟₁ | type-⇓ 𝒟₂
... | m , ⇓m | n , ⇓n = m M.== n , (⇓m ==⇓ ⇓n)
type-⇓ (T- 𝒟₁) with type-⇓ 𝒟₁
... | n , ⇓n = M.- n , -⇓ ⇓n
type-⇓ (𝒟₁ T+ 𝒟₂) with type-⇓ 𝒟₁ | type-⇓ 𝒟₂
... | m , ⇓m | n , ⇓n = m M.+ n , ⇓m +⇓ ⇓n
type-⇓ (𝒟₁ T- 𝒟₂) with type-⇓ 𝒟₁ | type-⇓ 𝒟₂
... | m , ⇓m | n , ⇓n = m M.- n , (⇓m -⇓ ⇓n)
type-⇓ (𝒟₁ T* 𝒟₂) with type-⇓ 𝒟₁ | type-⇓ 𝒟₂
... | m , ⇓m | n , ⇓n = m M.* n , ⇓m *⇓ ⇓n
type-⇓ (𝒟₁ Tmod 𝒟₂) with type-⇓ 𝒟₁ | type-⇓ 𝒟₂
... | m , ⇓m | n , ⇓n = m M.mod n , ⇓m mod⇓ ⇓n
type-⇓ (Tcond 𝒟₁ 𝒟₂ 𝒟₃) with type-⇓ 𝒟₁
type-⇓ (Tcond 𝒟₁ 𝒟₂ 𝒟₃) | true  , ⇓t with type-⇓ 𝒟₂
... | v , ⇓v = v , then⇓ ⇓t ⇓v
type-⇓ (Tcond 𝒟₁ 𝒟₂ 𝒟₃) | false , ⇓f with type-⇓ 𝒟₃
... | v , v⇓ = v , else⇓ ⇓f v⇓

--- Program typing

OK-preservation : 𝒞 OK → 𝒞 —→ 𝒞′ → 𝒞′ OK
OK-preservation (TConfig (TProg e∶τ ok)) (assign e⇓v) with ⇓-functional e⇓v (type-⇓ e∶τ .proj₂)
... | refl = TConfig ok

OK-doesn't-go-wrong : 𝒞 OK → ∃[ ℳ′ ] 𝒞 —→* (ℳ′ , ∅)
OK-doesn't-go-wrong (TConfig ok) = OK-doesn't-go-wrongₚ ok where
  OK-doesn't-go-wrongₚ : ⌊ ℳ ⌋ ⊢ 𝒫 OK → ∃[ ℳ′ ] (ℳ , 𝒫) —→* (ℳ′ , ∅)
  OK-doesn't-go-wrongₚ TProgEmpty = _ , refl (_ , ∅)
  OK-doesn't-go-wrongₚ {ℳ} {x ≔ e ⨾ 𝒫} (TProg e∶τ ok) with type-⇓ e∶τ
  ... | v , e⇓v with OK-doesn't-go-wrongₚ {ℳ = ℳ , x ↦ (_ , v)} ok
  ... | ℳ′ , eval = ℳ′ , step (ℳ , x ≔ e ⨾ 𝒫) (assign e⇓v) eval
