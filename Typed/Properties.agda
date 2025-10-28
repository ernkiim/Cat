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

τ-functional : Γ ⊢ e ∶ τ₁ → Γ ⊢ e ∶ τ₂ → τ₁ ≡ τ₂
τ-functional Tval Tval = refl
τ-functional TvarZero TvarZero = refl
τ-functional TvarZero (TvarSuc {x} x≢x 𝒟) = contradiction refl x≢x
τ-functional (TvarSuc {x} x≢x 𝒟) TvarZero = contradiction refl x≢x
τ-functional (TvarSuc _ 𝒟₁) (TvarSuc _ 𝒟₂) = τ-functional 𝒟₁ 𝒟₂
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
τ-decidable ∅ (var x) = no λ ()
τ-decidable (ℳ , y ∶ τ) (var x) with x M.≟S y
... | no x≢y with τ-decidable ℳ (var x)
... | yes (τ , 𝒟) = yes (τ , TvarSuc x≢y 𝒟)
... | no  ¬∃τ = no λ { (τ , TvarZero)     → x≢y refl
                     ; (τ , TvarSuc _ 𝒟′) → ¬∃τ (τ , 𝒟′) }
τ-decidable (ℳ , y ∶ τ) (var x) | yes refl = yes (τ , TvarZero)
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
τ-⇓ : ⌊ ℳ ⌋ ⊢ e ∶ τ → ∃[ v ] ℳ ⊢ e ⇓ (τ , v)
τ-⇓ Tval = _ , val⇓
τ-⇓ {ℳ = ℳ , x ↦ (τ  , v)} TvarZero = v , here⇓
τ-⇓ {ℳ = ℳ , y ↦ (τ′ , w)} (TvarSuc x≢y 𝒟) with τ-⇓ 𝒟
... | v , 𝒟′ = v , there⇓ x≢y 𝒟′
τ-⇓ (Tnot 𝒟) with τ-⇓ 𝒟
... | b , ⇓b = M.not b , (not⇓ ⇓b)
τ-⇓ (𝒟₁ Tand 𝒟₂) with τ-⇓ 𝒟₁
... | false , ⇓f = false , ⇓f f-and⇓
... | true  , ⇓t with τ-⇓ 𝒟₂
... | b , ⇓b = b , ⇓t t-and⇓ ⇓b
τ-⇓ (𝒟₁ Tor 𝒟₂) with τ-⇓ 𝒟₁
... | true , ⇓t = true , ⇓t t-or⇓
... | false , ⇓f with τ-⇓ 𝒟₂
... | b , ⇓b  = b , ⇓f f-or⇓ ⇓b
τ-⇓ (𝒟₁ T== 𝒟₂) with τ-⇓ 𝒟₁ | τ-⇓ 𝒟₂
... | m , ⇓m | n , ⇓n = m M.== n , (⇓m ==⇓ ⇓n)
τ-⇓ (T- 𝒟₁) with τ-⇓ 𝒟₁
... | n , ⇓n = M.- n , -⇓ ⇓n
τ-⇓ (𝒟₁ T+ 𝒟₂) with τ-⇓ 𝒟₁ | τ-⇓ 𝒟₂
... | m , ⇓m | n , ⇓n = m M.+ n , ⇓m +⇓ ⇓n
τ-⇓ (𝒟₁ T- 𝒟₂) with τ-⇓ 𝒟₁ | τ-⇓ 𝒟₂
... | m , ⇓m | n , ⇓n = m M.- n , (⇓m -⇓ ⇓n)
τ-⇓ (𝒟₁ T* 𝒟₂) with τ-⇓ 𝒟₁ | τ-⇓ 𝒟₂
... | m , ⇓m | n , ⇓n = m M.* n , ⇓m *⇓ ⇓n
τ-⇓ (𝒟₁ Tmod 𝒟₂) with τ-⇓ 𝒟₁ | τ-⇓ 𝒟₂
... | m , ⇓m | n , ⇓n = m M.mod n , ⇓m mod⇓ ⇓n
τ-⇓ (Tcond 𝒟₁ 𝒟₂ 𝒟₃) with τ-⇓ 𝒟₁
τ-⇓ (Tcond 𝒟₁ 𝒟₂ 𝒟₃) | true  , ⇓t with τ-⇓ 𝒟₂
... | v , ⇓v = v , then⇓ ⇓t ⇓v
τ-⇓ (Tcond 𝒟₁ 𝒟₂ 𝒟₃) | false , ⇓f with τ-⇓ 𝒟₃
... | v , v⇓ = v , else⇓ ⇓f v⇓

-- Partial converse: variable evaluation predicts typing
var-⇓-τ : ℳ ⊢ var x ⇓ (τ , V) → ⌊ ℳ ⌋ ⊢ var x ∶ τ
var-⇓-τ here⇓ = TvarZero
var-⇓-τ (there⇓ x≢y ⇓) = TvarSuc x≢y (var-⇓-τ ⇓)

--- Program typing

OK-preservation : 𝒞 OK → 𝒞 —→ 𝒞′ → 𝒞′ OK
OK-preservation (TConfig (TProg e∶τ ok)) (assign e⇓v) with ⇓-functional e⇓v (τ-⇓ e∶τ .proj₂)
... | refl = TConfig ok

OK-doesn't-go-wrong : 𝒞 OK → ∃[ ℳ′ ] 𝒞 —→* (ℳ′ , ∅)
OK-doesn't-go-wrong (TConfig ok) = OK-doesn't-go-wrongₚ ok where
  OK-doesn't-go-wrongₚ : ⌊ ℳ ⌋ ⊢ 𝒫 OK → ∃[ ℳ′ ] (ℳ , 𝒫) —→* (ℳ′ , ∅)
  OK-doesn't-go-wrongₚ TProgEmpty = _ , refl (_ , ∅)
  OK-doesn't-go-wrongₚ {ℳ} {x ≔ e ⨾ 𝒫} (TProg e∶τ ok) with τ-⇓ e∶τ
  ... | v , e⇓v with OK-doesn't-go-wrongₚ {ℳ = ℳ , x ↦ (_ , v)} ok
  ... | ℳ′ , eval = ℳ′ , step (ℳ , x ≔ e ⨾ 𝒫) (assign e⇓v) eval
