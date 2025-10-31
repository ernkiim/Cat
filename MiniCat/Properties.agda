{-# OPTIONS --safe #-}

module Cat.MiniCat.Properties where

open import Relation.Nullary.Negation using (¬_; contradiction; contraposition)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; _≢_)
open import Data.Product using (_×_; proj₁; proj₂; Σ; _,_; ∃-syntax)
open import Function

open import Cat.Meta as M using (_≟S_; true; false)

open import Cat.MiniCat.Base

--- Expression properties

⇓-functional : ℳ ⊢ e ⇓ v₁ → ℳ ⊢ e ⇓ v₂ → v₁ ≡ v₂
⇓-functional val⇓ val⇓ = refl
⇓-functional here⇓ here⇓                 = refl
⇓-functional here⇓ (there⇓ x≢x _)        = contradiction refl x≢x
⇓-functional (there⇓ x≢x _) here⇓        = contradiction refl x≢x
⇓-functional (there⇓ _ 𝒟₁) (there⇓ _ 𝒟₂) = ⇓-functional 𝒟₁ 𝒟₂
⇓-functional (not⇓ 𝒟₁) (not⇓ 𝒟₂) with ⇓-functional 𝒟₁ 𝒟₂
... | refl = refl
⇓-functional (_ f-and⇓)    (_ f-and⇓)    = refl
⇓-functional (⇓f f-and⇓)   (⇓t t-and⇓ _) = contradiction (⇓-functional ⇓t ⇓f) λ ()
⇓-functional (⇓t t-and⇓ _) (⇓f f-and⇓)   = contradiction (⇓-functional ⇓t ⇓f) λ ()
⇓-functional (_ t-and⇓ 𝒟₁) (_ t-and⇓ 𝒟₂) = ⇓-functional 𝒟₁ 𝒟₂
⇓-functional (_ t-or⇓)    (_ t-or⇓)    = refl
⇓-functional (⇓t t-or⇓)   (⇓f f-or⇓ _) = contradiction (⇓-functional ⇓t ⇓f) λ ()
⇓-functional (⇓f f-or⇓ _) (⇓t t-or⇓)   = contradiction (⇓-functional ⇓t ⇓f) λ ()
⇓-functional (_ f-or⇓ 𝒟₁) (_ f-or⇓ 𝒟₂) = ⇓-functional 𝒟₁ 𝒟₂
⇓-functional (𝒟₁ ==⇓ 𝒟₂) (𝒟₃ ==⇓ 𝒟₄) with ⇓-functional 𝒟₁ 𝒟₃ | ⇓-functional 𝒟₂ 𝒟₄
... | refl | refl = refl
⇓-functional (-⇓ 𝒟₁) (-⇓ 𝒟₂) with ⇓-functional 𝒟₁ 𝒟₂
... | refl = refl
⇓-functional (𝒟₁ +⇓ 𝒟₂) (𝒟₃ +⇓ 𝒟₄) with ⇓-functional 𝒟₁ 𝒟₃ | ⇓-functional 𝒟₂ 𝒟₄
... | refl | refl = refl
⇓-functional (𝒟₁ -⇓ 𝒟₂) (𝒟₃ -⇓ 𝒟₄) with ⇓-functional 𝒟₁ 𝒟₃ | ⇓-functional 𝒟₂ 𝒟₄
... | refl | refl = refl
⇓-functional (𝒟₁ *⇓ 𝒟₂) (𝒟₃ *⇓ 𝒟₄) with ⇓-functional 𝒟₁ 𝒟₃ | ⇓-functional 𝒟₂ 𝒟₄
... | refl | refl = refl
⇓-functional (𝒟₁ mod⇓ 𝒟₂) (𝒟₃ mod⇓ 𝒟₄) with ⇓-functional 𝒟₁ 𝒟₃ | ⇓-functional 𝒟₂ 𝒟₄
... | refl | refl = refl
⇓-functional (then⇓ 𝒟₁ 𝒟₂) (then⇓ 𝒟₃ 𝒟₄) with ⇓-functional 𝒟₁ 𝒟₃ | ⇓-functional 𝒟₂ 𝒟₄
... | refl | refl = refl
⇓-functional (then⇓ 𝒟₁ _ ) (else⇓ 𝒟₂ _ ) with ⇓-functional 𝒟₁ 𝒟₂
... | ()
⇓-functional (else⇓ 𝒟₁ _ ) (then⇓ 𝒟₂ _ ) with ⇓-functional 𝒟₁ 𝒟₂
... | ()
⇓-functional (else⇓ 𝒟₁ 𝒟₂) (else⇓ 𝒟₃ 𝒟₄) with ⇓-functional 𝒟₁ 𝒟₃ | ⇓-functional 𝒟₂ 𝒟₄
... | refl | refl = refl

⇓-decidable : ∀ ℳ e → Dec (∃[ v ] ℳ ⊢ e ⇓ v)
⇓-decidable ∅ (var _) = no λ ()
⇓-decidable (ℳ , y ↦ _) (var x) with x ≟S y
... | yes refl = yes (_ , here⇓)
... | no  x≢y with ⇓-decidable ℳ (var x)
...   | yes (v , 𝒟) = yes (v , there⇓ x≢y 𝒟)
...   | no  ¬⇓      = no λ { (_ , here⇓)      → x≢y refl
                           ; (v , there⇓ _ 𝒟) → ¬⇓ (v , 𝒟) }
⇓-decidable ℳ (val _) = yes (_ , val⇓)
⇓-decidable ℳ (not e) with ⇓-decidable ℳ e 
... | yes ((bool , _) , 𝒟)  = yes (_ , not⇓ 𝒟)
... | yes ((int  , _) , 𝒟) = no λ { (_ , (not⇓ 𝒟′)) → contradiction (⇓-functional 𝒟 𝒟′) λ () }
... | no  ¬⇓               = no λ { (_ , (not⇓ 𝒟′)) → ¬⇓ (_ , 𝒟′) }
⇓-decidable ℳ (e₁ and e₂) with ⇓-decidable ℳ e₁
... | no ¬e₁⇓ = no λ { (_ , 𝒟₁′ f-and⇓)   → ¬e₁⇓ (_ , 𝒟₁′)
                     ; (_ , 𝒟₁′ t-and⇓ _) → ¬e₁⇓ (_ , 𝒟₁′) }
... | yes ((int , _) , 𝒟₁) = no λ { (_ , 𝒟₁′ f-and⇓)   → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ ()
                                  ; (_ , 𝒟₁′ t-and⇓ _) → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ () }
... | yes ((bool , false) , 𝒟) = yes (_ , 𝒟 f-and⇓)
... | yes ((bool , true ) , 𝒟₁) with ⇓-decidable ℳ e₂
...   | yes ((bool , _) , 𝒟₂) = yes (_ , 𝒟₁ t-and⇓ 𝒟₂)
...   | yes ((int  , _) , 𝒟₂) = no λ { (_ , 𝒟₁′ f-and⇓)   → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ ()
                                     ; (_ , _ t-and⇓ 𝒟₂′) → contradiction (⇓-functional 𝒟₂ 𝒟₂′) λ () }
...   | no ¬e₂⇓ = no λ { (_ , 𝒟₁′ f-and⇓)   → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ ()
                       ; (_ , _ t-and⇓ 𝒟₂′) → ¬e₂⇓ (_ , 𝒟₂′) }
⇓-decidable ℳ (e₁ or e₂) with ⇓-decidable ℳ e₁
... | no ¬e₁⇓ = no λ { (_ , 𝒟₁′ t-or⇓)   → ¬e₁⇓ (_ , 𝒟₁′)
                     ; (_ , 𝒟₁′ f-or⇓ _) → ¬e₁⇓ (_ , 𝒟₁′) }
... | yes ((int , _) , 𝒟₁) = no λ { (x , 𝒟₁′ t-or⇓)   → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ ()
                                  ; (x , 𝒟₁′ f-or⇓ _) → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ () }
... | yes ((bool , true) , 𝒟) = yes (_ , 𝒟 t-or⇓)
... | yes ((bool , false) , 𝒟₁) with ⇓-decidable ℳ e₂
...   | yes ((bool , _) , 𝒟₂) = yes (_ , 𝒟₁ f-or⇓ 𝒟₂)
...   | yes ((int  , _) , 𝒟₂) = no λ { (x , 𝒟₁′ t-or⇓)   → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ ()
                                     ; (x , _ f-or⇓ 𝒟₂′) → contradiction (⇓-functional 𝒟₂ 𝒟₂′) λ () }
...   | no ¬e₂⇓ = no λ { (x , 𝒟₁′ t-or⇓) → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ ()
                       ; (x , _ f-or⇓ 𝒟₂′) → ¬e₂⇓ (_ , 𝒟₂′) }
⇓-decidable ℳ (e == e₁) with ⇓-decidable ℳ e | ⇓-decidable ℳ e₁ 
... | yes ((int  , m) , 𝒟₁) | yes ((int , n) , 𝒟₂) = yes (_ , (𝒟₁ ==⇓ 𝒟₂))
... | yes ((bool , b) , 𝒟) | _ = no λ { (_ , (𝒟′ ==⇓ _)) → contradiction (⇓-functional 𝒟 𝒟′ ) λ () }
... | _ | yes ((bool , _) , 𝒟) = no λ { (_ , (_ ==⇓ 𝒟′)) → contradiction (⇓-functional 𝒟 𝒟′ ) λ () }
... | _ | no ¬e₂⇓ = no λ { (_ , (_ ==⇓ e₂⇓)) → ¬e₂⇓ (_ , e₂⇓) }
... | no ¬e₁⇓ | _ = no λ { (_ , (e₁⇓ ==⇓ _)) → ¬e₁⇓ (_ , e₁⇓) }
⇓-decidable ℳ (- e) with ⇓-decidable ℳ e 
... | yes ((int , b) , 𝒟)  = yes ((int , M.- b) , -⇓ 𝒟)
... | yes ((bool  , _) , 𝒟₁) = no λ { (_ , (-⇓ 𝒟₂)) → contradiction (⇓-functional 𝒟₁ 𝒟₂)  λ () }
... | no  ¬⇓                 = no λ { (_ , (-⇓ 𝒟₂)) → ¬⇓ (_ , 𝒟₂) }
⇓-decidable ℳ (e₁  +  e₂) with ⇓-decidable ℳ e₁ | ⇓-decidable ℳ e₂
... | yes ((int , _) , 𝒟₁) | yes ((int , _) , 𝒟₂) = yes (_ , (𝒟₁ +⇓ 𝒟₂))
... | yes ((bool , _) , 𝒟₁) | _ = no λ { (_ , (𝒟₁′ +⇓ _)) → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ () }
... | _ | yes ((bool , _) , 𝒟₂) = no λ { (_ , (_ +⇓ 𝒟₂′)) → contradiction (⇓-functional 𝒟₂ 𝒟₂′) λ () }
... | _ | no ¬e₂⇓ = no λ { (_ , (_ +⇓ 𝒟₂′)) → ¬e₂⇓ (_ , 𝒟₂′) }
... | no ¬e₁⇓ | _ = no λ { (_ , (𝒟₁′ +⇓ _)) → ¬e₁⇓ (_ , 𝒟₁′) }
⇓-decidable ℳ (e₁  -  e₂) with ⇓-decidable ℳ e₁ | ⇓-decidable ℳ e₂
... | yes ((int , _) , 𝒟₁) | yes ((int , _) , 𝒟₂) = yes (_ , 𝒟₁ -⇓ 𝒟₂)
... | yes ((bool , _) , 𝒟₁) | _ = no λ { (_ , (𝒟₁′ -⇓ _)) → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ () }
... | _ | yes ((bool , _) , 𝒟₂) = no λ { (_ , (_ -⇓ 𝒟₂′)) → contradiction (⇓-functional 𝒟₂ 𝒟₂′) λ () }
... | _ | no ¬e₂⇓ = no λ { (_ , (_ -⇓ 𝒟₂′)) → ¬e₂⇓ (_ , 𝒟₂′) }
... | no ¬e₁⇓ | _ = no λ { (_ , (𝒟₁′ -⇓ _)) → ¬e₁⇓ (_ , 𝒟₁′) }
⇓-decidable ℳ (e₁  *  e₂) with ⇓-decidable ℳ e₁ | ⇓-decidable ℳ e₂
... | yes ((int , _) , 𝒟₁) | yes ((int , _) , 𝒟₂) = yes (_ , (𝒟₁ *⇓ 𝒟₂))
... | yes ((bool , _) , 𝒟₁) | _ = no λ { (_ , (𝒟₁′ *⇓ _)) → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ () }
... | _ | yes ((bool , _) , 𝒟₂) = no λ { (_ , (_ *⇓ 𝒟₂′)) → contradiction (⇓-functional 𝒟₂ 𝒟₂′) λ () }
... | _ | no ¬e₂⇓ = no λ { (_ , (_ *⇓ 𝒟₂′)) → ¬e₂⇓ (_ , 𝒟₂′) }
... | no ¬e₁⇓ | _ = no λ { (_ , (𝒟₁′ *⇓ _)) → ¬e₁⇓ (_ , 𝒟₁′) }
⇓-decidable ℳ (e₁ mod e₂) with ⇓-decidable ℳ e₁ | ⇓-decidable ℳ e₂
... | yes ((int , _) , 𝒟₁) | yes ((int , _) , 𝒟₂) = yes (_ , (𝒟₁ mod⇓ 𝒟₂))
... | yes ((bool , _) , 𝒟₁) | _ = no λ { (_ , (𝒟₁′ mod⇓ _)) → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ () }
... | _ | yes ((bool , _) , 𝒟₂) = no λ { (_ , (_ mod⇓ 𝒟₂′)) → contradiction (⇓-functional 𝒟₂ 𝒟₂′) λ () }
... | _ | no ¬e₂⇓ = no λ { (_ , (_ mod⇓ 𝒟₂′)) → ¬e₂⇓ (_ , 𝒟₂′) }
... | no ¬e₁⇓ | _ = no λ { (_ , (𝒟₁′ mod⇓ _)) → ¬e₁⇓ (_ , 𝒟₁′) }
⇓-decidable ℳ (if e₁ then e₂ else e₃) with ⇓-decidable ℳ e₁
... | yes ((int , _) , 𝒟₁) = no λ { (_ , then⇓ 𝒟₁′ _) → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ ()
                                  ; (_ , else⇓ 𝒟₁′ _) → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ () }
... | no ¬e₁⇓ = no λ { (_ , then⇓ 𝒟₁ _) → ¬e₁⇓ (_ , 𝒟₁)
                     ; (_ , else⇓ 𝒟₁ _) → ¬e₁⇓ (_ , 𝒟₁) }
⇓-decidable ℳ (if e₁ then e₂ else e₃) | yes ((bool , true)  , 𝒟₁) with ⇓-decidable ℳ e₂
... | yes (_ , 𝒟₂) = yes (_ , then⇓ 𝒟₁ 𝒟₂)
... | no  ¬e₂⇓     = no λ { (_ , then⇓ _ 𝒟₂′) → ¬e₂⇓ (_ , 𝒟₂′)
                          ; (_ , else⇓ 𝒟₁′ _) → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ () }
⇓-decidable ℳ (if e₁ then e₂ else e₃) | yes ((bool , false) , 𝒟₁) with ⇓-decidable ℳ e₃
... | yes (_ , 𝒟₃) = yes (_ , else⇓ 𝒟₁ 𝒟₃)
... | no  ¬e₃⇓     = no λ { (_ , then⇓ 𝒟₁′ _) → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ ()
                          ; (_ , else⇓ _ 𝒟₃′) → ¬e₃⇓ (_ , 𝒟₃′) }

--- Program and configuration properties

∅-normal : Normal (ℳ , ∅)
∅-normal ()

reducible-decidable : ∀ 𝒞 → Dec (Reducible 𝒞)
reducible-decidable (ℳ , ∅) = no λ ()
reducible-decidable (ℳ , x ≔ e ⨾ 𝒫) with ⇓-decidable ℳ e
... | yes (v , 𝒟) = yes ((ℳ , x ↦ v , 𝒫) , assign 𝒟)
... | no ¬∃⇓ = no λ { (_ , assign ⇓) → ¬∃⇓ (_ , ⇓) }

normalize : ∀ 𝒞 → ∃[ 𝒞′ ] 𝒞 —→* 𝒞′ —̸→
normalize (ℳ , 𝒫) = rec ℳ 𝒫 where
  rec : ∀ ℳ 𝒫 → ∃[ 𝒞′ ]  (ℳ , 𝒫) —→* 𝒞′ —̸→
  rec ℳ ∅ = (ℳ , ∅) , [ (λ ()) ]
  rec ℳ 𝒫@(x ≔ e ⨾ 𝒫′) with ⇓-decidable ℳ e
  ... | no ¬∃e⇓v = (ℳ , 𝒫) , [ (λ { (𝒞′ , assign e⇓v) → ¬∃e⇓v (_ , e⇓v) }) ]
  ... | yes (v , ℳ⊢e⇓v) with rec (ℳ , x ↦ v) 𝒫′
  ... | 𝒞′ , —→* = 𝒞′ , (assign ℳ⊢e⇓v) ∷ —→*

-- trace-unique : ∀ (θ₁ θ₂ : FullTrace 𝒞) → θ₁ ≡ θ₂

=dom-ext : ℳ₁ =dom ℳ₂ → (ℳ₁ , x ↦ v₁) =dom (ℳ₂ , x ↦ v₂)
=dom-ext (⊆dom & ⊇dom) =
  (λ { here⇓ → _ , here⇓ ; (there⇓ x≢y rest) → ⊆dom rest .proj₁ , there⇓ x≢y (⊆dom rest .proj₂) } ) &
   λ { here⇓ → _ , here⇓ ; (there⇓ x≢y rest) → ⊇dom rest .proj₁ , there⇓ x≢y (⊇dom rest .proj₂) }

=dom-preservation : (ℳ₁ , 𝒫) —→ (ℳ₁′ , 𝒫′) → (ℳ₂ , 𝒫) —→ (ℳ₂′ , 𝒫′) →
  ℳ₁  =dom ℳ₂ → ℳ₁′ =dom ℳ₂′
=dom-preservation (assign e⇓v₁) (assign e⇓v₂) =dom = =dom-ext =dom
