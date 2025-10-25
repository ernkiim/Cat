module Properties where

open import Axiom.UniquenessOfIdentityProofs

open import Relation.Nullary.Negation using (¬_; contradiction; contraposition)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Data.Product using (_×_; proj₁; proj₂; Σ; _,_; ∃-syntax)

open import MetaCat as M using (_≟S_; true; false)

open import MiniCat


-- Expression properties

-- Evaluation is functional
⇓-functional : ℳ ⊢ e ⇓ v₁ → ℳ ⊢ e ⇓ v₂ → v₁ ≡ v₂
⇓-functional val⇓ val⇓ = refl
⇓-functional here⇓ here⇓                 = refl
⇓-functional here⇓ (there⇓ _ x≢x)        = contradiction refl x≢x
⇓-functional (there⇓ _ x≢x) here⇓        = contradiction refl x≢x
⇓-functional (there⇓ 𝒟₁ _) (there⇓ 𝒟₂ _) = ⇓-functional 𝒟₁ 𝒟₂
⇓-functional (not⇓ 𝒟₁) (not⇓ 𝒟₂) with ⇓-functional 𝒟₁ 𝒟₂
... | refl = refl
⇓-functional (f-and⇓ _)    (f-and⇓ _)    = refl
⇓-functional (f-and⇓ ⇓f)   (t-and⇓ ⇓t _) = contradiction (⇓-functional ⇓t ⇓f) λ ()
⇓-functional (t-and⇓ ⇓t _) (f-and⇓ ⇓f)   = contradiction (⇓-functional ⇓t ⇓f) λ ()
⇓-functional (t-and⇓ _ 𝒟₁) (t-and⇓ _ 𝒟₂) = ⇓-functional 𝒟₁ 𝒟₂
⇓-functional (t-or⇓ _)    (t-or⇓ _)    = refl
⇓-functional (t-or⇓ ⇓t)   (f-or⇓ ⇓f _) = contradiction (⇓-functional ⇓t ⇓f) λ ()
⇓-functional (f-or⇓ ⇓f _) (t-or⇓ ⇓t)   = contradiction (⇓-functional ⇓t ⇓f) λ ()
⇓-functional (f-or⇓ _ 𝒟₁) (f-or⇓ _ 𝒟₂) = ⇓-functional 𝒟₁ 𝒟₂
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

-- Evaluation is decidable
⇓-decidable : ∀ ℳ e → Dec (∃[ v ] ℳ ⊢ e ⇓ v)
⇓-decidable ∅ (var _) = no λ ()
⇓-decidable (ℳ , y ↦ _) (var x) with x ≟S y
... | yes refl = yes (_ , here⇓)
... | no  x≢y with ⇓-decidable ℳ (var x)
...   | yes (v , 𝒟) = yes (v , there⇓ 𝒟 x≢y)
...   | no  ¬⇓      = no λ { (_ , here⇓)      → x≢y refl
                           ; (v , there⇓ 𝒟 _) → ¬⇓ (v , 𝒟) }
⇓-decidable ℳ (val _) = yes (_ , val⇓)
⇓-decidable ℳ (not e) with ⇓-decidable ℳ e 
... | yes ((bool , _) , 𝒟)  = yes (_ , not⇓ 𝒟)
... | yes ((int  , _) , 𝒟) = no λ { (_ , (not⇓ 𝒟′)) → contradiction (⇓-functional 𝒟 𝒟′) λ () }
... | no  ¬⇓               = no λ { (_ , (not⇓ 𝒟′)) → ¬⇓ (_ , 𝒟′) }
⇓-decidable ℳ (e₁ and e₂) with ⇓-decidable ℳ e₁
... | no ¬e₁⇓ = no λ { (_ , f-and⇓ 𝒟₁′)   → ¬e₁⇓ (_ , 𝒟₁′)
                     ; (_ , t-and⇓ 𝒟₁′ _) → ¬e₁⇓ (_ , 𝒟₁′) }
... | yes ((int , _) , 𝒟₁) = no λ { (_ , f-and⇓ 𝒟₁′)   → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ ()
                                  ; (_ , t-and⇓ 𝒟₁′ _) → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ () }
... | yes ((bool , false) , 𝒟) = yes (_ , f-and⇓ 𝒟)
... | yes ((bool , true ) , 𝒟₁) with ⇓-decidable ℳ e₂
...   | yes ((bool , _) , 𝒟₂) = yes (_ , t-and⇓ 𝒟₁ 𝒟₂)
...   | yes ((int  , _) , 𝒟₂) = no λ { (_ , f-and⇓ 𝒟₁′)   → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ ()
                                     ; (_ , t-and⇓ _ 𝒟₂′) → contradiction (⇓-functional 𝒟₂ 𝒟₂′) λ () }
...   | no ¬e₂⇓ = no λ { (_ , f-and⇓ 𝒟₁′)   → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ ()
                       ; (_ , t-and⇓ _ 𝒟₂′) → ¬e₂⇓ (_ , 𝒟₂′) }
⇓-decidable ℳ (e₁ or e₂) with ⇓-decidable ℳ e₁
... | no ¬e₁⇓ = no λ { (_ , t-or⇓ 𝒟₁′)   → ¬e₁⇓ (_ , 𝒟₁′)
                     ; (_ , f-or⇓ 𝒟₁′ _) → ¬e₁⇓ (_ , 𝒟₁′) }
... | yes ((int , _) , 𝒟₁) = no λ { (x , t-or⇓ 𝒟₁′)   → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ ()
                                  ; (x , f-or⇓ 𝒟₁′ _) → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ () }
... | yes ((bool , true) , 𝒟) = yes (_ , t-or⇓ 𝒟)
... | yes ((bool , false) , 𝒟₁) with ⇓-decidable ℳ e₂
...   | yes ((bool , _) , 𝒟₂) = yes (_ , f-or⇓ 𝒟₁ 𝒟₂)
...   | yes ((int  , _) , 𝒟₂) = no λ { (x , t-or⇓ 𝒟₁′)   → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ ()
                                     ; (x , f-or⇓ _ 𝒟₂′) → contradiction (⇓-functional 𝒟₂ 𝒟₂′) λ () }
...   | no ¬e₂⇓ = no λ { (x , t-or⇓ 𝒟₁′) → contradiction (⇓-functional 𝒟₁ 𝒟₁′) λ ()
                       ; (x , f-or⇓ _ 𝒟₂′) → ¬e₂⇓ (_ , 𝒟₂′) }
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
... | yes ((int , _) , 𝒟₁) | yes ((int , _) , 𝒟₂) = yes (_ , _-⇓_ 𝒟₁ 𝒟₂) -- ambiguous parse ???
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


Normal : Configuration → Set
Normal 𝒞 = ∀ {𝒞′} → ¬ (𝒞 —→ 𝒞′)

data Done : Configuration → Set where
  done : Done (ℳ , ϵ)

Stuck : Configuration → Set
Stuck 𝒞 = Normal 𝒞 × ¬ (Done 𝒞)

--- Examples and constants

expression1 : Expression
expression1 = if var "x" then t else +1

_ = ⇓-decidable ∅ expression1
