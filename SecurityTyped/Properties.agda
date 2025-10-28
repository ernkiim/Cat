{-# OPTIONS --safe #-}

module Cat.SecurityTyped.Properties where

open import Relation.Binary.PropositionalEquality

open import Cat.MiniCat
open import Cat.Typed
open import Cat.Typed.Properties
open import Cat.SecurityLevels
open import Cat.SecurityTyped.Base

-- dumb lemma


=[ς]-sym : ℳ₁ =[ ς ] ℳ₂ → ℳ₂ =[ ς ] ℳ₁
=[ς]-sym (⟨ ⊆dom , ⊇dom ⟩ , ⊆ς , ⊇ς) = ⟨ ⊇dom , ⊆dom ⟩ , ⊇ς , ⊆ς

=[L]-τ-wf : ℳ₁ =[ L ] ℳ₂ → σ e ≡ L → ⌊ ℳ₁ ⌋ ⊢ e ∶ τ → ⌊ ℳ₂ ⌋ ⊢ e ∶ τ
=[L]-τ-wf {e = var x} (=dom , ⊆ς , ⊇ς) σe≡L (Tvar ∋) = {!!}
=[L]-τ-wf =[L] σe≡L Tval = Tval
=[L]-τ-wf =[L] σe≡L (Tnot a) = {!!}
=[L]-τ-wf =[L] σe≡L (a Tand a₁) = {!!}
=[L]-τ-wf =[L] σe≡L (a Tor a₁) = {!!}
=[L]-τ-wf =[L] σe≡L (a T== a₁) = {!!}
=[L]-τ-wf =[L] σe≡L (T- a) = {!!}
=[L]-τ-wf =[L] σe≡L (a T+ a₁) = {!!}
=[L]-τ-wf =[L] σe≡L (a T- a₁) = {!!}
=[L]-τ-wf =[L] σe≡L (a T* a₁) = {!!}
=[L]-τ-wf =[L] σe≡L (a Tmod a₁) = {!!}
=[L]-τ-wf =[L] σe≡L (Tcond a a₁ a₂) = {!!}
