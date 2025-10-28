{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Dynamically typed minicat
------------------------------------------------------------------------

module Cat.MiniCat.Base where

open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality hiding (trans)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Product using (_×_; proj₁; proj₂; Σ; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit

open import Function

open import Cat.Meta hiding (-_; _+_; _-_; _*_; not; _==_; _mod_; if_then_else_; ap)
open import Cat.Meta as M using (Bool; ℕ; ℤ; Variable)

variable
  b b₁ b₂ : Bool
  m n : ℤ
  x y z : Variable

-- Values have types
data Type : Set where
  int  : Type
  bool : Type
variable τ τ′ τ₁ τ₂ : Type

⟦_⟧τ : Type → Set
⟦ int  ⟧τ = ℤ
⟦ bool ⟧τ = Bool
variable V W : ⟦ τ ⟧τ

_≟τ_ : DecidableEquality Type
int ≟τ int = yes refl
int ≟τ bool = no λ ()
bool ≟τ int = no λ () 
bool ≟τ bool = yes refl

Value = ∃[ τ ] ⟦ τ ⟧τ

variable v w v₁ v₂ v₃ : Value


-- Expressions
data Expression : Set where

  val : Value    → Expression
  var : Variable → Expression

  not_            : Expression → Expression
  _and_ _or_ _==_ : Expression → Expression → Expression

  -_                : Expression → Expression
  _+_ _-_ _*_ _mod_ : Expression → Expression → Expression
  
  if_then_else_ : Expression → Expression → Expression → Expression

variable e e₁ e₂ e₃ : Expression

pattern t = val ⟨ bool , true ⟩
pattern f = val ⟨ bool , false ⟩
pattern +0 = val ⟨ int , + 0 ⟩
pattern +1 = val ⟨ int , + 1 ⟩
pattern —1 = val ⟨ int , -[1+ 0 ] ⟩

-- Memories take variables to values
data Memory : Set where
  ∅     : Memory
  _,_↦_ : Memory → Variable → Value → Memory
variable ℳ ℳ′ ℳ₁ ℳ₂ ℳ₁′ ℳ₂′ : Memory

-- Evaluation
data _⊢_⇓_ : Memory → Expression → Value → Set where

  val⇓ : ℳ ⊢ val v ⇓ v

  here⇓ : (ℳ , x ↦ v) ⊢ var x ⇓ v
  there⇓ : (x ≢ y) → (ℳ ⊢ var x ⇓ v) → (ℳ , y ↦ w) ⊢ var x ⇓ v

  not⇓_ : ℳ ⊢ e ⇓ ⟨ bool , b ⟩ → ℳ ⊢ not e ⇓ ⟨ bool , M.not b ⟩
  _f-and⇓ : ℳ ⊢ e₁ ⇓ ⟨ _ , false ⟩ → ℳ ⊢ e₁ and e₂ ⇓ ⟨ _ , false ⟩
  _t-or⇓  : ℳ ⊢ e₁ ⇓ ⟨ _ , true  ⟩ → ℳ ⊢ e₁ or  e₂ ⇓ ⟨ _ , true ⟩
  _t-and⇓_ : ℳ ⊢ e₁ ⇓ ⟨ _ , true  ⟩ → ℳ ⊢ e₂ ⇓ ⟨ _ , b ⟩ → ℳ ⊢ e₁ and e₂ ⇓ ⟨ _ , b ⟩
  _f-or⇓_  : ℳ ⊢ e₁ ⇓ ⟨ _ , false ⟩ → ℳ ⊢ e₂ ⇓ ⟨ _ , b ⟩ → ℳ ⊢ e₁ or  e₂ ⇓ ⟨ _ , b ⟩
  _==⇓_ : ℳ ⊢ e₁ ⇓ ⟨ int , m ⟩ → ℳ ⊢ e₂ ⇓ ⟨ int , n ⟩ → ℳ ⊢ e₁ == e₂ ⇓ ⟨ bool , m M.== n ⟩
  
  -⇓_ : ℳ ⊢ e ⇓ ⟨ int , n ⟩ → ℳ ⊢ - e ⇓ ⟨ int , M.- n ⟩
  _+⇓_ : ℳ ⊢ e₁ ⇓ ⟨ int , m ⟩ → ℳ ⊢ e₂ ⇓ ⟨ int , n ⟩ → ℳ ⊢ e₁ + e₂ ⇓ ⟨ int , m M.+ n ⟩
  _-⇓_ : ℳ ⊢ e₁ ⇓ ⟨ int , m ⟩ → ℳ ⊢ e₂ ⇓ ⟨ int , n ⟩ → ℳ ⊢ e₁ - e₂ ⇓ ⟨ int , m M.- n ⟩
  _*⇓_ : ℳ ⊢ e₁ ⇓ ⟨ int , m ⟩ → ℳ ⊢ e₂ ⇓ ⟨ int , n ⟩ → ℳ ⊢ e₁ * e₂ ⇓ ⟨ int , m M.* n ⟩
  _mod⇓_ : ℳ ⊢ e₁ ⇓ ⟨ int , m ⟩ → ℳ ⊢ e₂ ⇓ ⟨ int , n ⟩ → ℳ ⊢ e₁ mod e₂ ⇓ ⟨ int , m M.mod n ⟩
  

  then⇓ :

    ℳ ⊢ e₁ ⇓ ⟨ _ , true ⟩ → ℳ ⊢ e₂ ⇓ v →
    -------------------------------------
      ℳ ⊢ if e₁ then e₂ else e₃ ⇓ v

  else⇓ :

    ℳ ⊢ e₁ ⇓ ⟨ _ , false ⟩ → ℳ ⊢ e₃ ⇓ v →
    -------------------------------------
      ℳ ⊢ if e₁ then e₂ else e₃ ⇓ v

-- Programs are lists of assignments
data Program : Set where
  ∅ : Program
  _≔_⨾_ : Variable → Expression → Program → Program
variable 𝒫 𝒫′ 𝒫₁ 𝒫₁′ 𝒫₂ 𝒫₂′ : Program
  
Configuration = Memory × Program
variable 𝒞 𝒞′ 𝒞″ 𝒞₁ 𝒞₁′ 𝒞₂ 𝒞₂′ : Configuration

-- Reduction semantics
data _—→_ : Configuration → Configuration → Set where
  assign : ℳ ⊢ e ⇓ v  → ⟨ ℳ , x ≔ e ⨾ 𝒫 ⟩ —→ ⟨ (ℳ , x ↦ v) , 𝒫 ⟩

data _—→*_ : Configuration → Configuration → Set where
  refl : ∀ 𝒞 → 𝒞 —→* 𝒞
  step : ∀ 𝒞 → 𝒞 —→ 𝒞′ → 𝒞′ —→* 𝒞″ → 𝒞 —→* 𝒞″ 
variable θ θ′ θ₁ θ₁′ θ₂ θ₂′ : 𝒞 —→* 𝒞′

Reducible : Configuration → Set
Reducible 𝒞 = ∃[ 𝒞′ ] 𝒞 —→ 𝒞′

Normal : Configuration → Set
Normal = ¬_ ∘ Reducible

Trace : Configuration → Set
Trace 𝒞 = ∃[ 𝒞′ ] 𝒞 —→* 𝒞′ × Normal 𝒞′

record _=dom_ (ℳ₁ ℳ₂ : Memory) : Set where
  constructor _&_
  field
    ⊆dom : ℳ₁ ⊢ var x ⇓ v₁ → ∃[ v₂ ] ℳ₂ ⊢ var x ⇓ v₂
    ⊇dom : ℳ₂ ⊢ var x ⇓ v₂ → ∃[ v₁ ] ℳ₁ ⊢ var x ⇓ v₁

--- Precedence declarations
infix 5 _⊢_⇓_
infix 6 _,_↦_

infixl 10 _≔_⨾_

infixl 20 if_then_else_

infixl 30 _or_
infixl 31 _and_
infixl 32 _==_ _==⇓_
infix  33 not_ not⇓_

infixl 40 _+_ _-_ _+⇓_ _-⇓_
infixl 41 _*_ _mod_ _*⇓_ _mod⇓_
infix  42 -_ -⇓_
infix  43 val var val⇓ here⇓ there⇓
