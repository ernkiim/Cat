------------------------------------------------------------------------
-- Dynamically typed minicat
------------------------------------------------------------------------
module MiniCat where

open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality hiding (trans)
open import Data.Product using (_×_; proj₁; proj₂; Σ; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit

open import MetaCat hiding (-_; _+_; _-_; _*_; not; _==_; _mod_; if_then_else_; ap)
open import MetaCat as M using (Bool; ℕ; ℤ; Variable)

variable
  b b₁ b₂ : Bool
  m n : ℤ
  x y z : Variable

-- Values have types
data Type : Set where
  int  : Type
  bool : Type
variable τ τ₁ τ₂ : Type

⟦_⟧τ : Type → Set
⟦ int  ⟧τ = ℤ
⟦ bool ⟧τ = Bool
variable V W : ⟦ τ ⟧τ

Value = ∃[ τ ] ⟦ τ ⟧τ

variable v w v₁ v₂ v₃ : Value


-- Expressions
data Expression : Set where

  var : Variable → Expression
  val : Value    → Expression

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
variable ℳ ℳ₁ ℳ₂ : Memory

-- Evaluation
data _⊢_⇓_ : Memory → Expression → Value → Set where

  val⇓ : ℳ ⊢ val v ⇓ v

  here⇓ : (ℳ , x ↦ v) ⊢ var x ⇓ v
  there⇓ : (ℳ ⊢ var x ⇓ v) → (x ≢ y) → (ℳ , y ↦ w) ⊢ var x ⇓ v

  not⇓_ : ℳ ⊢ e ⇓ ⟨ bool , b ⟩ → ℳ ⊢ not e ⇓ ⟨ bool , M.not b ⟩
  f-and⇓ : ℳ ⊢ e₁ ⇓ ⟨ _ , false ⟩ → ℳ ⊢ e₁ and e₂ ⇓ ⟨ _ , false ⟩
  t-or⇓  : ℳ ⊢ e₁ ⇓ ⟨ _ , true  ⟩ → ℳ ⊢ e₁ or  e₂ ⇓ ⟨ _ , true ⟩
  t-and⇓ : ℳ ⊢ e₁ ⇓ ⟨ _ , true  ⟩ → ℳ ⊢ e₂ ⇓ ⟨ _ , b ⟩ → ℳ ⊢ e₁ and e₂ ⇓ ⟨ _ , b ⟩
  f-or⇓  : ℳ ⊢ e₁ ⇓ ⟨ _ , false ⟩ → ℳ ⊢ e₂ ⇓ ⟨ _ , b ⟩ → ℳ ⊢ e₁ or  e₂ ⇓ ⟨ _ , b ⟩
  _==⇓_ : ℳ ⊢ e₁ ⇓ ⟨ int , m ⟩ → ℳ ⊢ e₂ ⇓ ⟨ int , n ⟩ → ℳ ⊢ e₁ == e₂ ⇓ ⟨ bool , m M.== n ⟩
  
  -⇓ : ℳ ⊢ e ⇓ ⟨ int , n ⟩ → ℳ ⊢ - e ⇓ ⟨ int , M.- n ⟩
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
  ϵ : Program
  _≔_⨾_ : Variable → Expression → Program → Program
variable 𝒫 𝒫₁ 𝒫₂ : Program
  
Configuration = Memory × Program
variable 𝒞 𝒞′ 𝒞″ : Configuration

-- Reduction semantics
data _—→_ : Configuration → Configuration → Set where
  step : ℳ ⊢ e ⇓ v  → ⟨ ℳ , x ≔ e ⨾ 𝒫 ⟩ —→ ⟨ (ℳ , x ↦ v) , 𝒫 ⟩

data _—→*_ : Configuration → Configuration → Set where
  refl  : 𝒞 —→* 𝒞
  trans : 𝒞 —→ 𝒞′ → 𝒞′ —→* 𝒞″ → 𝒞 —→* 𝒞″ 

--- Precedence declarations
infix 5 _⊢_⇓_
infix 6 _,_↦_

infixl 10 _≔_⨾_

infixl 20 if_then_else_

infixl 30 _or_
infixl 31 _and_
infixl 32 _==_
infix  33 not_

infixl 40 _+_ _-_ _+⇓_ _-⇓_
infixl 41 _*_ _mod_
infix  42 -_
infix  43 val var
