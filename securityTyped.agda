------------------------------------------------------------------------
-- Security Typed Minicat
------------------------------------------------------------------------

module SecurityTyped where

open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
import MetaCat as M
open M using (Variable; true; false) 

open import Levels renaming (𝟚 to Level)
open import MiniCat



-- Types

-- Contexts take variables to types
data Context : Set where
  ∅     : Context
  _,_∶_ : Context → Variable → Type → Context
variable Γ : Context

data _∋_∶_ : Context → Variable → Type → Set where
  zero : Γ , x ∶ τ ∋ x ∶ τ
  suc  : {x ≢ y} → Γ ∋ x ∶ τ₁ → Γ , y ∶ τ₂ ∋ x ∶ τ₁

-- Type and Security level judgments
data _⊢_∶_·_ : Context → Expression → Type → Level → Set where

  -- Variables

  STvar   : Γ ∋ x ∶ τ → Γ ⊢ var x ∶ τ · ℒ x


  -- Integers
  
  STint : Γ ⊢ val n ∶ int · L

  STneg :

     Γ ⊢ e ∶ int · ς →
    -----------------
    Γ ⊢ - e ∶ int · ς

  ST+ :

    Γ ⊢ e₁ ∶ int · ς₁  →  Γ ⊢ e₂ ∶ int · ς₂ →
    ---------------------------------------
          Γ ⊢ (e₁ + e₂) ∶ int · ς₁ ∨ ς₂

  ST- :

    Γ ⊢ e₁ ∶ int · ς₁  →  Γ ⊢ e₂ ∶ int · ς₂ →
    ---------------------------------------
          Γ ⊢ e₁ - e₂ ∶ int · ς₁ ∨ ς₂

  ST* :

    Γ ⊢ e₁ ∶ int · ς₁  →  Γ ⊢ e₂ ∶ int · ς₂ →
    ---------------------------------------
          Γ ⊢ e₁ * e₂ ∶ int · ς₁ ∨ ς₂

  STmod :

    Γ ⊢ e₁ ∶ int · ς₁  →  Γ ⊢ e₂ ∶ int · ς₂ →
    ---------------------------------------
          Γ ⊢ e₁ mod e₂ ∶ int · ς₁ ∨ ς₂


  -- Booleans

  STtrue  : Γ ⊢ val true  ∶ bool · L
  
  STfalse : Γ ⊢ val false ∶ bool · L

  STnot :
  
      Γ ⊢ e ∶ bool · ς   →
    --------------------
    Γ ⊢ not e ∶ bool · ς


  STand :

    Γ ⊢ e₁ ∶ bool · ς₁  →  Γ ⊢ e₂ ∶ bool · ς₂ →
    -----------------------------------------
          Γ ⊢ e₁ and e₂ ∶ bool · ς₁ ∨ ς₂

  STor :

    Γ ⊢ e₁ ∶ bool · ς₁  →  Γ ⊢ e₂ ∶ bool · ς₂ →
    -----------------------------------------
          Γ ⊢ e₁ or e₂ ∶ bool · ς₁ ∨ ς₂

  ST== :

    Γ ⊢ e₁ ∶ int · ς₁  →  Γ ⊢ e₂ ∶ int · ς₂ →
    ---------------------------------------
          Γ ⊢ e₁ == e₂ ∶ bool · ς₁ ∨ ς₂

  
  -- Conditional

  STif :

    Γ ⊢ e₁ ∶ bool · ς₁  →  Γ ⊢ e₂ ∶ τ · ς₂  →  Γ ⊢ e₃ ∶ τ · ς₃ → 
    ----------------------------------------------------------
           Γ ⊢ if e₁ then e₂ else e₃ ∶ τ · ς₁ ∨ ς₂ ∨ ς₃


⌊_⌋ : Memory → Context
⌊ ∅ ⌋ = ∅
⌊ _,_↦_ {τ} ℳ x v ⌋ = ⌊ ℳ ⌋ , x ∶ τ

lookup : ⌊ ℳ ⌋ ∋ x ∶ τ → ⟦ τ ⟧τ
lookup {_ , _ ↦ v} zero    = v
lookup {ℳ , _ ↦ _} (suc k) = lookup k

-- Evaluate well-typed expressions
⟦_⟧ : ⌊ ℳ ⌋ ⊢ e ∶ τ · ς → ⟦ τ ⟧τ
⟦ STvar k ⟧ = lookup k

⟦ STint {n = n} ⟧ = n
⟦ STneg 𝒟 ⟧ = M.- ⟦ 𝒟 ⟧
⟦ ST+ 𝒟₁ 𝒟₂ ⟧   = ⟦ 𝒟₁ ⟧ M.+ ⟦ 𝒟₂ ⟧
⟦ ST- 𝒟₁ 𝒟₂ ⟧   = ⟦ 𝒟₁ ⟧ M.- ⟦ 𝒟₂ ⟧
⟦ ST* 𝒟₁ 𝒟₂ ⟧   = ⟦ 𝒟₁ ⟧ M.* ⟦ 𝒟₂ ⟧
⟦ STmod 𝒟₁ 𝒟₂ ⟧ = ⟦ 𝒟₁ ⟧ M.mod ⟦ 𝒟₂ ⟧
⟦ STtrue  ⟧ = true
⟦ STfalse ⟧ = false
⟦ STnot 𝒟 ⟧ = M.not ⟦ 𝒟 ⟧
⟦ STand 𝒟₁ 𝒟₂ ⟧ = ⟦ 𝒟₁ ⟧ M.and ⟦ 𝒟₂ ⟧
⟦ STor 𝒟₁ 𝒟₂  ⟧ = ⟦ 𝒟₁ ⟧ M.or ⟦ 𝒟₂ ⟧
⟦ ST== 𝒟₁ 𝒟₂  ⟧ = ⟦ 𝒟₁ ⟧ M.==ℤ ⟦ 𝒟₂ ⟧
⟦ STif 𝒟₁ 𝒟₂ 𝒟₃ ⟧ = M.if ⟦ 𝒟₁ ⟧ then ⟦ 𝒟₂ ⟧ else ⟦ 𝒟₃ ⟧



--- Precedence
infixl 0 _∋_∶_ _⊢_∶_·_

infixl 1 _,_∶_
