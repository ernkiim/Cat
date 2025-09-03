module Programs where

open import Expressions

variable
  M M′ : Memory
  A B  : Type
  x y  : Variable
  e e′ : M ⊢ A


-- Programs relate memories to memories
infix 0 _⇓_
data _⇓_ : Memory → Memory → Set where

  ∅ :

    -----
    M ⇓ M

  _≔_⨾_ : ∀ x (e : M ⊢ A) →

    M , x ⦂ A ↦ ⟦ e ⟧e ⇓ M′ →
    -----------------------
            M ⇓ M′


-- Examples

--_ : (ϵ , x ⦂ ℤ ↦ (+ 2))  ⇓ ( ϵ , x ⦂ ℤ ↦ + 2 , y ⦂ ℤ ↦ + 3 , z ⦂ ℤ ↦ + 6)
