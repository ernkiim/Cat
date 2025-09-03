module MetaCat where

open import Data.Nat using (ℕ) public
open import Data.Integer hiding (suc) renaming (_≟_ to _≟ℤ_) public
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_) renaming (_≟_ to _≟B_) public
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality public

-- For all n m ∈ ℤ, return the least nonnegative k ≡ n (mod m) (defined for m = 0)
_mod_ : ℤ → ℤ → ℤ
n mod + 0          = n
n mod m@(+[1+ _ ]) = + (n % m)
n mod m@(-[1+ _ ]) = + (n % m)

infixl 7 _mod_

-- Boolean equality for integers
_==ℤ_ : ℤ → ℤ → Bool
n ==ℤ m = ⌊ n ≟ℤ m ⌋

-- Boolean equality for Bools
_==B_ : Bool → Bool → Bool
b ==B b′ = ⌊ b ≟B b′ ⌋

infixl 7 _==ℤ_ _==B_
