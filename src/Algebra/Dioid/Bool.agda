module Algebra.Dioid.Bool where

open import Algebra.Dioid

data Bool : Set where
  true  : Bool
  false : Bool

data _≡_ : (x y : Bool) -> Set where
  reflexivity  : ∀ {x     : Bool} ->                   x ≡ x
  symmetry     : ∀ {x y   : Bool} -> x ≡ y ->          y ≡ x
  transitivity : ∀ {x y z : Bool} -> x ≡ y -> y ≡ z -> x ≡ z

_or_ : Bool -> Bool -> Bool
false or false = false
_ or _ = true

_and_ : Bool -> Bool -> Bool
true and true = true
_ and _ = false
