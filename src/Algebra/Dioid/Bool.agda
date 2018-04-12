module Algebra.Dioid.Bool where

open import Algebra.Dioid using (Dioid; zero; one; _+_; _*_)

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

boolDioid : Dioid -> Bool
boolDioid zero = false
boolDioid one  = true
boolDioid (r + s) = boolDioid r or  boolDioid s
boolDioid (r * s) = boolDioid r and boolDioid s
