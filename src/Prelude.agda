module Prelude where

-- Function composition
_∘_ : ∀ {x y z : Set} -> (y -> z) -> (x -> y) -> (x -> z)
(f ∘ g) x = f (g x)

-- Product type
data _×_ (A B : Set) : Set where
    _,_ : A -> B -> A × B

uncurry : ∀ {x y z : Set} -> (x -> y -> z) -> (x × y) -> z
uncurry f (a , b) = f a b

-- Lists
data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

infixr 20 _::_

_++_ : ∀ {A} -> List A -> List A -> List A
[] ++ l = l
(x :: xs) ++ l = x :: (xs ++ l)

foldr : ∀ {A B : Set} -> (A -> B -> B) -> B -> List A -> B
foldr f b [] = b
foldr f b (x :: xs) = f x (foldr f b xs)

map : ∀ {A B} -> (A -> B) -> List A -> List B
map f [] = []
map f (x :: xs) = f x :: map f xs
