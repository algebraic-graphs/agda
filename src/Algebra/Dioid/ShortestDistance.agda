module Algebra.Dioid.ShortestDistance where

module Nat where
  data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

  min : Nat -> Nat -> Nat
  min zero n = n
  min n zero = n
  min (succ n) (succ m) = min n m

  _+_ : Nat -> Nat -> Nat
  zero + n = n
  n + zero = n
  (succ n) + m = succ (n + m)

open import Algebra.Dioid using (Dioid; zero; one; _+_; _*_)

data ShortestDistance : Set where
  Distance : Nat.Nat -> ShortestDistance
  Unreachable : ShortestDistance

data _≡_ : (x y : ShortestDistance) -> Set where
  reflexivity  : ∀ {x     : ShortestDistance} ->                   x ≡ x
  symmetry     : ∀ {x y   : ShortestDistance} -> x ≡ y ->          y ≡ x
  transitivity : ∀ {x y z : ShortestDistance} -> x ≡ y -> y ≡ z -> x ≡ z

shortestDistanceDioid : Dioid -> ShortestDistance
shortestDistanceDioid zero = Unreachable
shortestDistanceDioid one  = Distance Nat.zero
shortestDistanceDioid (r + s) with shortestDistanceDioid r
... | Unreachable = shortestDistanceDioid s
... | Distance n with shortestDistanceDioid s
... | Unreachable = Distance n
... | Distance m = Distance (Nat.min n m)
shortestDistanceDioid (r * s) with shortestDistanceDioid r
... | Unreachable = Unreachable
... | Distance n with shortestDistanceDioid s
... | Unreachable = Unreachable
... | Distance m = Distance (n Nat.+ m)
