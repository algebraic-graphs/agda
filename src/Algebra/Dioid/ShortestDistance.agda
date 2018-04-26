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

open import Algebra.Dioid

data ShortestDistance : Set where
  Distance : Nat.Nat -> ShortestDistance
  Unreachable : ShortestDistance

data _≡_ : (x y : ShortestDistance) -> Set where
  reflexivity  : ∀ {x     : ShortestDistance} ->                   x ≡ x
  symmetry     : ∀ {x y   : ShortestDistance} -> x ≡ y ->          y ≡ x
  transitivity : ∀ {x y z : ShortestDistance} -> x ≡ y -> y ≡ z -> x ≡ z

-- shortest-distance-dioid : Dioid -> ShortestDistance
-- shortest-distance-dioid zero = Unreachable
-- shortest-distance-dioid one  = Distance Nat.zero
-- shortest-distance-dioid (r + s) with shortest-distance-dioid r
-- ... | Unreachable = shortest-distance-dioid s
-- ... | Distance n with shortest-distance-dioid s
-- ... | Unreachable = Distance n
-- ... | Distance m = Distance (Nat.min n m)
-- shortest-distance-dioid (r * s) with shortest-distance-dioid r
-- ... | Unreachable = Unreachable
-- ... | Distance n with shortest-distance-dioid s
-- ... | Unreachable = Unreachable
-- ... | Distance m = Distance (n Nat.+ m)
