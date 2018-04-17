module Algebra.Dioid where

data Dioid : Set where
  zero : Dioid
  one  : Dioid
  _+_  : Dioid -> Dioid -> Dioid
  _*_  : Dioid -> Dioid -> Dioid

infixl 4  _≡_
infixl 8  _+_
infixl 9  _*_

-- Equational theory of dioids
data _≡_ : (r s : Dioid) -> Set where
    -- Equivalence relation
    reflexivity  : ∀ {r     : Dioid} ->                   r ≡ r
    symmetry     : ∀ {r s   : Dioid} -> r ≡ s ->          s ≡ r
    transitivity : ∀ {r s t : Dioid} -> r ≡ s -> s ≡ t -> r ≡ t

    -- Congruence
    +left-congruence  : ∀ {r s t : Dioid} -> r ≡ s -> r + t ≡ s + t
    +right-congruence : ∀ {r s t : Dioid} -> r ≡ s -> t + r ≡ t + s
    *left-congruence  : ∀ {r s t : Dioid} -> r ≡ s -> r * t ≡ s * t
    *right-congruence : ∀ {r s t : Dioid} -> r ≡ s -> t * r ≡ t * s

    -- Axioms of +
    +idempotence   : ∀ {r : Dioid}     -> r + r       ≡ r
    +commutativity : ∀ {r s : Dioid}   -> r + s       ≡ s + r
    +associativity : ∀ {r s t : Dioid} -> r + (s + t) ≡ (r + s) + t
    +zero-identity : ∀ {r : Dioid}     -> r + zero    ≡ r

    -- Axioms of *
    *associativity  : ∀ {r s t : Dioid} -> r * (s * t) ≡ (r * s) * t
    *left-zero      : ∀ {r : Dioid}     -> zero * r    ≡ zero
    *right-zero     : ∀ {r : Dioid}     -> r * zero    ≡ zero
    *left-identity  : ∀ {r : Dioid}     -> one * r     ≡ r
    *right-identity : ∀ {r : Dioid}     -> r * one     ≡ r

    -- Distributivity
    left-distributivity  : ∀ {r s t : Dioid} -> r * (s + t) ≡ r * s + r * t
    right-distributivity : ∀ {r s t : Dioid} -> (r + s) * t ≡ r * t + s * t
