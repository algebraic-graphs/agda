module Algebra.LabelledGraph where

open import Algebra.Dioid using (Dioid)
import Algebra.Dioid as Dioid

-- Core graph construction primitives
data LabelledGraph (A : Set) : Set where
    ε   : LabelledGraph A      -- Empty graph
    v   : A -> LabelledGraph A -- Graph comprising a single vertex
    _-[_]>_ : LabelledGraph A -> Dioid -> LabelledGraph A -> LabelledGraph A
                               -- Connect two graphs

_+_ : ∀ {A} -> LabelledGraph A -> LabelledGraph A -> LabelledGraph A
g + h = g -[ Dioid.zero ]> h

_*_ : ∀ {A} -> LabelledGraph A -> LabelledGraph A -> LabelledGraph A
g * h = g -[ Dioid.one ]> h

infixl 4  _≡_
infixl 8  _+_
infixl 9  _*_
infixl 9  _-[_]>_
infix  10 _⊆_

-- Equational theory of graphs
data _≡_ {A} : (x y : LabelledGraph A) -> Set where
    -- Equivalence relation
    reflexivity  : ∀ {x     : LabelledGraph A} ->                   x ≡ x
    symmetry     : ∀ {x y   : LabelledGraph A} -> x ≡ y ->          y ≡ x
    transitivity : ∀ {x y z : LabelledGraph A} -> x ≡ y -> y ≡ z -> x ≡ z

    -- Congruence
    left-congruence  : ∀ {x y z : LabelledGraph A} {r : Dioid} -> x ≡ y -> x -[ r ]> z ≡ y -[ r ]> z
    right-congruence : ∀ {x y z : LabelledGraph A} {r : Dioid} -> x ≡ y -> z -[ r ]> x ≡ z -[ r ]> y

    -- Axioms
    zero-commutativity  : ∀ {x y : LabelledGraph A} -> x + y ≡ y + x
    left-identity       : ∀ {x     : LabelledGraph A} {r   : Dioid} -> ε -[ r ]> x ≡ x
    right-identity      : ∀ {x     : LabelledGraph A} {r   : Dioid} -> x -[ r ]> ε ≡ x
    left-decomposition  : ∀ {x y z : LabelledGraph A} {r s : Dioid} -> x -[ r ]> (y -[ s ]> z) ≡ (x -[ r ]> y) + (x -[ r ]> z) + (y -[ s ]> z)
    right-decomposition : ∀ {x y z : LabelledGraph A} {r s : Dioid} -> (x -[ r ]> y) -[ s ]> z ≡ (x -[ r ]> y) + (x -[ s ]> z) + (y -[ s ]> z)
    label-addition      : ∀ {x y   : LabelledGraph A} {r s : Dioid} -> (x -[ r ]> y) + (x -[ s ]> y) ≡ (x -[ r Dioid.+ s ]> y)

-- Subgraph relation
_⊆_ : ∀ {A} -> LabelledGraph A -> LabelledGraph A -> Set
x ⊆ y = x + y ≡ y
