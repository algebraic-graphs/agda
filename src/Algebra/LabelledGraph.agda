module Algebra.LabelledGraph where

open import Algebra.Dioid

-- Core graph construction primitives
data LabelledGraph {D eq} (d : Dioid D eq) (A : Set) : Set where
    ε   : LabelledGraph d A      -- Empty graph
    v   : A -> LabelledGraph d A -- Graph comprising a single vertex
    _[_]>_ : LabelledGraph d A -> D -> LabelledGraph d A -> LabelledGraph d A
                               -- Connect two graphs

_+_ : ∀ {A D eq} {d : Dioid D eq} -> LabelledGraph d A -> LabelledGraph d A -> LabelledGraph d A
_+_ {_} {_} {_} {d} g h = g [ Dioid.zero d ]> h

_*_ : ∀ {A D eq} {d : Dioid D eq}  -> LabelledGraph d A -> LabelledGraph d A -> LabelledGraph d A
_*_ {_} {_} {_} {d} g h = g [ Dioid.one d ]> h

infixl 4  _≡_
infixl 8  _+_
infixl 9  _*_
infixl 9  _[_]>_
infix  10 _⊆_

-- Equational theory of graphs
data _≡_ {A D eq} {d : Dioid D eq} : (x y : LabelledGraph d A) -> Set where
    -- Equivalence relation
    reflexivity  : ∀ {x     : LabelledGraph d A} ->                   x ≡ x
    symmetry     : ∀ {x y   : LabelledGraph d A} -> x ≡ y ->          y ≡ x
    transitivity : ∀ {x y z : LabelledGraph d A} -> x ≡ y -> y ≡ z -> x ≡ z

    -- Congruence
    left-congruence  : ∀ {x y z : LabelledGraph d A} {r : D} -> x ≡ y -> x [ r ]> z ≡ y [ r ]> z
    right-congruence : ∀ {x y z : LabelledGraph d A} {r : D} -> x ≡ y -> z [ r ]> x ≡ z [ r ]> y

    -- Axioms
    zero-commutativity  : ∀ {x y : LabelledGraph d A} -> x + y ≡ y + x
    left-identity       : ∀ {x     : LabelledGraph d A} {r   : D} -> ε [ r ]> x ≡ x
    right-identity      : ∀ {x     : LabelledGraph d A} {r   : D} -> x [ r ]> ε ≡ x
    left-decomposition  : ∀ {x y z : LabelledGraph d A} {r s : D} -> x [ r ]> (y [ s ]> z) ≡ (x [ r ]> y) + (x [ r ]> z) + (y [ s ]> z)
    right-decomposition : ∀ {x y z : LabelledGraph d A} {r s : D} -> (x [ r ]> y) [ s ]> z ≡ (x [ r ]> y) + (x [ s ]> z) + (y [ s ]> z)
    label-addition      : ∀ {x y   : LabelledGraph d A} {r s : D} -> (x [ r ]> y) + (x [ s ]> y) ≡ (x [ Dioid.plus d r s ]> y)

-- Subgraph relation
_⊆_ : ∀ {A D eq} {d : Dioid D eq} -> LabelledGraph d A -> LabelledGraph d A -> Set
x ⊆ y = x + y ≡ y
