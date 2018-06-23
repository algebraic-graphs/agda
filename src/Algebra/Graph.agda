module Algebra.Graph where

-- Core graph construction primitives
data Graph (A : Set) : Set where
    ε   : Graph A                       -- Empty graph
    v   : A -> Graph A                  -- Graph comprising a single vertex
    _+_ : Graph A -> Graph A -> Graph A -- Overlay two graphs
    _*_ : Graph A -> Graph A -> Graph A -- Connect two graphs

infixl 4  _≡_
infixl 8  _+_
infixl 9  _*_
infix  10 _⊆_

-- Equational theory of graphs
data _≡_ {A} : (x y : Graph A) -> Set where
    -- Equivalence relation
    reflexivity  : ∀ {x     : Graph A} ->                   x ≡ x
    symmetry     : ∀ {x y   : Graph A} -> x ≡ y ->          y ≡ x
    transitivity : ∀ {x y z : Graph A} -> x ≡ y -> y ≡ z -> x ≡ z

    -- Congruence
    +left-congruence  : ∀ {x y z : Graph A} -> x ≡ y -> x + z ≡ y + z
    -- +right-congruence holds as a theorem, please see below
    *left-congruence  : ∀ {x y z : Graph A} -> x ≡ y -> x * z ≡ y * z
    *right-congruence : ∀ {x y z : Graph A} -> x ≡ y -> z * x ≡ z * y

    -- Axioms of +
    +commutativity : ∀ {x y : Graph A}   -> x + y       ≡ y + x
    +associativity : ∀ {x y z : Graph A} -> x + (y + z) ≡ (x + y) + z

    -- Axioms of *
    *left-identity  : ∀ {x     : Graph A} -> ε * x       ≡ x
    *right-identity : ∀ {x     : Graph A} -> x * ε       ≡ x
    *associativity  : ∀ {x y z : Graph A} -> x * (y * z) ≡ (x * y) * z

    -- Other axioms
    left-distributivity  : ∀ {x y z : Graph A} -> x * (y + z) ≡ x * y + x * z
    right-distributivity : ∀ {x y z : Graph A} -> (x + y) * z ≡ x * z + y * z
    decomposition        : ∀ {x y z : Graph A} -> x * y * z   ≡ x * y + x * z + y * z

+right-congruence : ∀ {A} {x y z : Graph A} -> x ≡ y -> z + x ≡ z + y
+right-congruence {_} {x} {y} {z} eq = transitivity +commutativity (transitivity (+left-congruence eq) +commutativity)

-- Subgraph relation
_⊆_ : ∀ {A} -> Graph A -> Graph A -> Set
x ⊆ y = x + y ≡ y
