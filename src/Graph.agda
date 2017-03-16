module Graph (V : Set) where

-- Core graph construction primitives
data Graph : Set where
    ε   : Graph                   -- Empty graph
    [_] : V -> Graph              -- Graph comprising a single vertex
    _+_ : Graph -> Graph -> Graph -- Overlay two graphs
    _*_ : Graph -> Graph -> Graph -- Connect two graphs

infixl 8 _+_
infixl 9 _*_
infixl 4 _≡_

-- Equational theory of graphs
data _≡_ : (x : Graph) -> (y : Graph) -> Set where
    -- Equivalence relation
    reflexivity  : ∀ {x}     ->                       x ≡ x
    symmetry     : ∀ {x y}   -> (x ≡ y) ->            y ≡ x
    transitivity : ∀ {x y z} -> (x ≡ y) -> (y ≡ z) -> x ≡ z

    -- Congruence
    +lc : ∀ {x y z} -> (x ≡ y) -> x + z ≡ y + z
    +rc : ∀ {x y z} -> (x ≡ y) -> z + x ≡ z + y
    *lc : ∀ {x y z} -> (x ≡ y) -> x * z ≡ y * z
    *rc : ∀ {x y z} -> (x ≡ y) -> z * x ≡ z * y

    -- Axioms of +
    +commutativity : ∀ {x y}   -> x + y       ≡ y + x
    +associativity : ∀ {x y z} -> x + (y + z) ≡ (x + y) + z

    -- Axioms of *
    *left-identity  : ∀ {x}     -> ε * x       ≡ x
    *right-identity : ∀ {x}     -> x * ε       ≡ x
    *associativity  : ∀ {x y z} -> x * (y * z) ≡ (x * y) * z

    -- Other axioms
    left-distributivity  : ∀ {x y z} -> x * (y + z) ≡ x * y + x * z
    right-distributivity : ∀ {x y z} -> (x + y) * z ≡ x * z + y * z
    decomposition        : ∀ {x y z} -> x * y * z   ≡ x * y + x * z + y * z

