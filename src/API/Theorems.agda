module API.Theorems where

open import Algebra
open import Algebra.Theorems
open import API
open import Prelude
open import Reasoning

-- vertices [x] == vertex x
vertices-vertex : ∀ {A} {x : A} -> vertices [ x ] ≡ vertex x
vertices-vertex = +identity >> reflexivity

-- edge x y == clique [x, y]
edge-clique : ∀ {A} {x y : A} -> edge x y ≡ clique (x :: [ y ])
edge-clique = symmetry (R *right-identity)

-- vertices xs ⊆ clique xs
vertices-clique : ∀ {A} {xs : List A} -> vertices xs ⊆ clique xs
vertices-clique {_} {[]}     = ⊆reflexivity
vertices-clique {a} {_ :: t} = ⊆transitivity (⊆right-monotony (vertices-clique {a} {t})) ⊆connect

-- clique (xs ++ ys) == connect (clique xs) (clique ys)
connect-clique : ∀ {A} {xs ys : List A} -> clique (xs ++ ys) ≡ connect (clique xs) (clique ys)
connect-clique {_} {[]}     = symmetry *left-identity
connect-clique {a} {_ :: t} = R (connect-clique {a} {t}) >> *associativity
