module API.Laws where

open import API
open import Graph
open import Prelude
open import Reasoning
open import Theorems

-- vertices [x] == vertex x
vertices-vertex : ∀ {A} {x : A} -> vertices (x :: []) ≡ vertex x
vertices-vertex = +identity >> reflexivity

-- vertices xs ⊆ clique xs
vertices-clique : ∀ {A} {xs : List A} -> vertices xs ⊆ clique xs
vertices-clique {_} {[]}     = ⊆reflexivity
vertices-clique {a} {_ :: t} = ⊆transitivity (⊆right-monotony (vertices-clique {a} {t})) ⊆connect

-- clique (xs ++ ys) == connect (clique xs) (clique ys)
connect-clique : ∀ {A} {xs ys : List A} -> clique (xs ++ ys) ≡ connect (clique xs) (clique ys)
connect-clique {_} {[]}     = symmetry *left-identity
connect-clique {a} {h :: t} = R (connect-clique {a} {t}) >> *associativity
