module API where

open import Algebra
open import Prelude

empty : ∀ {A} -> Graph A
empty = ε

vertex : ∀ {A} -> A -> Graph A
vertex = v

overlay : ∀ {A} -> Graph A -> Graph A -> Graph A
overlay = _+_

connect : ∀ {A} -> Graph A -> Graph A -> Graph A
connect = _*_

edge : ∀ {A} -> A -> A -> Graph A
edge x y = connect (vertex x) (vertex y)

overlays : ∀ {A} -> List (Graph A) -> Graph A
overlays = foldr overlay empty

connects : ∀ {A} -> List (Graph A) -> Graph A
connects = foldr connect empty

vertices : ∀ {A} -> List A -> Graph A
vertices = overlays ∘ map vertex

clique : ∀ {A} -> List A -> Graph A
clique = connects ∘ map vertex

edges : ∀ {A} -> List (A × A) -> Graph A
edges = overlays ∘ map (uncurry edge)

graph : ∀ {A} -> List A -> List (A × A) -> Graph A
graph vs es = overlay (vertices vs) (edges es)
