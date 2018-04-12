module API where

open import Algebra.Graph
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

edges : ∀ {A} -> List (A × A) -> Graph A
edges = overlays ∘ map (uncurry edge)

graph : ∀ {A} -> List A -> List (A × A) -> Graph A
graph vs es = overlay (vertices vs) (edges es)

foldg : ∀ {A} {B : Set} -> B -> (A -> B) -> (B -> B -> B) -> (B -> B -> B) -> Graph A -> B
foldg {A} {B} e w o c = go
  where
    go : Graph A -> B
    go ε       = e
    go (v x)   = w x
    go (x + y) = o (go x) (go y)
    go (x * y) = c (go x) (go y)

path : ∀ {A} -> List A -> Graph A
path []        = empty
path (x :: []) = vertex x
path (x :: xs) = edges (zip (x :: xs) xs)

circuit : ∀ {A} -> List A -> Graph A
circuit []        = empty
circuit (x :: xs) = path ([ x ] ++ xs ++ [ x ])

clique : ∀ {A} -> List A -> Graph A
clique = connects ∘ map vertex

biclique : ∀ {A} -> List A -> List A -> Graph A
biclique xs ys = connect (vertices xs) (vertices ys)

star : ∀ {A} -> A -> List A -> Graph A
star x ys = connect (vertex x) (vertices ys)

