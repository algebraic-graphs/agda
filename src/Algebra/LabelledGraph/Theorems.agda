module Algebra.LabelledGraph.Theorems where

open import Algebra.LabelledGraph
open import Algebra.LabelledGraph.Reasoning
open import Algebra.Dioid
open import Algebra.Graph using (Graph)
import Algebra.Graph as Graph
import Algebra.Dioid.Bool as Bool


associativity : ∀ {A D eq} {d : Dioid D eq} {a b c : LabelledGraph d A} {r : D} -> (a [ r ]> b) [ r ]> c ≡ a [ r ]> (b [ r ]> c)
associativity {_} {_} {_} {_} {a} {b} {c} {r} = right-decomposition >> symmetry left-decomposition

absorption : ∀ {A D eq} {d : Dioid D eq} {a b : LabelledGraph d A} {r : D} -> a [ r ]> b ≡ a [ r ]> b + a + b
absorption {_} {_} {_} {d} {a} {b} {r} =
  begin
    (a [ r ]> b) ≡⟨ symmetry right-identity ⟩
    (a [ r ]> b) [ Dioid.zero d ]> ε ≡⟨ right-decomposition ⟩
    (a [ r ]> b) + (a + ε) + (b + ε) ≡⟨ L (R right-identity ) ⟩
    (a [ r ]> b) + a + (b + ε) ≡⟨ R right-identity ⟩
    (a [ r ]> b) + a + b
  ∎

idempotence : ∀ {A D eq} {d : Dioid D eq} {a : LabelledGraph d A} -> a ≡ a + a
idempotence {_} {_} {_} {_} {a} =
  begin
    a ≡⟨ symmetry right-identity ⟩
    a + ε ≡⟨ symmetry right-identity ⟩
    a + ε + ε ≡⟨ right-decomposition ⟩
    (a + ε) + (a + ε) + (ε + ε) ≡⟨ right-congruence left-identity ⟩
    (a + ε) + (a + ε) + ε ≡⟨ right-identity ⟩
    (a + ε) + (a + ε) ≡⟨ right-congruence right-identity ⟩
    (a + ε) + a ≡⟨ left-congruence right-identity ⟩
    a + a
  ∎

left-absorption : ∀ {A D eq} {d : Dioid D eq} {a b : LabelledGraph d A} {r : D} -> a [ r ]> b ≡ a [ r ]> b + a
left-absorption {_} {_} {_} {_} {a} {b} {r} =
  begin
    (a [ r ]> b)                 ≡⟨ absorption ⟩
    (a [ r ]> b) + a + b         ≡⟨ L (R idempotence) ⟩
    (a [ r ]> b) + (a + a) + b   ≡⟨ associativity ⟩
    (a [ r ]> b) + (a + a + b)   ≡⟨ R zero-commutativity ⟩
    (a [ r ]> b) + (b + (a + a)) ≡⟨ R (symmetry associativity) ⟩
    (a [ r ]> b) + ((b + a) + a) ≡⟨ R (L zero-commutativity) ⟩
    (a [ r ]> b) + ((a + b) + a) ≡⟨ symmetry associativity ⟩
    (a [ r ]> b) + (a + b) + a   ≡⟨ L (symmetry associativity) ⟩
    (a [ r ]> b) + a + b + a     ≡⟨ L (symmetry absorption) ⟩
    (a [ r ]> b) + a
  ∎

right-absorption : ∀ {A D eq} {d : Dioid D eq} {a b : LabelledGraph d A} {r : D} -> a [ r ]> b ≡ a [ r ]> b + b
right-absorption {_} {_} {_} {_} {a} {b} {r} =
  begin
    (a [ r ]> b)               ≡⟨ absorption ⟩
    (a [ r ]> b) + a + b       ≡⟨ R idempotence ⟩
    (a [ r ]> b) + a + (b + b) ≡⟨ symmetry associativity ⟩
    (a [ r ]> b) + a + b + b   ≡⟨ L (symmetry absorption) ⟩
    (a [ r ]> b) + b
  ∎

right-distributivity : ∀ {A D eq} {d : Dioid D eq} {a b c : LabelledGraph d A} {r : D} -> (a + b) [ r ]> c ≡ a [ r ]> c + b [ r ]> c
right-distributivity {_} {_} {_} {_} {a} {b} {c} {r} =
  begin
    (a + b) [ r ]> c                       ≡⟨ right-decomposition ⟩
    a + b + (a [ r ]> c) + (b [ r ]> c)   ≡⟨ L zero-commutativity ⟩
    (a [ r ]> c) + (a + b) + (b [ r ]> c) ≡⟨ L (symmetry associativity) ⟩
    ((a [ r ]> c) + a) + b + (b [ r ]> c) ≡⟨ L (L (symmetry left-absorption)) ⟩
    (a [ r ]> c) + b + (b [ r ]> c)       ≡⟨ associativity ⟩
    (a [ r ]> c) + (b + (b [ r ]> c))     ≡⟨ R zero-commutativity ⟩
    (a [ r ]> c) + ((b [ r ]> c) + b)     ≡⟨ R (symmetry left-absorption) ⟩
    (a [ r ]> c) + (b [ r ]> c)
  ∎

left-distributivity : ∀ {A D eq} {d : Dioid D eq} {a b c : LabelledGraph d A} {r : D} -> a [ r ]> (b + c) ≡ a [ r ]> b + a [ r ]> c
left-distributivity {_} {_} {_} {_} {a} {b} {c} {r} =
  begin
    a [ r ]> (b + c)                   ≡⟨ left-decomposition ⟩
    a [ r ]> b + a [ r ]> c + (b + c) ≡⟨ symmetry associativity ⟩
    a [ r ]> b + a [ r ]> c + b + c   ≡⟨ L associativity ⟩
    a [ r ]> b + (a [ r ]> c + b) + c ≡⟨ L (R zero-commutativity) ⟩
    a [ r ]> b + (b + a [ r ]> c) + c ≡⟨ L (symmetry associativity) ⟩
    a [ r ]> b + b + a [ r ]> c + c   ≡⟨ L (L (symmetry right-absorption)) ⟩
    a [ r ]> b + a [ r ]> c + c       ≡⟨ associativity ⟩
    a [ r ]> b + (a [ r ]> c + c)     ≡⟨ R (symmetry right-absorption) ⟩
    a [ r ]> b + a [ r ]> c
  ∎

-- Notice that we can't define 'graph-laws' below for 'to-graph' as we can't derive the
-- labelled graph laws from a graph alone. The two constructs are therefore not isomorphic.
to-graph : ∀ {A} {d : Dioid Bool.Bool Bool._≡_} -> LabelledGraph d A -> Graph A
to-graph ε = Graph.ε
to-graph (v x) = Graph.v x
to-graph (x [ Bool.false ]> y) = to-graph x Graph.+ to-graph y
to-graph (x [ Bool.true  ]> y) = to-graph x Graph.* to-graph y

from-graph : ∀ {A D eq} {d : Dioid D eq} -> Graph A -> LabelledGraph d A
from-graph Graph.ε = ε
from-graph (Graph.v x) = v x
from-graph {_} {_} {_} {d} (x Graph.+ y) = from-graph x [ Dioid.zero d ]> from-graph y
from-graph {_} {_} {_} {d} (x Graph.* y) = from-graph x [ Dioid.one  d ]> from-graph y

graph-laws : ∀ {A D eq} {d : Dioid D eq} {x y : Graph A} -> x Graph.≡ y -> _≡_ {A} {D} {eq} {d} (from-graph x) (from-graph y)
graph-laws {x = x} {.x} Graph.reflexivity = reflexivity
graph-laws {x = x} {y} (Graph.symmetry eq) = symmetry (graph-laws eq)
graph-laws {x = x} {y} (Graph.transitivity eq eq₁) = transitivity (graph-laws eq) (graph-laws eq₁)
graph-laws {x = .(_ Graph.+ _)} {.(_ Graph.+ _)} (Graph.+left-congruence eq)  = left-congruence (graph-laws eq)
graph-laws {x = .(_ Graph.+ _)} {.(_ Graph.+ _)} (Graph.+right-congruence eq) = right-congruence (graph-laws eq)
graph-laws {x = .(_ Graph.* _)} {.(_ Graph.* _)} (Graph.*left-congruence eq)  = left-congruence (graph-laws eq)
graph-laws {x = .(_ Graph.* _)} {.(_ Graph.* _)} (Graph.*right-congruence eq) = right-congruence (graph-laws eq)
graph-laws {x = .(_ Graph.+ _)} {.(_ Graph.+ _)} Graph.+commutativity = zero-commutativity
graph-laws {x = .(_ Graph.+ (_ Graph.+ _))} {.(_ Graph.+ _ Graph.+ _)} Graph.+associativity = symmetry associativity
graph-laws {x = .(Graph.ε Graph.* y)} {y} Graph.*left-identity = left-identity
graph-laws {x = .(y Graph.* Graph.ε)} {y} Graph.*right-identity = right-identity
graph-laws {x = .(_ Graph.* (_ Graph.* _))} {.(_ Graph.* _ Graph.* _)} Graph.*associativity = symmetry associativity
graph-laws {x = .(_ Graph.* (_ Graph.+ _))} {.(_ Graph.* _ Graph.+ _ Graph.* _)} Graph.left-distributivity = left-distributivity
graph-laws {x = .((_ Graph.+ _) Graph.* _)} {.(_ Graph.* _ Graph.+ _ Graph.* _)} Graph.right-distributivity = right-distributivity
graph-laws {x = .(_ Graph.* _ Graph.* _)} {.(_ Graph.* _ Graph.+ _ Graph.* _ Graph.+ _ Graph.* _)} Graph.decomposition = right-decomposition
