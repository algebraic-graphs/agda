module Algebra.LabelledGraph.Theorems where

open import Algebra.LabelledGraph
open import Algebra.LabelledGraph.Reasoning
open import Algebra.Dioid using (Dioid)
import Algebra.Dioid as Dioid
open import Algebra.Graph using (Graph)
import Algebra.Graph as Graph
import Algebra.Dioid.Bool as Bool


associativity : ∀ {A} {a b c : LabelledGraph A} {r : Dioid} -> (a -[ r ]> b) -[ r ]> c ≡ a -[ r ]> (b -[ r ]> c)
associativity {_} {a} {b} {c} {r} = right-decomposition >> symmetry left-decomposition

absorption : ∀ {A} {a b : LabelledGraph A} {r : Dioid} -> a -[ r ]> b ≡ a -[ r ]> b + a + b
absorption {_} {a} {b} {r} =
  begin
    (a -[ r ]> b) ≡⟨ symmetry right-identity ⟩
    (a -[ r ]> b) -[ Dioid.zero ]> ε ≡⟨ right-decomposition ⟩
    (a -[ r ]> b) + (a + ε) + (b + ε) ≡⟨ L (R right-identity ) ⟩
    (a -[ r ]> b) + a + (b + ε) ≡⟨ R right-identity ⟩
    (a -[ r ]> b) + a + b
  ∎

idempotence : ∀ {A} {a : LabelledGraph A} -> a ≡ a + a
idempotence {_} {a} =
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

right-distributivity : ∀ {A} {a b c : LabelledGraph A} {r : Dioid} -> (a + b) -[ r ]> c ≡ a -[ r ]> c + b -[ r ]> c
right-distributivity {_} {a} {b} {c} {r} =
  begin
    (a + b) -[ r ]> c ≡⟨ right-decomposition ⟩
    ((a + b) + (a -[ r ]> c)) + (b -[ r ]> c) ≡⟨ L (R absorption) ⟩
    (a + b) + ((a -[ r ]> c) + a + c) + (b -[ r ]> c) ≡⟨ R absorption ⟩
    (a + b) + ((a -[ r ]> c) + a + c) + ((b -[ r ]> c) + b + c) ≡⟨ L (associativity)⟩
    a + (b + ((a -[ r ]> c) + a + c)) + ((b -[ r ]> c) + b + c) ≡⟨ L (R zero-commutativity)⟩
    a + (((a -[ r ]> c) + a + c) + b) + ((b -[ r ]> c) + b + c) ≡⟨ associativity ⟩
    a + ((((a -[ r ]> c) + a + c) + b) + ((b -[ r ]> c) + b + c)) ≡⟨ R (associativity) ⟩
    a + (((a -[ r ]> c) + a + c) + (b + ((b -[ r ]> c) + b + c))) ≡⟨ R (R zero-commutativity)⟩
    a + (((a -[ r ]> c) + a + c) + (((b -[ r ]> c) + b + c) + b)) ≡⟨ R (R associativity) ⟩
    a + (((a -[ r ]> c) + a + c) + ((b -[ r ]> c) + b + (c + b))) ≡⟨ R (R (R zero-commutativity)) ⟩
    a + (((a -[ r ]> c) + a + c) + ((b -[ r ]> c) + b + (b + c))) ≡⟨ R (R (symmetry associativity)) ⟩
    a + (((a -[ r ]> c) + a + c) + ((b -[ r ]> c) + b + b + c)) ≡⟨ R (R (L associativity)) ⟩
    a + (((a -[ r ]> c) + a + c) + ((b -[ r ]> c) + (b + b) + c)) ≡⟨ R (R (L (R (symmetry idempotence))))⟩
    a + (((a -[ r ]> c) + a + c) + ((b -[ r ]> c) + b + c)) ≡⟨ R (R (symmetry absorption)) ⟩
    a + (((a -[ r ]> c) + a + c) + (b -[ r ]> c)) ≡⟨ symmetry associativity ⟩
    a + ((a -[ r ]> c) + a + c) + (b -[ r ]> c) ≡⟨ L zero-commutativity ⟩
    ((a -[ r ]> c) + a + c) + a + (b -[ r ]> c) ≡⟨ L associativity ⟩
    ((a -[ r ]> c) + a + (c + a)) + (b -[ r ]> c) ≡⟨ L (R zero-commutativity)⟩
    ((a -[ r ]> c) + a + (a + c)) + (b -[ r ]> c) ≡⟨ L (symmetry associativity)⟩
    ((a -[ r ]> c) + a + a + c) + (b -[ r ]> c) ≡⟨ L (L associativity)⟩
    ((a -[ r ]> c) + (a + a) + c) + (b -[ r ]> c) ≡⟨ L (L (R (symmetry idempotence))) ⟩
    ((a -[ r ]> c) + a + c) + (b -[ r ]> c) ≡⟨ L (symmetry absorption) ⟩
    (a -[ r ]> c) + (b -[ r ]> c)
  ∎

left-distributivity : ∀ {A} {a b c : LabelledGraph A} {r : Dioid} -> a -[ r ]> (b + c) ≡ a -[ r ]> b + a -[ r ]> c
left-distributivity {_} {a} {b} {c} {r} =
  begin
    a -[ r ]> (b + c) ≡⟨ left-decomposition ⟩
    a -[ r ]> b + a -[ r ]> c + (b + c) ≡⟨ symmetry associativity ⟩
    a -[ r ]> b + a -[ r ]> c + b + c ≡⟨ L associativity ⟩
    a -[ r ]> b + (a -[ r ]> c + b) + c ≡⟨ L (R zero-commutativity) ⟩
    a -[ r ]> b + (b + a -[ r ]> c) + c ≡⟨ L (symmetry associativity) ⟩
    a -[ r ]> b + b + a -[ r ]> c + c ≡⟨ L (L (L absorption)) ⟩
    (a -[ r ]> b + a + b) + b + a -[ r ]> c + c ≡⟨ L (L associativity) ⟩
    a -[ r ]> b + a + (b + b) + a -[ r ]> c + c ≡⟨ L (L (R (symmetry idempotence))) ⟩
    a -[ r ]> b + a + b + a -[ r ]> c + c ≡⟨ L (L (symmetry absorption)) ⟩
    a -[ r ]> b + a -[ r ]> c + c ≡⟨ L (R absorption) ⟩
    a -[ r ]> b + (a -[ r ]> c + a + c) + c ≡⟨ associativity ⟩
    a -[ r ]> b + (a -[ r ]> c + a + c + c) ≡⟨ (R associativity) ⟩
    a -[ r ]> b + (a -[ r ]> c + a + (c + c)) ≡⟨ R (R (symmetry idempotence)) ⟩
    a -[ r ]> b + (a -[ r ]> c + a + c) ≡⟨ R (symmetry absorption) ⟩
    a -[ r ]> b + a -[ r ]> c
  ∎

-- Notice that we can't define 'graph-laws' below for 'to-graph' as we can't derive the
-- labelled graph laws from a graph alone. The two constructs are therefore not isomorphic.
to-graph : ∀ {A} -> LabelledGraph A -> Graph A
to-graph ε = Graph.ε
to-graph (v x) = Graph.v x
to-graph (x -[ r ]> y) with Bool.boolDioid r
... | Bool.false = to-graph x Graph.+ to-graph y
... | Bool.true  = to-graph x Graph.* to-graph y

from-graph : ∀ {A} -> Graph A -> LabelledGraph A
from-graph Graph.ε = ε
from-graph (Graph.v x) = v x
from-graph (x Graph.+ y) = from-graph x -[ Dioid.zero ]> from-graph y
from-graph (x Graph.* y) = from-graph x -[ Dioid.one  ]> from-graph y

graph-laws : ∀ {A} {x y : Graph A} -> x Graph.≡ y -> from-graph x ≡ from-graph y
graph-laws {x = x} {.x} Graph.reflexivity = reflexivity
graph-laws {x = x} {y} (Graph.symmetry eq) = symmetry (graph-laws eq)
graph-laws {x = x} {y} (Graph.transitivity eq eq₁) = transitivity (graph-laws eq) (graph-laws eq₁)
graph-laws {x = .(_ Graph.+ _)} {.(_ Graph.+ _)} (Graph.+left-congruence eq) = left-congruence (graph-laws eq)
graph-laws {x = .(_ Graph.+ _)} {.(_ Graph.+ _)} (Graph.+right-congruence eq) = right-congruence (graph-laws eq)
graph-laws {x = .(_ Graph.* _)} {.(_ Graph.* _)} (Graph.*left-congruence eq) = left-congruence (graph-laws eq)
graph-laws {x = .(_ Graph.* _)} {.(_ Graph.* _)} (Graph.*right-congruence eq) = right-congruence (graph-laws eq)
graph-laws {x = .(_ Graph.+ _)} {.(_ Graph.+ _)} Graph.+commutativity = zero-commutativity
graph-laws {x = .(_ Graph.+ (_ Graph.+ _))} {.(_ Graph.+ _ Graph.+ _)} Graph.+associativity = symmetry associativity
graph-laws {x = .(Graph.ε Graph.* y)} {y} Graph.*left-identity = left-identity
graph-laws {x = .(y Graph.* Graph.ε)} {y} Graph.*right-identity = right-identity
graph-laws {x = .(_ Graph.* (_ Graph.* _))} {.(_ Graph.* _ Graph.* _)} Graph.*associativity = symmetry associativity
graph-laws {x = .(_ Graph.* (_ Graph.+ _))} {.(_ Graph.* _ Graph.+ _ Graph.* _)} Graph.left-distributivity = left-distributivity
graph-laws {x = .((_ Graph.+ _) Graph.* _)} {.(_ Graph.* _ Graph.+ _ Graph.* _)} Graph.right-distributivity = right-distributivity
graph-laws {x = .(_ Graph.* _ Graph.* _)} {.(_ Graph.* _ Graph.+ _ Graph.* _ Graph.+ _ Graph.* _)} Graph.decomposition = right-decomposition
