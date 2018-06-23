module Algebra.LabelledGraph.Theorems where

open import Algebra.LabelledGraph
open import Algebra.LabelledGraph.Reasoning
open import Algebra.Dioid
open import Algebra.Graph using (Graph)
import Algebra.Graph as Graph
import Algebra.Graph.Reasoning as Graph
import Algebra.Graph.Theorems as Graph
import Algebra.Dioid.Bool as Bool
import Algebra.Dioid.Bool.Theorems as Bool

-- | Laws of labelled graphs

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

-- | Conversion functions
-- These allow for a conversion between LabelledGraphs labelled by Bools and ordinary Graphs.
-- As `graph-laws` and `labelled-graph-laws` demonstrates, these preserve their respective laws.

to-graph : ∀ {A} -> LabelledGraph Bool.bool-dioid A -> Graph A
to-graph ε = Graph.ε
to-graph (v x) = Graph.v x
to-graph (x [ Bool.false ]> y) = to-graph x Graph.+ to-graph y
to-graph (x [ Bool.true  ]> y) = to-graph x Graph.* to-graph y


labelled-graph-laws : ∀ {A} {x y : LabelledGraph Bool.bool-dioid A} -> x ≡ y -> (to-graph x) Graph.≡ (to-graph y)
labelled-graph-laws reflexivity = Graph.reflexivity
labelled-graph-laws (symmetry eq) = Graph.symmetry (labelled-graph-laws eq)
labelled-graph-laws (transitivity eq eq₁) = Graph.transitivity (labelled-graph-laws eq)
                                              (labelled-graph-laws eq₁)
labelled-graph-laws (left-congruence {r = r} eq) with r
... | Bool.true = Graph.*left-congruence (labelled-graph-laws eq)
... | Bool.false = Graph.+left-congruence (labelled-graph-laws eq)
labelled-graph-laws (right-congruence {r = r} eq) with r
... | Bool.true = Graph.*right-congruence (labelled-graph-laws eq)
... | Bool.false = Graph.+right-congruence (labelled-graph-laws eq)
labelled-graph-laws (dioid-congruence eq) = dioid-recur eq
  where
    dioid-recur : ∀ {A} {x y : LabelledGraph Bool.bool-dioid A} {r s : Bool.Bool}
               -> r Bool.≡ s -> (to-graph (x [ r ]> y)) Graph.≡ (to-graph (x [ s ]> y))
    dioid-recur Bool.reflexivity = Graph.reflexivity
    dioid-recur (Bool.symmetry eq) = Graph.symmetry (dioid-recur eq)
    dioid-recur (Bool.transitivity eq eq₁) = Graph.transitivity (dioid-recur eq) (dioid-recur eq₁)
labelled-graph-laws zero-commutativity = Graph.+commutativity
labelled-graph-laws (left-identity {r = r}) with r
... | Bool.true = Graph.*left-identity
... | Bool.false = Graph.+commutativity Graph.>> Graph.+identity
labelled-graph-laws (right-identity {r = r}) with r
... | Bool.true = Graph.*right-identity
... | Bool.false = Graph.+identity
labelled-graph-laws (left-decomposition {r = r} {s}) with r | s
... | Bool.true  | Bool.true  = Graph.*associativity Graph.>> Graph.decomposition
... | Bool.true  | Bool.false = Graph.*+ltriple
... | Bool.false | Bool.true  = Graph.+*ltriple
... | Bool.false | Bool.false = Graph.++ltriple
labelled-graph-laws (right-decomposition {r = r} {s}) with r | s
... | Bool.true  | Bool.true  = Graph.decomposition
... | Bool.true  | Bool.false = Graph.*+rtriple
... | Bool.false | Bool.true  = Graph.+*rtriple
... | Bool.false | Bool.false = Graph.++rtriple
labelled-graph-laws (label-addition {r = r} {s}) with r | s
... | Bool.true  | Bool.true  = Graph.+idempotence
... | Bool.true  | Bool.false = Graph.+associativity Graph.>> Graph.absorption
... | Bool.false | Bool.true  = (Graph.+commutativity Graph.>> Graph.+associativity) Graph.>> Graph.absorption
... | Bool.false | Bool.false = Graph.+idempotence

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

to-from-identity : ∀ {A} {x : Graph A} -> (to-graph (from-graph x)) Graph.≡ x
to-from-identity {x = Graph.ε} = Graph.reflexivity
to-from-identity {x = Graph.v x} = Graph.reflexivity
to-from-identity {x = x₁ Graph.+ x₂} = Graph.symmetry (Graph.+left-congruence  (Graph.symmetry (to-from-identity {x = x₁})))
                              Graph.>> Graph.symmetry (Graph.+right-congruence (Graph.symmetry (to-from-identity {x = x₂})))
to-from-identity {x = x₁ Graph.* x₂} = Graph.symmetry (Graph.*left-congruence  (Graph.symmetry (to-from-identity {x = x₁})))
                              Graph.>> Graph.symmetry (Graph.*right-congruence (Graph.symmetry (to-from-identity {x = x₂})))

from-to-identity : ∀ {A} {x : LabelledGraph Bool.bool-dioid A} -> (from-graph (to-graph x)) ≡ x
from-to-identity {x = ε} = reflexivity
from-to-identity {x = v x} = reflexivity
from-to-identity {x = x₁ [ d ]> x₂} with d
... | Bool.true  = symmetry (left-congruence  (symmetry (from-to-identity {x = x₁})))
                >> symmetry (right-congruence (symmetry (from-to-identity {x = x₂})))
... | Bool.false = symmetry (left-congruence  (symmetry (from-to-identity {x = x₁})))
                >> symmetry (right-congruence (symmetry (from-to-identity {x = x₂})))
