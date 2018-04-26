module Algebra.LabelledGraph.Reasoning where

open import Algebra.Dioid
open import Algebra.LabelledGraph

-- Standard syntax sugar for writing equational proofs
infix 4 _≈_
data _≈_ {A B eq} {d : Dioid B eq} (x y : LabelledGraph d A) : Set where
    prove : x ≡ y -> x ≈ y

infix 1 begin_
begin_ : ∀ {A B eq} {d : Dioid B eq} {x y : LabelledGraph d A} -> x ≈ y -> x ≡ y
begin prove p = p

infixr 2 _≡⟨_⟩_
_≡⟨_⟩_ : ∀ {A B eq} {d : Dioid B eq} (x : LabelledGraph d A) {y z : LabelledGraph d A} -> x ≡ y -> y ≈ z -> x ≈ z
_ ≡⟨ p ⟩ prove q = prove (transitivity p q)

infix 3 _∎
_∎ : ∀ {A B eq} {d : Dioid B eq} (x : LabelledGraph d A) -> x ≈ x
_∎ _ = prove reflexivity

infixl 8 _>>_
_>>_ : ∀ {A B eq} {d : Dioid B eq} {x y z : LabelledGraph d A} -> x ≡ y -> y ≡ z -> x ≡ z
_>>_ = transitivity

L : ∀ {A B eq} {d : Dioid B eq} {x y z : LabelledGraph d A} {r : B} -> x ≡ y -> x [ r ]> z ≡ y [ r ]> z
L = left-congruence

R : ∀ {A B eq} {d : Dioid B eq} {x y z : LabelledGraph d A} {r : B} -> x ≡ y -> z [ r ]> x ≡ z [ r ]> y
R = right-congruence
