module Algebra.LabelledGraph.Reasoning where

open import Algebra.Dioid using (Dioid)
open import Algebra.LabelledGraph

-- Standard syntax sugar for writing equational proofs
infix 4 _≈_
data _≈_ {A} (x y : LabelledGraph A) : Set where
    prove : x ≡ y -> x ≈ y

infix 1 begin_
begin_ : ∀ {A} {x y : LabelledGraph A} -> x ≈ y -> x ≡ y
begin prove p = p

infixr 2 _≡⟨_⟩_
_≡⟨_⟩_ : ∀ {A} (x : LabelledGraph A) {y z : LabelledGraph A} -> x ≡ y -> y ≈ z -> x ≈ z
_ ≡⟨ p ⟩ prove q = prove (transitivity p q)

infix 3 _∎
_∎ : ∀ {A} (x : LabelledGraph A) -> x ≈ x
_∎ _ = prove reflexivity

infixl 8 _>>_
_>>_ : ∀ {A} {x y z : LabelledGraph A} -> x ≡ y -> y ≡ z -> x ≡ z
_>>_ = transitivity

L : ∀ {A} {x y z : LabelledGraph A} {r : Dioid} -> x ≡ y -> x [ r ]> z ≡ y [ r ]> z
L = left-congruence

R : ∀ {A} {x y z : LabelledGraph A} {r : Dioid} -> x ≡ y -> z [ r ]> x ≡ z [ r ]> y
R = right-congruence
