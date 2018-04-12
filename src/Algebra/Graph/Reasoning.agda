module Algebra.Graph.Reasoning where

open import Algebra.Graph

-- Standard syntax sugar for writing equational proofs
infix 4 _≈_
data _≈_ {A} (x y : Graph A) : Set where
    prove : x ≡ y -> x ≈ y

infix 1 begin_
begin_ : ∀ {A} {x y : Graph A} -> x ≈ y -> x ≡ y
begin prove p = p

infixr 2 _≡⟨_⟩_
_≡⟨_⟩_ : ∀ {A} (x : Graph A) {y z : Graph A} -> x ≡ y -> y ≈ z -> x ≈ z
_ ≡⟨ p ⟩ prove q = prove (transitivity p q)

infix 3 _∎
_∎ : ∀ {A} (x : Graph A) -> x ≈ x
_∎ _ = prove reflexivity

infixl 8 _>>_
_>>_ : ∀ {A} {x y z : Graph A} -> x ≡ y -> y ≡ z -> x ≡ z
_>>_ = transitivity

data BinaryOperator : Set where
  +op : BinaryOperator
  *op : BinaryOperator

apply : ∀ {A} -> BinaryOperator -> Graph A -> Graph A -> Graph A
apply +op a b = a + b
apply *op a b = a * b

L : ∀ {op : BinaryOperator} -> ∀ {A} {x y z : Graph A} -> x ≡ y -> apply op x z ≡ apply op y z
L {+op} {x} {y} {z} eq = +left-congruence {x} {y} {z} eq
L {*op} {x} {y} {z} eq = *left-congruence {x} {y} {z} eq

R : ∀ {op : BinaryOperator} -> ∀ {A} {x y z : Graph A} -> x ≡ y -> apply op z x ≡ apply op z y
R {+op} {x} {y} {z} eq = +right-congruence {x} {y} {z} eq
R {*op} {x} {y} {z} eq = *right-congruence {x} {y} {z} eq
