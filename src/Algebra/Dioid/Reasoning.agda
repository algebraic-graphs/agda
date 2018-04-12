module Algebra.Dioid.Reasoning where

open import Algebra.Dioid

-- Standard syntax sugar for writing equational proofs
infix 4 _≈_
data _≈_ (x y : Dioid) : Set where
    prove : x ≡ y -> x ≈ y

infix 1 begin_
begin_ : ∀ {x y : Dioid} -> x ≈ y -> x ≡ y
begin prove p = p

infixr 2 _≡⟨_⟩_
_≡⟨_⟩_ : ∀ (x : Dioid) {y z : Dioid} -> x ≡ y -> y ≈ z -> x ≈ z
_ ≡⟨ p ⟩ prove q = prove (transitivity p q)

infix 3 _∎
_∎ : ∀ (x : Dioid) -> x ≈ x
_∎ _ = prove reflexivity

infixl 8 _>>_
_>>_ : ∀ {x y z : Dioid} -> x ≡ y -> y ≡ z -> x ≡ z
_>>_ = transitivity

data BinaryOperator : Set where
  +op : BinaryOperator
  *op : BinaryOperator

apply : BinaryOperator -> Dioid -> Dioid -> Dioid
apply +op a b = a + b
apply *op a b = a * b

L : ∀ {op : BinaryOperator} -> ∀ {x y z : Dioid} -> x ≡ y -> apply op x z ≡ apply op y z
L {+op} {x} {y} {z} eq = +left-congruence {x} {y} {z} eq
L {*op} {x} {y} {z} eq = *left-congruence {x} {y} {z} eq

R : ∀ {op : BinaryOperator} -> ∀ {x y z : Dioid} -> x ≡ y -> apply op z x ≡ apply op z y
R {+op} {x} {y} {z} eq = +right-congruence {x} {y} {z} eq
R {*op} {x} {y} {z} eq = *right-congruence {x} {y} {z} eq
