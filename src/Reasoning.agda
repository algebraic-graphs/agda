module Reasoning (A : Set) where

open import Graph A

-- Standard syntax sugar for writing equational proofs
infix 4 _≈_
data _≈_ (x y : Graph) : Set where
    prove : x ≡ y -> x ≈ y

infix 1 begin_
begin_ : {x y : Graph} -> x ≈ y -> x ≡ y
begin prove p = p

infixr 2 _≡⟨_⟩_
_≡⟨_⟩_ : (x : Graph) {y z : Graph} -> x ≡ y -> y ≈ z -> x ≈ z
_ ≡⟨ p ⟩ prove q = prove (transitivity p q)

infix 3 _∎
_∎ : (x : Graph) -> x ≈ x
_∎ _ = prove reflexivity

infixl 8 _>>_
_>>_ : ∀ {x y z} -> x ≡ y -> y ≡ z -> x ≡ z
_>>_ = transitivity
