module Algebra.Dioid.Bool.Theorems where

open import Algebra.Dioid
open import Algebra.Dioid.Bool

or-left-congruence : ∀ {b c d : Bool} -> b ≡ c -> (b or d) ≡ (c or d)
or-left-congruence {b} {.b} {d} reflexivity = reflexivity
or-left-congruence {b} {c} {d} (symmetry eq) = symmetry (or-left-congruence eq)
or-left-congruence {b} {c} {d} (transitivity eq eq₁) = transitivity (or-left-congruence eq) (or-left-congruence eq₁)

or-right-congruence : ∀ {b c d : Bool} -> c ≡ d -> (b or c) ≡ (b or d)
or-right-congruence {b} {c} {.c} reflexivity = reflexivity
or-right-congruence {b} {c} {d} (symmetry eq) = symmetry (or-right-congruence eq)
or-right-congruence {b} {c} {d} (transitivity eq eq₁) = transitivity (or-right-congruence eq) (or-right-congruence eq₁)

and-left-congruence : ∀ {b c d : Bool} -> b ≡ c -> (b and d) ≡ (c and d)
and-left-congruence {b} {.b} {d} reflexivity = reflexivity
and-left-congruence {b} {c} {d} (symmetry eq) = symmetry (and-left-congruence eq)
and-left-congruence {b} {c} {d} (transitivity eq eq₁) = transitivity (and-left-congruence eq) (and-left-congruence eq₁)

and-right-congruence : ∀ {b c d : Bool} -> c ≡ d -> (b and c) ≡ (b and d)
and-right-congruence {b} {c} {.c} reflexivity = reflexivity
and-right-congruence {b} {c} {d} (symmetry eq) = symmetry (and-right-congruence eq)
and-right-congruence {b} {c} {d} (transitivity eq eq₁) = transitivity (and-right-congruence eq) (and-right-congruence eq₁)

or-idempotence : ∀ {b : Bool} -> (b or b) ≡ b
or-idempotence {true} = reflexivity
or-idempotence {false} = reflexivity

or-commutativity : ∀ {b c : Bool} -> (b or c) ≡ (c or b)
or-commutativity {true} {true} = reflexivity
or-commutativity {true} {false} = reflexivity
or-commutativity {false} {true} = reflexivity
or-commutativity {false} {false} = reflexivity

or-associativity : ∀ {b c d : Bool} -> (b or (c or d)) ≡ ((b or c) or d)
or-associativity {true} {c} {d} = reflexivity
or-associativity {false} {true} {d} = reflexivity
or-associativity {false} {false} {true} = reflexivity
or-associativity {false} {false} {false} = reflexivity

or-false-identity : ∀ {b : Bool} -> (b or false) ≡ b
or-false-identity {true} = reflexivity
or-false-identity {false} = reflexivity

and-associativity : ∀ {b c d : Bool} -> (b and (c and d)) ≡ ((b and c) and d)
and-associativity {true} {true} {true} = reflexivity
and-associativity {true} {true} {false} = reflexivity
and-associativity {true} {false} {d} = reflexivity
and-associativity {false} {c} {d} = reflexivity

and-left-false : ∀ {b : Bool} -> (false and b) ≡ false
and-left-false {b} = reflexivity

and-right-false : ∀ {b : Bool} -> (b and false) ≡ false
and-right-false {true} = reflexivity
and-right-false {false} = reflexivity

and-left-true : ∀ {b : Bool} -> (true and b) ≡ b
and-left-true {true} = reflexivity
and-left-true {false} = reflexivity

and-right-true : ∀ {b : Bool} -> (b and true) ≡ b
and-right-true {true} = reflexivity
and-right-true {false} = reflexivity

left-distributivity : ∀ {b c d : Bool} -> (b and (c or d)) ≡ ((b and c) or (b and d))
left-distributivity {true} {true} {d} = reflexivity
left-distributivity {true} {false} {true} = reflexivity
left-distributivity {true} {false} {false} = reflexivity
left-distributivity {false} {c} {d} = reflexivity

right-distributivity : ∀ {b c d : Bool} -> ((b or c) and d) ≡ ((b and d) or (c and d))
right-distributivity {true} {true} {true} = reflexivity
right-distributivity {true} {true} {false} = reflexivity
right-distributivity {true} {false} {true} = reflexivity
right-distributivity {true} {false} {false} = reflexivity
right-distributivity {false} {true} {true} = reflexivity
right-distributivity {false} {true} {false} = reflexivity
right-distributivity {false} {false} {d} = reflexivity

bool-dioid : Dioid Bool _≡_
bool-dioid = record
  { zero = false
  ; one  = true
  ; _+_  = _or_
  ; _*_  = _and_
  ; reflexivity  = reflexivity
  ; symmetry     = symmetry
  ; transitivity = transitivity

  ; +left-congruence  = or-left-congruence
  ; *left-congruence  = and-left-congruence
  ; *right-congruence = and-right-congruence

  ; +idempotence   = or-idempotence
  ; +commutativity = or-commutativity
  ; +associativity = or-associativity
  ; +zero-identity = or-false-identity

  ; *associativity  = and-associativity
  ; *left-zero      = λ {r} → reflexivity
  ; *right-zero     = and-right-false
  ; *left-identity  = and-left-true
  ; *right-identity = and-right-true

  ; left-distributivity  = left-distributivity
  ; right-distributivity = right-distributivity
  }
