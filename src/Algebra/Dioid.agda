module Algebra.Dioid where

record Dioid A (_≡_ : A -> A -> Set) : Set where
  field
    zero : A
    one  : A
    _+_  : A -> A -> A
    _*_  : A -> A -> A

    reflexivity  : ∀ {r     : A} ->                   r ≡ r
    symmetry     : ∀ {r s   : A} -> r ≡ s ->          s ≡ r
    transitivity : ∀ {r s t : A} -> r ≡ s -> s ≡ t -> r ≡ t

    +left-congruence  : ∀ {r s t : A} -> r ≡ s -> (r + t) ≡ (s + t)
    -- +right-congruence holds but as a theorem, please see below
    *left-congruence  : ∀ {r s t : A} -> r ≡ s -> (r * t) ≡ (s * t)
    *right-congruence : ∀ {r s t : A} -> r ≡ s -> (t * r) ≡ (t * s)

    +idempotence   : ∀ {r : A}      -> (r + r)       ≡ r
    +commutativity : ∀ {r s : A}    -> (r + s)       ≡ (s + r)
    +associativity : ∀ {r s t : A}  -> (r + (s + t)) ≡ ((r + s) + t)
    +zero-identity : ∀ {r : A}      -> (r + zero)    ≡ r

    *associativity  : ∀ {r s t : A} -> (r * (s * t)) ≡ ((r * s) * t)
    *left-zero      : ∀ {r : A}     -> (zero * r)    ≡ zero
    *right-zero     : ∀ {r : A}     -> (r * zero)    ≡ zero
    *left-identity  : ∀ {r : A}     -> (one * r)     ≡ r
    *right-identity : ∀ {r : A}     -> (r * one)     ≡ r

    left-distributivity  : ∀ {r s t : A} -> (r * (s + t)) ≡ ((r * s) + (r * t))
    right-distributivity : ∀ {r s t : A} -> ((r + s) * t) ≡ ((r * t) + (s * t))

  -- For convenience to avoid `Dioid._+_ d r s`
  plus : A -> A -> A
  plus x y = x + y

  times : A -> A -> A
  times x y = x * y

+right-congruence : ∀ {D eq} {d : Dioid D eq} {r s t : D} -> eq r s -> eq (Dioid.plus d t r) (Dioid.plus d t s)
+right-congruence {_} {_} {d} {r} {s} {t} e = trans commut (trans (Dioid.+left-congruence d e) commut)
  where
    trans = Dioid.transitivity d
    commut = Dioid.+commutativity d
