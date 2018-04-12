module Algebra.Dioid.Bool.Theorems where

open import Algebra.Dioid using (Dioid; zero; one; _+_; _*_)
import Algebra.Dioid
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

boolDioidLawful : ∀ {r s : Dioid} -> r Algebra.Dioid.≡ s -> boolDioid r ≡ boolDioid s
boolDioidLawful {r} {.r} Algebra.Dioid.reflexivity = reflexivity
boolDioidLawful {r} {s} (Algebra.Dioid.symmetry eq) = symmetry (boolDioidLawful eq)
boolDioidLawful {r} {s} (Algebra.Dioid.transitivity eq eq₁) = transitivity (boolDioidLawful eq) (boolDioidLawful eq₁)
boolDioidLawful {.(_ + _)} {.(_ + _)} (Algebra.Dioid.+left-congruence eq) = or-left-congruence (boolDioidLawful eq)
boolDioidLawful {.(_ + _)} {.(_ + _)} (Algebra.Dioid.+right-congruence eq) = or-right-congruence (boolDioidLawful eq)
boolDioidLawful {.(_ * _)} {.(_ * _)} (Algebra.Dioid.*left-congruence eq) = and-left-congruence (boolDioidLawful eq)
boolDioidLawful {.(_ * _)} {.(_ * _)} (Algebra.Dioid.*right-congruence eq) = and-right-congruence (boolDioidLawful eq)
boolDioidLawful {.(s + s)} {s} Algebra.Dioid.+idempotence = or-idempotence
boolDioidLawful {.(_ + _)} {.(_ + _)} Algebra.Dioid.+commutativity = or-commutativity
boolDioidLawful {.(_ + (_ + _))} {.(_ + _ + _)} Algebra.Dioid.+associativity = or-associativity
boolDioidLawful {.(s + zero)} {s} Algebra.Dioid.+zero-identity = or-false-identity
boolDioidLawful {.(_ * (_ * _))} {.(_ * _ * _)} Algebra.Dioid.*associativity = and-associativity
boolDioidLawful {.(zero * _)} {.zero} Algebra.Dioid.*left-zero = reflexivity
boolDioidLawful {.(_ * zero)} {.zero} Algebra.Dioid.*right-zero = and-right-false
boolDioidLawful {.(one * s)} {s} Algebra.Dioid.*left-identity = and-left-true
boolDioidLawful {.(s * one)} {s} Algebra.Dioid.*right-identity = and-right-true
boolDioidLawful {.(_ * (_ + _))} {.(_ * _ + _ * _)} Algebra.Dioid.left-distributivity = left-distributivity
boolDioidLawful {.((_ + _) * _)} {.(_ * _ + _ * _)} Algebra.Dioid.right-distributivity = right-distributivity
