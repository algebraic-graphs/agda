module Algebra.Theorems where

open import Algebra
open import Reasoning

+pre-idempotence : ∀ {A} {x : Graph A} -> x + x + ε ≡ x
+pre-idempotence {_} {x} =
  begin
    (x + x) + ε             ≡⟨ L (L (symmetry *right-identity)) ⟩
    (x * ε + x) + ε         ≡⟨ L (R (symmetry *right-identity)) ⟩
    (x * ε + x * ε) + ε     ≡⟨ R (symmetry *right-identity)     ⟩
    (x * ε + x * ε) + ε * ε ≡⟨ symmetry decomposition           ⟩
    (x * ε) * ε             ≡⟨ *right-identity                  ⟩
    x * ε                   ≡⟨ *right-identity                  ⟩
    x
  ∎

+identity : ∀ {A} {x : Graph A} -> x + ε ≡ x
+identity {_} {x} =
  begin
    x + ε                   ≡⟨ symmetry +pre-idempotence       ⟩
    ((x + ε) + (x + ε)) + ε ≡⟨ L +associativity                ⟩
    (((x + ε) + x) + ε) + ε ≡⟨ L (L (symmetry +associativity)) ⟩
    ((x + (ε + x)) + ε) + ε ≡⟨ L (L (R +commutativity))        ⟩
    ((x + (x + ε)) + ε) + ε ≡⟨ L (L +associativity)            ⟩
    (((x + x) + ε) + ε) + ε ≡⟨ L (symmetry +associativity)     ⟩
    ((x + x) + (ε + ε)) + ε ≡⟨ symmetry +associativity         ⟩
    (x + x) + ((ε + ε) + ε) ≡⟨ R +pre-idempotence              ⟩
    (x + x) + ε             ≡⟨ +pre-idempotence                ⟩
    x
  ∎

+idempotence : ∀ {A} {x : Graph A} -> x + x ≡ x
+idempotence = transitivity (symmetry +identity) +pre-idempotence

saturation : ∀ {A} {x : Graph A} -> x * x * x ≡ x * x
saturation {_} {x} =
  begin
    (x * x) * x             ≡⟨ decomposition  ⟩
    (x * x + x * x) + x * x ≡⟨ L +idempotence ⟩
    x * x + x * x           ≡⟨ +idempotence   ⟩
    x * x
  ∎

absorption : ∀ {A} {x y : Graph A} -> x * y + x + y ≡ x * y
absorption {_} {x} {y} =
  begin
    (x * y + x) + y         ≡⟨ L (R (symmetry *right-identity)) ⟩
    (x * y + x * ε) + y     ≡⟨ R (symmetry *right-identity)     ⟩
    (x * y + x * ε) + y * ε ≡⟨ symmetry decomposition           ⟩
    (x * y) * ε             ≡⟨ *right-identity                  ⟩
    x * y
  ∎

-- Subgraph relation
⊆reflexivity : ∀ {A} {x : Graph A} -> x ⊆ x
⊆reflexivity = +idempotence

⊆antisymmetry : ∀ {A} {x y : Graph A} -> x ⊆ y -> y ⊆ x -> x ≡ y
⊆antisymmetry p q = symmetry q      -- x = y + x
                 >> +commutativity  --     y + x = x + y
                 >> p               --             x + y = y

⊆transitivity : ∀ {A} {x y z : Graph A} -> x ⊆ y -> y ⊆ z -> x ⊆ z
⊆transitivity p q = symmetry
    (symmetry q              -- z = y + z
  >> L (symmetry p)          --     y + z = (x + y) + z
  >> symmetry +associativity --             (x + y) + z = x + (y + z)
  >> R q)                    --                           x + (y + z) = x + z

⊆least-element : ∀ {A} {x : Graph A} -> ε ⊆ x
⊆least-element = +commutativity >> +identity

⊆overlay : ∀ {A} {x y : Graph A} -> x ⊆ (x + y)
⊆overlay = +associativity >> L +idempotence

⊆connect : ∀ {A} {x y : Graph A} -> (x + y) ⊆ (x * y)
⊆connect = +commutativity >> +associativity >> absorption

⊆left-overlay-monotony : ∀ {A} {x y z : Graph A} -> x ⊆ y -> (x + z) ⊆ (y + z)
⊆left-overlay-monotony {_} {x} {y} {z} p =
  begin
    (x + z) + (y + z) ≡⟨ symmetry +associativity     ⟩
    x + (z + (y + z)) ≡⟨ R +commutativity            ⟩
    x + ((y + z) + z) ≡⟨ R (symmetry +associativity) ⟩
    x + (y + (z + z)) ≡⟨ R (R +idempotence)          ⟩
    x + (y + z)       ≡⟨ +associativity              ⟩
    (x + y) + z       ≡⟨ L p                         ⟩
    y + z
  ∎

⊆right-overlay-monotony : ∀ {A} {x y z : Graph A} -> x ⊆ y -> (z + x) ⊆ (z + y)
⊆right-overlay-monotony {_} {x} {y} {z} p =
  begin
    (z + x) + (z + y) ≡⟨ +associativity          ⟩
    ((z + x) + z) + y ≡⟨ L +commutativity        ⟩
    (z + (z + x)) + y ≡⟨ L +associativity        ⟩
    ((z + z) + x) + y ≡⟨ L (L +idempotence)      ⟩
    (z + x) + y       ≡⟨ symmetry +associativity ⟩
    z + (x + y)       ≡⟨ R p                     ⟩
    z + y
  ∎

⊆left-connect-monotony : ∀ {A} {x y z : Graph A} -> x ⊆ y -> (x * z) ⊆ (y * z)
⊆left-connect-monotony {_} {x} {y} {z} p =
  begin
    (x * z) + (y * z) ≡⟨ symmetry right-distributivity ⟩
    (x + y) * z       ≡⟨ L p                           ⟩
    y * z
  ∎

⊆right-connect-monotony : ∀ {A} {x y z : Graph A} -> x ⊆ y -> (z * x) ⊆ (z * y)
⊆right-connect-monotony {_} {x} {y} {z} p =
  begin
    (z * x) + (z * y) ≡⟨ symmetry left-distributivity ⟩
    z * (x + y)       ≡⟨ R p                          ⟩
    z * y
  ∎

⊆left-monotony : ∀ {A} {op : BinaryOperator} {x y z : Graph A} -> x ⊆ y -> apply op x z ⊆ apply op y z
⊆left-monotony {_} {+op} {x} {y} {z} p = ⊆left-overlay-monotony p
⊆left-monotony {_} {*op} {x} {y} {z} p = ⊆left-connect-monotony p

⊆right-monotony : ∀ {A} {op : BinaryOperator} {x y z : Graph A} -> x ⊆ y -> apply op z x ⊆ apply op z y
⊆right-monotony {_} {+op} {x} {y} {z} p = ⊆right-overlay-monotony p
⊆right-monotony {_} {*op} {x} {y} {z} p = ⊆right-connect-monotony p
