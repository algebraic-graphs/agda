module Theorems (A : Set) where

open import Graph A
open import Reasoning A

+pre-idempotence : ∀ {x} -> x + x + ε ≡ x
+pre-idempotence {x} =
  begin
    (x + x) + ε             ≡⟨ L (L (symmetry *right-identity)) ⟩
    (x * ε + x) + ε         ≡⟨ L (R (symmetry *right-identity)) ⟩
    (x * ε + x * ε) + ε     ≡⟨ R (symmetry *right-identity)     ⟩
    (x * ε + x * ε) + ε * ε ≡⟨ symmetry decomposition           ⟩
    (x * ε) * ε             ≡⟨ *right-identity                  ⟩
    x * ε                   ≡⟨ *right-identity                  ⟩
    x
  ∎

+identity : ∀ {x} -> x + ε ≡ x
+identity {x} =
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

+idempotence : ∀ {x} -> x + x ≡ x
+idempotence = transitivity (symmetry +identity) +pre-idempotence

saturation : ∀ {x} -> x * x * x ≡ x * x
saturation {x} =
  begin
    (x * x) * x             ≡⟨ decomposition  ⟩
    (x * x + x * x) + x * x ≡⟨ L +idempotence ⟩
    x * x + x * x           ≡⟨ +idempotence   ⟩
    x * x
  ∎

absorption : ∀ {x y} -> x * y + x + y ≡ x * y
absorption {x} {y} =
  begin
    (x * y + x) + y         ≡⟨ L (R (symmetry *right-identity)) ⟩
    (x * y + x * ε) + y     ≡⟨ R (symmetry *right-identity)     ⟩
    (x * y + x * ε) + y * ε ≡⟨ symmetry decomposition           ⟩
    (x * y) * ε             ≡⟨ *right-identity                  ⟩
    x * y
  ∎

-- Subgraph relation
⊆reflexivity : ∀ {x} -> x ⊆ x
⊆reflexivity = +idempotence

⊆antisymmetry : ∀ {x y} -> x ⊆ y -> y ⊆ x -> x ≡ y
⊆antisymmetry p q = symmetry q      -- x = y + x
                 >> +commutativity  --     y + x = x + y
                 >> p               --             x + y = y

⊆transitivity : ∀ {x y z} -> x ⊆ y -> y ⊆ z -> x ⊆ z
⊆transitivity p q = symmetry
    (symmetry q              -- z = y + z
  >> L (symmetry p)          --     y + z = (x + y) + z
  >> symmetry +associativity --             (x + y) + z = x + (y + z)
  >> R q)                    --                           x + (y + z) = x + z

⊆least-element : ∀ {x} -> ε ⊆ x
⊆least-element = +commutativity >> +identity

⊆overlay : ∀ {x y} -> x ⊆ (x + y)
⊆overlay = +associativity >> L +idempotence

⊆connect : ∀ {x y} -> (x + y) ⊆ (x * y)
⊆connect = +commutativity >> +associativity >> absorption

⊆overlay-monotony : ∀ {x y z} -> x ⊆ y -> (x + z) ⊆ (y + z)
⊆overlay-monotony {x} {y} {z} p =
  begin
    (x + z) + (y + z) ≡⟨ symmetry +associativity     ⟩
    x + (z + (y + z)) ≡⟨ R +commutativity            ⟩
    x + ((y + z) + z) ≡⟨ R (symmetry +associativity) ⟩
    x + (y + (z + z)) ≡⟨ R (R +idempotence)          ⟩
    x + (y + z)       ≡⟨ +associativity              ⟩
    (x + y) + z       ≡⟨ L p                         ⟩
    y + z
  ∎

⊆left-connect-monotony : ∀ {x y z} -> x ⊆ y -> (x * z) ⊆ (y * z)
⊆left-connect-monotony {x} {y} {z} p =
  begin
    (x * z) + (y * z) ≡⟨ symmetry right-distributivity ⟩
    (x + y) * z       ≡⟨ L p                           ⟩
    y * z
  ∎

⊆right-connect-monotony : ∀ {x y z} -> x ⊆ y -> (z * x) ⊆ (z * y)
⊆right-connect-monotony {x} {y} {z} p =
  begin
    (z * x) + (z * y) ≡⟨ symmetry left-distributivity ⟩
    z * (x + y)       ≡⟨ R p                          ⟩
    z * y
  ∎
