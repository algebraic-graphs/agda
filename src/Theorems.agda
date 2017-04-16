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
