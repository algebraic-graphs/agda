module Theorems (A : Set) where

open import Graph A
open import Reasoning A

+pre-idempotence : ∀ {x} -> x + x + ε ≡ x
+pre-idempotence {x} =
  begin
    (x + x) + ε             ≡⟨ +lc (+lc (symmetry *right-identity)) ⟩
    (x * ε + x) + ε         ≡⟨ +lc (+rc (symmetry *right-identity)) ⟩
    (x * ε + x * ε) + ε     ≡⟨ +rc (symmetry *right-identity)       ⟩
    (x * ε + x * ε) + ε * ε ≡⟨ symmetry decomposition               ⟩
    (x * ε) * ε             ≡⟨ *right-identity                      ⟩
    x * ε                   ≡⟨ *right-identity                      ⟩
    x
  ∎

+identity : ∀ {x} -> x + ε ≡ x
+identity {x} =
  begin
    x + ε                   ≡⟨ symmetry +pre-idempotence           ⟩
    ((x + ε) + (x + ε)) + ε ≡⟨ +lc +associativity                  ⟩
    (((x + ε) + x) + ε) + ε ≡⟨ +lc (+lc (symmetry +associativity)) ⟩
    ((x + (ε + x)) + ε) + ε ≡⟨ +lc (+lc (+rc +commutativity))      ⟩
    ((x + (x + ε)) + ε) + ε ≡⟨ +lc (+lc +associativity)            ⟩
    (((x + x) + ε) + ε) + ε ≡⟨ +lc (symmetry +associativity)       ⟩
    ((x + x) + (ε + ε)) + ε ≡⟨ symmetry +associativity             ⟩
    (x + x) + ((ε + ε) + ε) ≡⟨ +rc +pre-idempotence                ⟩
    (x + x) + ε             ≡⟨ +pre-idempotence                    ⟩
    x
  ∎

+idempotence : ∀ {x} -> x + x ≡ x
+idempotence = transitivity (symmetry +identity) +pre-idempotence
