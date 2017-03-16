module Theorems (A : Set) where

open import Graph A
open import Reasoning A

+pre-idempotence : ∀ {x} -> x + x + ε ≡ x
+pre-idempotence {x} = symmetry
  (begin
    x                     ≡⟨ symmetry *right-identity  ⟩
    x * ε                 ≡⟨ symmetry *right-identity  ⟩
    x * ε * ε             ≡⟨ decomposition             ⟩
    x * ε + x * ε + ε * ε ≡⟨ +rc *right-identity       ⟩
    x * ε + x * ε + ε     ≡⟨ +lc (+rc *right-identity) ⟩
    x * ε + x + ε         ≡⟨ +lc (+lc *right-identity) ⟩
    x + x + ε
  ∎)

+identity : ∀ {x} -> x + ε ≡ x
+identity {x} = symmetry
  (begin
    x                       ≡⟨ symmetry +pre-idempotence           ⟩
    (x + x) + ε             ≡⟨ +rc (symmetry +pre-idempotence)     ⟩
    (x + x) + ((ε + ε) + ε) ≡⟨ +associativity                      ⟩
    ((x + x) + (ε + ε)) + ε ≡⟨ +lc +associativity                  ⟩
    (((x + x) + ε) + ε) + ε ≡⟨ +lc (+lc (symmetry +associativity)) ⟩
    ((x + (x + ε)) + ε) + ε ≡⟨ +lc (+lc (+rc +commutativity))      ⟩
    ((x + (ε + x)) + ε) + ε ≡⟨ +lc (+lc +associativity)            ⟩
    (((x + ε) + x) + ε) + ε ≡⟨ +lc (symmetry +associativity)       ⟩
    ((x + ε) + (x + ε)) + ε ≡⟨ +pre-idempotence                    ⟩
    x + ε
  ∎)

+idempotence : ∀ {x} -> x + x ≡ x
+idempotence = transitivity (symmetry +identity) +pre-idempotence
