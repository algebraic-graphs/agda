module Theorems (A : Set) where

open import Graph A
open import Reasoning A

+pre-idempotence : ∀ x -> x ≡ x + x + ε
+pre-idempotence x =
  begin
    x                     ≡⟨ symmetry *right-identity  ⟩
    x * ε                 ≡⟨ symmetry *right-identity  ⟩
    x * ε * ε             ≡⟨ decomposition             ⟩
    x * ε + x * ε + ε * ε ≡⟨ +rc *right-identity       ⟩
    x * ε + x * ε + ε     ≡⟨ +lc (+rc *right-identity) ⟩
    x * ε + x + ε         ≡⟨ +lc (+lc *right-identity) ⟩
    x + x + ε
  ∎

+identity : ∀ x -> x ≡ x + ε
+identity x =
  begin
    x                       ≡⟨ +pre-idempotence x                  ⟩
    (x + x) + ε             ≡⟨ +rc (+pre-idempotence ε)            ⟩
    (x + x) + ((ε + ε) + ε) ≡⟨ +associativity                      ⟩
    ((x + x) + (ε + ε)) + ε ≡⟨ +lc +associativity                  ⟩
    (((x + x) + ε) + ε) + ε ≡⟨ +lc (+lc (symmetry +associativity)) ⟩
    ((x + (x + ε)) + ε) + ε ≡⟨ +lc (+lc (+rc +commutativity))      ⟩
    ((x + (ε + x)) + ε) + ε ≡⟨ +lc (+lc +associativity)            ⟩
    (((x + ε) + x) + ε) + ε ≡⟨ +lc (symmetry +associativity)       ⟩
    ((x + ε) + (x + ε)) + ε ≡⟨ symmetry (+pre-idempotence (x + ε)) ⟩
    x + ε
  ∎

