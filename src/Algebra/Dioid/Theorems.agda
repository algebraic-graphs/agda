module Algebra.Dioid.Theorems where

open import Algebra.Dioid
open import Algebra.Dioid.Reasoning

left-zero-identity : ∀ {r : Dioid} -> (zero + r) ≡ r
left-zero-identity {r} =
  begin
    zero + r ≡⟨ +commutativity ⟩
    r + zero ≡⟨ +zero-identity ⟩
    r
  ∎
