{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of Multiset:map~umap
-- Lean module Batteries.Logic
module U.Batteries.Logic where
import U.Init.Prelude

-- theorem
opaque
  congr~uarg : {α₀ : Set} → {β₁ : Set} → {a₂ : α₀} → {a₃ : α₀} → (f₄ : α₀ → β₁) → U.Init.Prelude.Eq {α₀} a₂ a₃ → U.Init.Prelude.Eq {β₁} (f₄ a₂) (f₄ a₃)
  congr~uarg = U.Init.Prelude.congrArg
