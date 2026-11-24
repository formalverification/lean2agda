{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of Subtype:coe~ueta
-- Lean module Mathlib.Data.Subtype
module U.Mathlib.Data.Subtype where
import U.Init.Core
import U.Init.Prelude

-- theorem
opaque
  Subtype:coe~ueta : {α₀ : Set} → {p₁ : α₀ → Set} → (a₂ : U.Init.Prelude.Subtype {α₀} (λ (a₂ : α₀) → p₁ a₂)) → (h₃ : p₁ (U.Init.Prelude.Subtype:val {α₀} {λ (a₃ : α₀) → p₁ a₃} a₂)) → U.Init.Prelude.Eq {U.Init.Prelude.Subtype {α₀} (λ (a₄ : α₀) → p₁ a₄)} (U.Init.Prelude.Subtype:mk {α₀} {λ (a₄ : α₀) → p₁ a₄} (U.Init.Prelude.Subtype:val {α₀} {λ (a₄ : α₀) → p₁ a₄} a₂) h₃) a₂
  Subtype:coe~ueta {α₀} {p₁} a₂ h₃ = U.Init.Core.Subtype:ext {α₀} {p₁} {U.Init.Prelude.Subtype:mk {α₀} {λ (a₄ : α₀) → p₁ a₄} (U.Init.Prelude.Subtype:val {α₀} {λ (a₄ : α₀) → p₁ a₄} a₂) h₃} {a₂} (U.Init.Prelude.rfl {α₀} {U.Init.Prelude.Subtype:val {α₀} {λ (x₄ : α₀) → p₁ x₄} (U.Init.Prelude.Subtype:mk {α₀} {λ (a₄ : α₀) → p₁ a₄} (U.Init.Prelude.Subtype:val {α₀} {λ (a₄ : α₀) → p₁ a₄} a₂) h₃)})
