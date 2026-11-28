{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of OrderHom:map~ulfp
-- Lean module Mathlib.Order.Monotone.Defs
module U.Mathlib.Order.Monotone.Defs where
import U.Init.Prelude
import U.Mathlib.Order.Defs.PartialOrder

Monotone : {α₀ : Set} → {β₁ : Set} → ⦃ _ : U.Mathlib.Order.Defs.PartialOrder.Preorder α₀ ⦄ → ⦃ _ : U.Mathlib.Order.Defs.PartialOrder.Preorder β₁ ⦄ → (α₀ → β₁) → Set
Monotone {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ f₄ = {a₅ : α₀} → {b₆ : α₀} → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ inst₂ ⦄ ⦄ a₅ b₆ → U.Init.Prelude.LE:le {β₁} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {β₁} ⦃ inst₃ ⦄ ⦄ (f₄ a₅) (f₄ b₆)
