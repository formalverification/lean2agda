{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of OrderHom:map~ulfp
-- Lean module Mathlib.Order.Interval.Set.Defs
module U.Mathlib.Order.Interval.~sSet.Defs where
import U.Init.Prelude
import U.Mathlib.Data.~sSet.Defs
import U.Mathlib.Order.Defs.PartialOrder

~sSet:Iic : {α₀ : Set} → ⦃ _ : U.Mathlib.Order.Defs.PartialOrder.Preorder α₀ ⦄ → α₀ → U.Mathlib.Data.~sSet.Defs.~sSet α₀
~sSet:Iic {α₀} ⦃ inst₁ ⦄ b₂ = U.Mathlib.Data.~sSet.Defs.~sSet:ofPred {α₀} (λ (x₃ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ inst₁ ⦄ ⦄ x₃ b₂)
