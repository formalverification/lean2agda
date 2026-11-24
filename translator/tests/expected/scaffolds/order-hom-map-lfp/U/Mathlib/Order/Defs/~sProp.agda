{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of OrderHom:map~ulfp
-- Lean module Mathlib.Order.Defs.Prop
module U.Mathlib.Order.Defs.~sProp where
import U.Init.Prelude

Pi:hasLe : {ι₀ : Set} → {π₁ : ι₀ → Set} → ⦃ _ : (i₂ : ι₀) → U.Init.Prelude.LE (π₁ i₂) ⦄ → U.Init.Prelude.LE ((i₂ : ι₀) → π₁ i₂)
Pi:hasLe {ι₀} {π₁} ⦃ inst₂ ⦄ = U.Init.Prelude.LE:mk {(i₃ : ι₀) → π₁ i₃} (λ (x₃ : (i₃ : ι₀) → π₁ i₃) → λ (y₄ : (i₄ : ι₀) → π₁ i₄) → (i₅ : ι₀) → U.Init.Prelude.LE:le {π₁ i₅} ⦃ inst₂ i₅ ⦄ (x₃ i₅) (y₄ i₅))
