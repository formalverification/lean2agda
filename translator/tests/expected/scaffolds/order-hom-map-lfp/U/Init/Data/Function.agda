{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of OrderHom:map~ulfp
-- Lean module Init.Data.Function
module U.Init.Data.Function where
import U.Init.Prelude

Function:Injective : {α₀ : Set} → {β₁ : Set} → (α₀ → β₁) → Set
Function:Injective {α₀} {β₁} f₂ = {a₃ : α₀} → {a₄ : α₀} → U.Init.Prelude.Eq {β₁} (f₂ a₃) (f₂ a₄) → U.Init.Prelude.Eq {α₀} a₃ a₄
