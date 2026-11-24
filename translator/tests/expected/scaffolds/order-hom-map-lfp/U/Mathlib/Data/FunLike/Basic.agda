{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of OrderHom:map~ulfp
-- Lean module Mathlib.Data.FunLike.Basic
module U.Mathlib.Data.FunLike.Basic where
import U.Init.Data.Function
import U.Init.Prelude

record DFunLike (F₀ : Set) (α₁ : U.Init.Prelude.outParam Set) (β₂ : U.Init.Prelude.outParam (α₁ → Set)) : Set where
  constructor DFunLike:mk
  field
    coe₃ : F₀ → (a₃ : α₁) → β₂ a₃
    coeinjective₄ : U.Init.Data.Function.Function:Injective {F₀} {(a₄ : α₁) → β₂ a₄} coe₃

-- recursor
DFunLike:rec : {F₀ : Set} → {α₁ : Set} → {β₂ : α₁ → Set} → {motive₃ : DFunLike F₀ α₁ β₂ → Set} → ((coe₄ : F₀ → (a₄ : α₁) → β₂ a₄) → (coeinjective₅ : U.Init.Data.Function.Function:Injective {F₀} {(a₅ : α₁) → β₂ a₅} coe₄) → motive₃ (DFunLike:mk {F₀} {α₁} {β₂} coe₄ coeinjective₅)) → (t₄ : DFunLike F₀ α₁ β₂) → motive₃ t₄
DFunLike:rec {F₀} {α₁} {β₂} {motive₃} mk₄ (DFunLike:mk coe₅ coeinjective₆) = mk₄ coe₅ coeinjective₆

DFunLike:coe : {F₀ : Set} → {α₁ : U.Init.Prelude.outParam Set} → {β₂ : U.Init.Prelude.outParam (α₁ → Set)} → ⦃ _ : DFunLike F₀ α₁ β₂ ⦄ → F₀ → (a₃ : α₁) → β₂ a₃
DFunLike:coe {F₀} {α₁} {β₂} ⦃ self₃ ⦄ = DFunLike.coe₃ {F₀} {α₁} {β₂} self₃

FunLike : Set → Set → Set → Set
FunLike F₀ α₁ β₂ = DFunLike F₀ α₁ (λ (x₃ : α₁) → β₂)
