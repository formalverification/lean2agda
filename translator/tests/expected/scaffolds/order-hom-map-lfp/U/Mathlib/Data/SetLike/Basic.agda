{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of OrderHom:map~ulfp
-- Lean module Mathlib.Data.SetLike.Basic
module U.Mathlib.Data.SetLike.Basic where
import U.Init.Data.Function
import U.Init.Prelude
import U.Mathlib.Data.~sSet.Defs

record SetLike (A₀ : Set) (B₁ : U.Init.Prelude.outParam Set) : Set where
  constructor SetLike:mk
  field
    coe₂ : A₀ → U.Mathlib.Data.~sSet.Defs.~sSet B₁
    coeinjective₃ : U.Init.Data.Function.Function:Injective {A₀} {U.Mathlib.Data.~sSet.Defs.~sSet B₁} coe₂

-- recursor
SetLike:rec : {A₀ : Set} → {B₁ : Set} → {motive₂ : SetLike A₀ B₁ → Set} → ((coe₃ : A₀ → U.Mathlib.Data.~sSet.Defs.~sSet B₁) → (coeinjective₄ : U.Init.Data.Function.Function:Injective {A₀} {U.Mathlib.Data.~sSet.Defs.~sSet B₁} coe₃) → motive₂ (SetLike:mk {A₀} {B₁} coe₃ coeinjective₄)) → (t₃ : SetLike A₀ B₁) → motive₂ t₃
SetLike:rec {A₀} {B₁} {motive₂} mk₃ (SetLike:mk coe₄ coeinjective₅) = mk₃ coe₄ coeinjective₅

SetLike:coe : {A₀ : Set} → {B₁ : U.Init.Prelude.outParam Set} → ⦃ _ : SetLike A₀ B₁ ⦄ → A₀ → U.Mathlib.Data.~sSet.Defs.~sSet B₁
SetLike:coe {A₀} {B₁} ⦃ self₂ ⦄ = SetLike.coe₂ {A₀} {B₁} self₂
