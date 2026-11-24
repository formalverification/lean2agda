{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of OrderHom:map~ulfp
-- Lean module Mathlib.Order.SetNotation
module U.Mathlib.Order.SetNotation where
import U.Mathlib.Data.~sSet.Defs

record InfSet (α₀ : Set) : Set where
  constructor InfSet:mk
  field
    sInf₁ : U.Mathlib.Data.~sSet.Defs.~sSet α₀ → α₀

-- recursor
InfSet:rec : {α₀ : Set} → {motive₁ : InfSet α₀ → Set} → ((sInf₂ : U.Mathlib.Data.~sSet.Defs.~sSet α₀ → α₀) → motive₁ (InfSet:mk {α₀} sInf₂)) → (t₂ : InfSet α₀) → motive₁ t₂
InfSet:rec {α₀} {motive₁} mk₂ (InfSet:mk sInf₃) = mk₂ sInf₃

InfSet:sInf : {α₀ : Set} → ⦃ _ : InfSet α₀ ⦄ → U.Mathlib.Data.~sSet.Defs.~sSet α₀ → α₀
InfSet:sInf {α₀} ⦃ self₁ ⦄ = InfSet.sInf₁ {α₀} self₁

record SupSet (α₀ : Set) : Set where
  constructor SupSet:mk
  field
    sSup₁ : U.Mathlib.Data.~sSet.Defs.~sSet α₀ → α₀

-- recursor
SupSet:rec : {α₀ : Set} → {motive₁ : SupSet α₀ → Set} → ((sSup₂ : U.Mathlib.Data.~sSet.Defs.~sSet α₀ → α₀) → motive₁ (SupSet:mk {α₀} sSup₂)) → (t₂ : SupSet α₀) → motive₁ t₂
SupSet:rec {α₀} {motive₁} mk₂ (SupSet:mk sSup₃) = mk₂ sSup₃

SupSet:sSup : {α₀ : Set} → ⦃ _ : SupSet α₀ ⦄ → U.Mathlib.Data.~sSet.Defs.~sSet α₀ → α₀
SupSet:sSup {α₀} ⦃ self₁ ⦄ = SupSet.sSup₁ {α₀} self₁
