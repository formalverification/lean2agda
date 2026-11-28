{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of OrderHom:map~ulfp
-- Lean module Mathlib.Logic.Pairwise
module U.Mathlib.Logic.Pairwise where
import U.Init.Core
import U.Init.Prelude
import U.Mathlib.Data.~sSet.Defs

~sSet:Pairwise : {α₀ : Set} → U.Mathlib.Data.~sSet.Defs.~sSet α₀ → (α₀ → α₀ → Set) → Set
~sSet:Pairwise {α₀} s₁ r₂ = {x₃ : α₀} → U.Init.Prelude.Membership:mem {α₀} {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instMembership {α₀} ⦄ s₁ x₃ → {y₄ : α₀} → U.Init.Prelude.Membership:mem {α₀} {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instMembership {α₀} ⦄ s₁ y₄ → U.Init.Core.Ne {α₀} x₃ y₄ → r₂ x₃ y₄
