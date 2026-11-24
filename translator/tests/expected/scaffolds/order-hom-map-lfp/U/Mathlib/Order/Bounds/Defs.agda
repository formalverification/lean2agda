{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of OrderHom:map~ulfp
-- Lean module Mathlib.Order.Bounds.Defs
module U.Mathlib.Order.Bounds.Defs where
import U.Init.Prelude
import U.Mathlib.Data.~sSet.Defs

upperBounds : {α₀ : Set} → ⦃ _ : U.Init.Prelude.LE α₀ ⦄ → U.Mathlib.Data.~sSet.Defs.~sSet α₀ → U.Mathlib.Data.~sSet.Defs.~sSet α₀
upperBounds {α₀} ⦃ inst₁ ⦄ s₂ = U.Mathlib.Data.~sSet.Defs.~sSet:ofPred {α₀} (λ (x₃ : α₀) → {a₄ : α₀} → U.Init.Prelude.Membership:mem {α₀} {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instMembership {α₀} ⦄ s₂ a₄ → U.Init.Prelude.LE:le {α₀} ⦃ inst₁ ⦄ a₄ x₃)

IsGreatest : {α₀ : Set} → ⦃ _ : U.Init.Prelude.LE α₀ ⦄ → U.Mathlib.Data.~sSet.Defs.~sSet α₀ → α₀ → Set
IsGreatest {α₀} ⦃ inst₁ ⦄ s₂ a₃ = U.Init.Prelude.And (U.Init.Prelude.Membership:mem {α₀} {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instMembership {α₀} ⦄ s₂ a₃) (U.Init.Prelude.Membership:mem {α₀} {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instMembership {α₀} ⦄ (upperBounds {α₀} ⦃ inst₁ ⦄ s₂) a₃)

lowerBounds : {α₀ : Set} → ⦃ _ : U.Init.Prelude.LE α₀ ⦄ → U.Mathlib.Data.~sSet.Defs.~sSet α₀ → U.Mathlib.Data.~sSet.Defs.~sSet α₀
lowerBounds {α₀} ⦃ inst₁ ⦄ s₂ = U.Mathlib.Data.~sSet.Defs.~sSet:ofPred {α₀} (λ (x₃ : α₀) → {a₄ : α₀} → U.Init.Prelude.Membership:mem {α₀} {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instMembership {α₀} ⦄ s₂ a₄ → U.Init.Prelude.LE:le {α₀} ⦃ inst₁ ⦄ x₃ a₄)

IsGLB : {α₀ : Set} → ⦃ _ : U.Init.Prelude.LE α₀ ⦄ → U.Mathlib.Data.~sSet.Defs.~sSet α₀ → α₀ → Set
IsGLB {α₀} ⦃ inst₁ ⦄ s₂ = IsGreatest {α₀} ⦃ inst₁ ⦄ (lowerBounds {α₀} ⦃ inst₁ ⦄ s₂)

IsLeast : {α₀ : Set} → ⦃ _ : U.Init.Prelude.LE α₀ ⦄ → U.Mathlib.Data.~sSet.Defs.~sSet α₀ → α₀ → Set
IsLeast {α₀} ⦃ inst₁ ⦄ s₂ a₃ = U.Init.Prelude.And (U.Init.Prelude.Membership:mem {α₀} {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instMembership {α₀} ⦄ s₂ a₃) (U.Init.Prelude.Membership:mem {α₀} {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instMembership {α₀} ⦄ (lowerBounds {α₀} ⦃ inst₁ ⦄ s₂) a₃)

IsLUB : {α₀ : Set} → ⦃ _ : U.Init.Prelude.LE α₀ ⦄ → U.Mathlib.Data.~sSet.Defs.~sSet α₀ → α₀ → Set
IsLUB {α₀} ⦃ inst₁ ⦄ s₂ = IsLeast {α₀} ⦃ inst₁ ⦄ (upperBounds {α₀} ⦃ inst₁ ⦄ s₂)
