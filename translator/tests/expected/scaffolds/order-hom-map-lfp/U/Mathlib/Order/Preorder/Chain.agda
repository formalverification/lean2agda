{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of OrderHom:map~ulfp
-- Lean module Mathlib.Order.Preorder.Chain
module U.Mathlib.Order.Preorder.Chain where
import U.Init.Prelude
import U.Mathlib.Data.~sSet.Defs
import U.Mathlib.Logic.Pairwise

IsChain : {α₀ : Set} → (α₀ → α₀ → Set) → U.Mathlib.Data.~sSet.Defs.~sSet α₀ → Set
IsChain {α₀} r₁ s₂ = U.Mathlib.Logic.Pairwise.~sSet:Pairwise {α₀} s₂ (λ (x₃ : α₀) → λ (y₄ : α₀) → U.Init.Prelude.Or (r₁ x₃ y₄) (r₁ y₄ x₃))
