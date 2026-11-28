{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of ~sSet:ext
-- Lean module Mathlib.Data.Set.Defs
module U.Mathlib.Data.~sSet.Defs where
import U.Init.Core
import U.Init.Prelude

~sSet : Set → Set
~sSet α₀ = α₀ → Set

~sSet:Mem : {α₀ : Set} → ~sSet α₀ → α₀ → Set
~sSet:Mem {α₀} s₁ a₂ = s₁ a₂

~sSet:instMembership : {α₀ : Set} → U.Init.Prelude.Membership α₀ (~sSet α₀)
~sSet:instMembership {α₀} = U.Init.Prelude.Membership:mk {α₀} {~sSet α₀} (~sSet:Mem {α₀})

-- theorem
opaque
  ~sSet:ext : {α₀ : Set} → {a₁ : ~sSet α₀} → {b₂ : ~sSet α₀} → ((x₃ : α₀) → U.Init.Core.Iff (U.Init.Prelude.Membership:mem {α₀} {~sSet α₀} ⦃ ~sSet:instMembership {α₀} ⦄ a₁ x₃) (U.Init.Prelude.Membership:mem {α₀} {~sSet α₀} ⦃ ~sSet:instMembership {α₀} ⦄ b₂ x₃)) → U.Init.Prelude.Eq {~sSet α₀} a₁ b₂
  ~sSet:ext {α₀} {a₁} {b₂} h₃ = U.Init.Core.funext {α₀} {λ (x₄ : α₀) → Set} {a₁} {b₂} (λ (x₄ : α₀) → U.Init.Core.propext {a₁ x₄} {b₂ x₄} (h₃ x₄))
