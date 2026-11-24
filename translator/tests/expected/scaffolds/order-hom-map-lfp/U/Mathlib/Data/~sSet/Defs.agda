{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of OrderHom:map~ulfp
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

~sSet:Nonempty : {α₀ : Set} → ~sSet α₀ → Set
~sSet:Nonempty {α₀} s₁ = U.Init.Core.Exists {α₀} (λ (x₂ : α₀) → U.Init.Prelude.Membership:mem {α₀} {~sSet α₀} ⦃ ~sSet:instMembership {α₀} ⦄ s₁ x₂)

~sSet:ofPred : {α₀ : Set} → (α₀ → Set) → ~sSet α₀
~sSet:ofPred {α₀} p₁ = p₁

-- theorem
opaque
  ~sSet:ext : {α₀ : Set} → {a₁ : ~sSet α₀} → {b₂ : ~sSet α₀} → ((x₃ : α₀) → U.Init.Core.Iff (U.Init.Prelude.Membership:mem {α₀} {~sSet α₀} ⦃ ~sSet:instMembership {α₀} ⦄ a₁ x₃) (U.Init.Prelude.Membership:mem {α₀} {~sSet α₀} ⦃ ~sSet:instMembership {α₀} ⦄ b₂ x₃)) → U.Init.Prelude.Eq {~sSet α₀} a₁ b₂
  ~sSet:ext {α₀} {a₁} {b₂} h₃ = U.Init.Core.funext {α₀} {λ (x₄ : α₀) → Set} {a₁} {b₂} (λ (x₄ : α₀) → U.Init.Core.propext {a₁ x₄} {b₂ x₄} (h₃ x₄))

~sSet:Subset : {α₀ : Set} → ~sSet α₀ → ~sSet α₀ → Set
~sSet:Subset {α₀} s₁ s₂ = {a₃ : α₀} → U.Init.Prelude.Membership:mem {α₀} {~sSet α₀} ⦃ ~sSet:instMembership {α₀} ⦄ s₁ a₃ → U.Init.Prelude.Membership:mem {α₀} {~sSet α₀} ⦃ ~sSet:instMembership {α₀} ⦄ s₂ a₃

~sSet:instLE : {α₀ : Set} → U.Init.Prelude.LE (~sSet α₀)
~sSet:instLE {α₀} = U.Init.Prelude.LE:mk {~sSet α₀} (~sSet:Subset {α₀})
