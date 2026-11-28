{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of Multiset:map~umap
-- Lean module Mathlib.Data.Multiset.MapFold
module U.Mathlib.Data.Multiset.MapFold where
import U.Batteries.Logic
import U.Init.Core
import U.Init.Data.List.Lemmas
import U.Init.Data.List.Perm
import U.Init.Prelude
import U.Mathlib.Data.Multiset.Defs

-- theorem
opaque
  Multiset:map:~uproof~u1 : {α₀ : Set} → {β₁ : Set} → (f₂ : α₀ → β₁) → (l₃ : U.Init.Prelude.List α₀) → (l₄ : U.Init.Prelude.List α₀) → U.Init.Core.Setoid:r {U.Init.Prelude.List α₀} ⦃ U.Init.Data.List.Perm.List:isSetoid α₀ ⦄ l₃ l₄ → U.Init.Prelude.Eq {U.Init.Prelude.Quot {U.Init.Prelude.List β₁} (U.Init.Core.Setoid:r {U.Init.Prelude.List β₁} ⦃ U.Init.Data.List.Perm.List:isSetoid β₁ ⦄)} (U.Init.Prelude.Quot:mk {U.Init.Prelude.List β₁} (U.Init.Core.Setoid:r {U.Init.Prelude.List β₁} ⦃ U.Init.Data.List.Perm.List:isSetoid β₁ ⦄) (U.Init.Prelude.List:map {α₀} {β₁} f₂ l₃)) (U.Init.Prelude.Quot:mk {U.Init.Prelude.List β₁} (U.Init.Core.Setoid:r {U.Init.Prelude.List β₁} ⦃ U.Init.Data.List.Perm.List:isSetoid β₁ ⦄) (U.Init.Prelude.List:map {α₀} {β₁} f₂ l₄))
  Multiset:map:~uproof~u1 {α₀} {β₁} f₂ l₃ l₄ p₅ = U.Init.Core.Quot:sound {U.Init.Prelude.List β₁} {U.Init.Core.Setoid:r {U.Init.Prelude.List β₁} ⦃ U.Init.Data.List.Perm.List:isSetoid β₁ ⦄} {U.Init.Prelude.List:map {α₀} {β₁} f₂ l₃} {U.Init.Prelude.List:map {α₀} {β₁} f₂ l₄} (U.Init.Data.List.Perm.List:Perm:map {α₀} {β₁} f₂ {l₃} {l₄} p₅)

Multiset:map : {α₀ : Set} → {β₁ : Set} → (α₀ → β₁) → U.Mathlib.Data.Multiset.Defs.Multiset α₀ → U.Mathlib.Data.Multiset.Defs.Multiset β₁
Multiset:map {α₀} {β₁} f₂ s₃ = U.Init.Core.Quot:liftOn {U.Init.Prelude.List α₀} {U.Mathlib.Data.Multiset.Defs.Multiset β₁} {U.Init.Core.Setoid:r {U.Init.Prelude.List α₀} ⦃ U.Init.Data.List.Perm.List:isSetoid α₀ ⦄} s₃ (λ (l₄ : U.Init.Prelude.List α₀) → U.Mathlib.Data.Multiset.Defs.Multiset:ofList {β₁} (U.Init.Prelude.List:map {α₀} {β₁} f₂ l₄)) (Multiset:map:~uproof~u1 {α₀} {β₁} f₂)

-- theorem
opaque
  Multiset:map~umap : {α₀ : Set} → {β₁ : Set} → {γ₂ : Set} → (g₃ : β₁ → γ₂) → (f₄ : α₀ → β₁) → (s₅ : U.Mathlib.Data.Multiset.Defs.Multiset α₀) → U.Init.Prelude.Eq {U.Mathlib.Data.Multiset.Defs.Multiset γ₂} (Multiset:map {β₁} {γ₂} g₃ (Multiset:map {α₀} {β₁} f₄ s₅)) (Multiset:map {α₀} {γ₂} (U.Init.Prelude.Function:comp {α₀} {β₁} {γ₂} g₃ f₄) s₅)
  Multiset:map~umap {α₀} {β₁} {γ₂} g₃ f₄ s₅ = U.Init.Core.Quot:inductionOn {U.Init.Prelude.List α₀} {U.Init.Core.Setoid:r {U.Init.Prelude.List α₀} ⦃ U.Init.Data.List.Perm.List:isSetoid α₀ ⦄} {λ (x₆ : U.Mathlib.Data.Multiset.Defs.Multiset α₀) → U.Init.Prelude.Eq {U.Mathlib.Data.Multiset.Defs.Multiset γ₂} (Multiset:map {β₁} {γ₂} g₃ (Multiset:map {α₀} {β₁} f₄ x₆)) (Multiset:map {α₀} {γ₂} (U.Init.Prelude.Function:comp {α₀} {β₁} {γ₂} g₃ f₄) x₆)} s₅ (λ (l₆ : U.Init.Prelude.List α₀) → U.Batteries.Logic.congr~uarg {U.Init.Prelude.List γ₂} {U.Mathlib.Data.Multiset.Defs.Multiset γ₂} {U.Init.Prelude.List:map {β₁} {γ₂} g₃ (U.Init.Prelude.List:map {α₀} {β₁} f₄ l₆)} {U.Init.Prelude.List:map {α₀} {γ₂} (U.Init.Prelude.Function:comp {α₀} {β₁} {γ₂} g₃ f₄) l₆} (U.Init.Prelude.Quot:mk {U.Init.Prelude.List γ₂} (U.Init.Core.Setoid:r {U.Init.Prelude.List γ₂} ⦃ U.Init.Data.List.Perm.List:isSetoid γ₂ ⦄)) (U.Init.Data.List.Lemmas.List:map~umap {β₁} {γ₂} {α₀} {g₃} {f₄} {l₆}))
