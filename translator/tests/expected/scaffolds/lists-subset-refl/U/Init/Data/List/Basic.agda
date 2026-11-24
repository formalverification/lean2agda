{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of Lists~x27~:Subset:refl
-- Lean module Init.Data.List.Basic
module U.Init.Data.List.Basic where
import U.Init.Core
import U.Init.Prelude

data List:Mem {α₀ : Set} (a₁ : α₀) : U.Init.Prelude.List α₀ → Set where
  List:Mem:head : (as₂ : U.Init.Prelude.List α₀) → List:Mem {α₀} a₁ (U.Init.Prelude.List:cons {α₀} a₁ as₂)
  List:Mem:tail : (b₂ : α₀) → {as₃ : U.Init.Prelude.List α₀} → List:Mem {α₀} a₁ as₃ → List:Mem {α₀} a₁ (U.Init.Prelude.List:cons {α₀} b₂ as₃)

-- recursor
List:Mem:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : U.Init.Prelude.List α₀) → List:Mem {α₀} a₁ a₂ → Set} → ((as₃ : U.Init.Prelude.List α₀) → motive₂ (U.Init.Prelude.List:cons {α₀} a₁ as₃) (List:Mem:head {α₀} {a₁} as₃)) → ((b₃ : α₀) → {as₄ : U.Init.Prelude.List α₀} → (a₅ : List:Mem {α₀} a₁ as₄) → motive₂ as₄ a₅ → motive₂ (U.Init.Prelude.List:cons {α₀} b₃ as₄) (List:Mem:tail {α₀} {a₁} b₃ {as₄} a₅)) → {a₃ : U.Init.Prelude.List α₀} → (t₄ : List:Mem {α₀} a₁ a₃) → motive₂ a₃ t₄
List:Mem:rec {α₀} {a₁} {motive₂} head₃ tail₄ {_} (List:Mem:head as₆) = head₃ as₆
List:Mem:rec {α₀} {a₁} {motive₂} head₃ tail₄ {_} (List:Mem:tail b₆ {as₇} a₈) = tail₄ b₆ {as₇} a₈ (List:Mem:rec {α₀} {a₁} {motive₂} head₃ tail₄ {as₇} a₈)

List:Mem:casesOn : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : U.Init.Prelude.List α₀) → List:Mem {α₀} a₁ a₂ → Set} → {a₃ : U.Init.Prelude.List α₀} → (t₄ : List:Mem {α₀} a₁ a₃) → ((as₅ : U.Init.Prelude.List α₀) → motive₂ (U.Init.Prelude.List:cons {α₀} a₁ as₅) (List:Mem:head {α₀} {a₁} as₅)) → ((b₅ : α₀) → {as₆ : U.Init.Prelude.List α₀} → (a₇ : List:Mem {α₀} a₁ as₆) → motive₂ (U.Init.Prelude.List:cons {α₀} b₅ as₆) (List:Mem:tail {α₀} {a₁} b₅ {as₆} a₇)) → motive₂ a₃ t₄
List:Mem:casesOn {α₀} {a₁} {motive₂} {a₃} t₄ head₅ tail₆ = List:Mem:rec {α₀} {a₁} {motive₂} (λ (as₇ : U.Init.Prelude.List α₀) → head₅ as₇) (λ (b₇ : α₀) → λ {as₈ : U.Init.Prelude.List α₀} → λ (a₉ : List:Mem {α₀} a₁ as₈) → λ (aih₁₀ : motive₂ as₈ a₉) → tail₆ b₇ {as₈} a₉) {a₃} t₄

List:instMembership : {α₀ : Set} → U.Init.Prelude.Membership α₀ (U.Init.Prelude.List α₀)
List:instMembership {α₀} = U.Init.Prelude.Membership:mk {α₀} {U.Init.Prelude.List α₀} (λ (l₁ : U.Init.Prelude.List α₀) → λ (a₂ : α₀) → List:Mem {α₀} a₂ l₁)

List:Subset : {α₀ : Set} → U.Init.Prelude.List α₀ → U.Init.Prelude.List α₀ → Set
List:Subset {α₀} l₁ l₂ = {a₃ : α₀} → U.Init.Prelude.Membership:mem {α₀} {U.Init.Prelude.List α₀} ⦃ List:instMembership {α₀} ⦄ l₁ a₃ → U.Init.Prelude.Membership:mem {α₀} {U.Init.Prelude.List α₀} ⦃ List:instMembership {α₀} ⦄ l₂ a₃

List:instHasSubset : {α₀ : Set} → U.Init.Core.HasSubset (U.Init.Prelude.List α₀)
List:instHasSubset {α₀} = U.Init.Core.HasSubset:mk {U.Init.Prelude.List α₀} (List:Subset {α₀})
