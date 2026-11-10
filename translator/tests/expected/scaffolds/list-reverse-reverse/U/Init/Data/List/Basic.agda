{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of List:reverse~ureverse
-- Lean module Init.Data.List.Basic
module U.Init.Data.List.Basic where
import U.Init.Prelude

List:reverseAux:match~u1 : {α₀ : Set} → (motive₁ : U.Init.Prelude.List α₀ → U.Init.Prelude.List α₀ → Set) → (x₂ : U.Init.Prelude.List α₀) → (x₃ : U.Init.Prelude.List α₀) → ((r₄ : U.Init.Prelude.List α₀) → motive₁ (U.Init.Prelude.List:nil {α₀}) r₄) → ((a₄ : α₀) → (l₅ : U.Init.Prelude.List α₀) → (r₆ : U.Init.Prelude.List α₀) → motive₁ (U.Init.Prelude.List:cons {α₀} a₄ l₅) r₆) → motive₁ x₂ x₃
List:reverseAux:match~u1 {α₀} motive₁ x₂ x₃ h1₄ h2₅ = U.Init.Prelude.List:casesOn {α₀} {λ (x₆ : U.Init.Prelude.List α₀) → motive₁ x₆ x₃} x₂ (h1₄ x₃) (λ (head₆ : α₀) → λ (tail₇ : U.Init.Prelude.List α₀) → h2₅ head₆ tail₇ x₃)

List:reverseAux:~uf : {α₀ : Set} → (x₁ : U.Init.Prelude.List α₀) → U.Init.Prelude.List:below {α₀} {λ (x₂ : U.Init.Prelude.List α₀) → U.Init.Prelude.List α₀ → U.Init.Prelude.List α₀} x₁ → U.Init.Prelude.List α₀ → U.Init.Prelude.List α₀
List:reverseAux:~uf {α₀} x₁ f₂ x₃ = List:reverseAux:match~u1 {α₀} (λ (x₄ : U.Init.Prelude.List α₀) → λ (x₅ : U.Init.Prelude.List α₀) → U.Init.Prelude.List:below {α₀} {λ (x₆ : U.Init.Prelude.List α₀) → U.Init.Prelude.List α₀ → U.Init.Prelude.List α₀} x₄ → U.Init.Prelude.List α₀) x₁ x₃ (λ (r₄ : U.Init.Prelude.List α₀) → λ (x₅ : U.Init.Prelude.List:below {α₀} {λ (x₅ : U.Init.Prelude.List α₀) → U.Init.Prelude.List α₀ → U.Init.Prelude.List α₀} (U.Init.Prelude.List:nil {α₀})) → r₄) (λ (a₄ : α₀) → λ (l₅ : U.Init.Prelude.List α₀) → λ (r₆ : U.Init.Prelude.List α₀) → λ (x₇ : U.Init.Prelude.List:below {α₀} {λ (x₇ : U.Init.Prelude.List α₀) → U.Init.Prelude.List α₀ → U.Init.Prelude.List α₀} (U.Init.Prelude.List:cons {α₀} a₄ l₅)) → U.Init.Prelude.PProd.fst₂ {(λ (x₈ : U.Init.Prelude.List α₀) → U.Init.Prelude.List α₀ → U.Init.Prelude.List α₀) l₅} {U.Init.Prelude.List:rec {α₀} {λ (t₈ : U.Init.Prelude.List α₀) → Set} U.Init.Prelude.PUnit (λ (head₈ : α₀) → λ (tail₉ : U.Init.Prelude.List α₀) → λ (tailih₁₀ : Set) → U.Init.Prelude.PProd ((λ (x₁₁ : U.Init.Prelude.List α₀) → U.Init.Prelude.List α₀ → U.Init.Prelude.List α₀) tail₉) tailih₁₀) l₅} x₇ (U.Init.Prelude.List:cons {α₀} a₄ r₆)) f₂

List:reverseAux : {α₀ : Set} → U.Init.Prelude.List α₀ → U.Init.Prelude.List α₀ → U.Init.Prelude.List α₀
List:reverseAux {α₀} x₁ x₂ = U.Init.Prelude.List:brecOn {α₀} {λ (x₃ : U.Init.Prelude.List α₀) → U.Init.Prelude.List α₀ → U.Init.Prelude.List α₀} x₁ (List:reverseAux:~uf {α₀}) x₂

List:reverse : {α₀ : Set} → U.Init.Prelude.List α₀ → U.Init.Prelude.List α₀
List:reverse {α₀} as₁ = List:reverseAux {α₀} as₁ (U.Init.Prelude.List:nil {α₀})
