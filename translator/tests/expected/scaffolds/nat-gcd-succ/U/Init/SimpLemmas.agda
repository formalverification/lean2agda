{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of Nat:gcd~usucc
-- Lean module Init.SimpLemmas
module U.Init.SimpLemmas where
import U.Init.Prelude

-- theorem
opaque
  ite~uself : {α₀ : Set} → {c₁ : Set} → {d₂ : U.Init.Prelude.Decidable c₁} → (a₃ : α₀) → U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} c₁ ⦃ d₂ ⦄ a₃ a₃) a₃
  ite~uself {α₀} {c₁} {d₂} a₃ = U.Init.Prelude.Decidable:casesOn {c₁} {λ (t₄ : U.Init.Prelude.Decidable c₁) → U.Init.Prelude.Eq {U.Init.Prelude.Decidable c₁} d₂ t₄ → U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} c₁ ⦃ d₂ ⦄ a₃ a₃) a₃} d₂ (λ (h₄ : U.Init.Prelude.Not c₁) → λ (h₅ : U.Init.Prelude.Eq {U.Init.Prelude.Decidable c₁} d₂ (U.Init.Prelude.Decidable:isFalse {c₁} h₄)) → U.Init.Prelude.Eq:ndrec {U.Init.Prelude.Decidable c₁} {U.Init.Prelude.Decidable:isFalse {c₁} h₄} {λ (d₆ : U.Init.Prelude.Decidable c₁) → U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} c₁ ⦃ d₆ ⦄ a₃ a₃) a₃} (U.Init.Prelude.Eq:refl {α₀} (U.Init.Prelude.ite {α₀} c₁ ⦃ U.Init.Prelude.Decidable:isFalse {c₁} h₄ ⦄ a₃ a₃)) {d₂} (U.Init.Prelude.Eq:symm {U.Init.Prelude.Decidable c₁} {d₂} {U.Init.Prelude.Decidable:isFalse {c₁} h₄} h₅)) (λ (h₄ : c₁) → λ (h₅ : U.Init.Prelude.Eq {U.Init.Prelude.Decidable c₁} d₂ (U.Init.Prelude.Decidable:isTrue {c₁} h₄)) → U.Init.Prelude.Eq:ndrec {U.Init.Prelude.Decidable c₁} {U.Init.Prelude.Decidable:isTrue {c₁} h₄} {λ (d₆ : U.Init.Prelude.Decidable c₁) → U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} c₁ ⦃ d₆ ⦄ a₃ a₃) a₃} (U.Init.Prelude.Eq:refl {α₀} (U.Init.Prelude.ite {α₀} c₁ ⦃ U.Init.Prelude.Decidable:isTrue {c₁} h₄ ⦄ a₃ a₃)) {d₂} (U.Init.Prelude.Eq:symm {U.Init.Prelude.Decidable c₁} {d₂} {U.Init.Prelude.Decidable:isTrue {c₁} h₄} h₅)) (U.Init.Prelude.Eq:refl {U.Init.Prelude.Decidable c₁} d₂)
