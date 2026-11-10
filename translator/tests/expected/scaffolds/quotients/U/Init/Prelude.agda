{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of QuotFixtures:eta~umk QuotFixtures:ind~umk QuotFixtures:over~umk QuotFixtures:succ QuotFixtures:succ~umk
-- Lean module Init.Prelude
module U.Init.Prelude where

data Eq {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁
{-# BUILTIN REWRITE Eq #-}

postulate Eq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq {α₀} a₁ a₂ → Set} → motive₂ a₁ (Eq:refl {α₀} a₁) → {a₃ : α₀} → (t₄ : Eq {α₀} a₁ a₃) → motive₂ a₃ t₄

data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

postulate Nat:rec : {motive₀ : Nat → Set} → motive₀ Nat:zero → ((n₁ : Nat) → motive₀ n₁ → motive₀ (Nat:succ n₁)) → (t₁ : Nat) → motive₀ t₁

postulate Quot : {α₀ : Set} → (α₀ → α₀ → Set) → Set

postulate Quot:mk : {α₀ : Set} → (r₁ : α₀ → α₀ → Set) → α₀ → Quot {α₀} r₁

postulate Quot:ind : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {β₂ : Quot {α₀} r₁ → Set} → ((a₃ : α₀) → β₂ (Quot:mk {α₀} r₁ a₃)) → (q₃ : Quot {α₀} r₁) → β₂ q₃

-- computation rule
postulate Quot:ind-β : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {β₂ : Quot {α₀} r₁ → Set} → (mk₃ : (a₃ : α₀) → β₂ (Quot:mk {α₀} r₁ a₃)) → (a₄ : α₀) → Eq {β₂ (Quot:mk {α₀} r₁ a₄)} (Quot:ind {α₀} {r₁} {β₂} mk₃ (Quot:mk {α₀} r₁ a₄)) (mk₃ a₄)
{-# REWRITE Quot:ind-β #-}

postulate Quot:lift : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {β₂ : Set} → (f₃ : α₀ → β₂) → ((a₄ : α₀) → (b₅ : α₀) → r₁ a₄ b₅ → Eq {β₂} (f₃ a₄) (f₃ b₅)) → Quot {α₀} r₁ → β₂

-- computation rule
postulate Quot:lift-β : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {β₂ : Set} → (f₃ : α₀ → β₂) → (h₄ : (a₄ : α₀) → (b₅ : α₀) → r₁ a₄ b₅ → Eq {β₂} (f₃ a₄) (f₃ b₅)) → (a₅ : α₀) → Eq {β₂} (Quot:lift {α₀} {r₁} {β₂} f₃ h₄ (Quot:mk {α₀} r₁ a₅)) (f₃ a₅)
{-# REWRITE Quot:lift-β #-}

rfl : {α₀ : Set} → {a₁ : α₀} → Eq {α₀} a₁ a₁
rfl {α₀} {a₁} = Eq:refl {α₀} a₁

-- theorem
opaque
  congrArg : {α₀ : Set} → {β₁ : Set} → {a₂ : α₀} → {a₃ : α₀} → (f₄ : α₀ → β₁) → Eq {α₀} a₂ a₃ → Eq {β₁} (f₄ a₂) (f₄ a₃)
  congrArg {α₀} {β₁} {a₂} {a₃} f₄ h₅ = Eq:rec {α₀} {a₂} {λ (x₆ : α₀) → λ (h₇ : Eq {α₀} a₂ x₆) → Eq {β₁} (f₄ a₂) (f₄ x₆)} (rfl {β₁} {f₄ a₂}) {a₃} h₅
