{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of ~sSet:ext
-- Lean module Init.Prelude
module U.Init.Prelude where

data Eq {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁
{-# BUILTIN REWRITE Eq #-}

-- recursor
Eq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq {α₀} a₁ a₂ → Set} → motive₂ a₁ (Eq:refl {α₀} a₁) → {a₃ : α₀} → (t₄ : Eq {α₀} a₁ a₃) → motive₂ a₃ t₄
Eq:rec {α₀} {a₁} {motive₂} refl₃ {_} (Eq:refl _) = refl₃

outParam : Set → Set
outParam α₀ = α₀

record Membership (α₀ : outParam Set) (γ₁ : Set) : Set where
  constructor Membership:mk
  field
    mem₂ : γ₁ → α₀ → Set

-- recursor
Membership:rec : {α₀ : Set} → {γ₁ : Set} → {motive₂ : Membership α₀ γ₁ → Set} → ((mem₃ : γ₁ → α₀ → Set) → motive₂ (Membership:mk {α₀} {γ₁} mem₃)) → (t₃ : Membership α₀ γ₁) → motive₂ t₃
Membership:rec {α₀} {γ₁} {motive₂} mk₃ (Membership:mk mem₄) = mk₃ mem₄

Membership:mem : {α₀ : outParam Set} → {γ₁ : Set} → ⦃ _ : Membership α₀ γ₁ ⦄ → γ₁ → α₀ → Set
Membership:mem {α₀} {γ₁} ⦃ self₂ ⦄ = Membership.mem₂ {α₀} {γ₁} self₂

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

id : {α₀ : Set} → α₀ → α₀
id {α₀} a₁ = a₁
