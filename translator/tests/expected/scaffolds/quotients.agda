-- File: translator/tests/expected/scaffolds/quotients.agda
{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of QuotFixtures:eta~umk QuotFixtures:ind~umk QuotFixtures:over~umk QuotFixtures:succ QuotFixtures:succ~umk
module U.TranslatorTests.Input.Quotients where

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

-- theorem
opaque
  QuotFixtures:eta~umk : (f₀ : Nat → Nat) → Eq {Nat → Nat} (λ (x₁ : Nat) → Quot:lift {Nat → Nat} {Eq {Nat → Nat}} {Nat} (λ (g₂ : Nat → Nat) → g₂ x₁) (λ (x₂ : Nat → Nat) → λ (x₃ : Nat → Nat) → λ (h₄ : Eq {Nat → Nat} x₂ x₃) → congrArg {Nat → Nat} {Nat} {x₂} {x₃} (λ (g₅ : Nat → Nat) → g₅ x₁) h₄) (Quot:mk {Nat → Nat} (Eq {Nat → Nat}) f₀)) f₀
  QuotFixtures:eta~umk f₀ = rfl {Nat → Nat} {λ (x₁ : Nat) → Quot:lift {Nat → Nat} {Eq {Nat → Nat}} {Nat} (λ (g₂ : Nat → Nat) → g₂ x₁) (λ (x₂ : Nat → Nat) → λ (x₃ : Nat → Nat) → λ (h₄ : Eq {Nat → Nat} x₂ x₃) → congrArg {Nat → Nat} {Nat} {x₂} {x₃} (λ (g₅ : Nat → Nat) → g₅ x₁) h₄) (Quot:mk {Nat → Nat} (Eq {Nat → Nat}) f₀)}

-- theorem
opaque
  QuotFixtures:ind~umk : (n₀ : Nat) → Eq {Eq {Nat} n₀ n₀} (Quot:ind {Nat} {Eq {Nat}} {λ (x₁ : Quot {Nat} (Eq {Nat})) → Eq {Nat} n₀ n₀} (λ (x₁ : Nat) → rfl {Nat} {n₀}) (Quot:mk {Nat} (Eq {Nat}) n₀)) (rfl {Nat} {n₀})
  QuotFixtures:ind~umk n₀ = rfl {Eq {Nat} n₀ n₀} {Quot:ind {Nat} {Eq {Nat}} {λ (x₁ : Quot {Nat} (Eq {Nat})) → Eq {Nat} n₀ n₀} (λ (x₁ : Nat) → rfl {Nat} {n₀}) (Quot:mk {Nat} (Eq {Nat}) n₀)}

QuotFixtures:over~umk:~ushare:~n1 : Quot {Nat} (Eq {Nat}) → Nat → Nat
QuotFixtures:over~umk:~ushare:~n1 = Quot:lift {Nat} {Eq {Nat}} {Nat → Nat} (λ (a₀ : Nat) → λ (x₁ : Nat) → a₀) (λ (x₀ : Nat) → λ (x₁ : Nat) → λ (h₂ : Eq {Nat} x₀ x₁) → congrArg {Nat} {Nat → Nat} {x₀} {x₁} (λ (a₃ : Nat) → λ (x₄ : Nat) → a₃) h₂)

-- theorem
opaque
  QuotFixtures:over~umk : (n₀ : Nat) → (m₁ : Nat) → Eq {Nat} (QuotFixtures:over~umk:~ushare:~n1 (Quot:mk {Nat} (Eq {Nat}) n₀) m₁) n₀
  QuotFixtures:over~umk n₀ m₁ = rfl {Nat} {QuotFixtures:over~umk:~ushare:~n1 (Quot:mk {Nat} (Eq {Nat}) n₀) m₁}

QuotFixtures:succ : Quot {Nat} (Eq {Nat}) → Nat
QuotFixtures:succ q₀ = Quot:lift {Nat} {Eq {Nat}} {Nat} Nat:succ (λ (x₁ : Nat) → λ (x₂ : Nat) → λ (h₃ : Eq {Nat} x₁ x₂) → congrArg {Nat} {Nat} {x₁} {x₂} Nat:succ h₃) q₀

-- theorem
opaque
  QuotFixtures:succ~umk : (n₀ : Nat) → Eq {Nat} (QuotFixtures:succ (Quot:mk {Nat} (Eq {Nat}) n₀)) (Nat:succ n₀)
  QuotFixtures:succ~umk n₀ = rfl {Nat} {QuotFixtures:succ (Quot:mk {Nat} (Eq {Nat}) n₀)}
