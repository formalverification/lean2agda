-- Outcome on 2026-10-13 with Agda 2.8.0: accepted
{-# OPTIONS --type-in-type #-}
module R01Promoted where

-- Eq and HEq with Lean's promoted parameter `a` an Agda index.  The
-- recursor binds `a` as a variable pattern, Lean's parameter, and the
-- constructor's argument and the indices as `_`, which Agda's unifier
-- fills in (K is on, as Agda's default).
data Eq {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁

Eq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq {α₀} a₁ a₂ → Set} → motive₂ a₁ (Eq:refl {α₀} a₁) → {a₃ : α₀} → (t₄ : Eq {α₀} a₁ a₃) → motive₂ a₃ t₄
Eq:rec {α₀} {a₁} {motive₂} refl₃ {_} (Eq:refl _) = refl₃

data HEq {α₀ : Set} : α₀ → {β₂ : Set} → β₂ → Set where
  HEq:refl : (a₁ : α₀) → HEq {α₀} a₁ {α₀} a₁

HEq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : {β₂ : Set} → (a₃ : β₂) → HEq {α₀} a₁ {β₂} a₃ → Set} → motive₂ {α₀} a₁ (HEq:refl {α₀} a₁) → {β₃ : Set} → {a₄ : β₃} → (t₅ : HEq {α₀} a₁ {β₃} a₄) → motive₂ {β₃} a₄ t₅
HEq:rec {α₀} {a₁} {motive₂} refl₃ {_} {_} (HEq:refl _) = refl₃

data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

-- Iota on a closed proof.
iota : (P : Nat → Set) → (p : P 3) → Eq {P 3} (Eq:rec {Nat} {3} {λ x _ → P x} p {3} (Eq:refl 3)) p
iota P p = Eq:refl p
