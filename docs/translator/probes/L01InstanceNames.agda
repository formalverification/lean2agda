-- Outcome on 2026-11-24 with Agda 2.8.0: accepted
{-# OPTIONS --type-in-type --rewriting #-}
module L01InstanceNames where

-- An instance's identifier is its constant's followed by `#` and one
-- letter per split level parameter, `z` for zero and `n` for nonzero
-- (docs/translator/levels.md).  Agda reads `#` as a name character: the
-- identifiers below lex as one name each, also after a module path, in a
-- pattern, before the suffix `-β` of a computation rule, and inside a
-- pragma, whose closing `#-}` is a token of its own.
data Eq#n {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl#n : (a₁ : α₀) → Eq#n {α₀} a₁ a₁
{-# BUILTIN REWRITE Eq#n #-}

Eq:rec#nn : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq#n {α₀} a₁ a₂ → Set} → motive₂ a₁ (Eq:refl#n {α₀} a₁) → {a₃ : α₀} → (t₄ : Eq#n {α₀} a₁ a₃) → motive₂ a₃ t₄
Eq:rec#nn {α₀} {a₁} {motive₂} refl₃ {_} (Eq:refl#n _) = refl₃

postulate Quot#n : {α₀ : Set} → (α₀ → α₀ → Set) → Set
postulate Quot:mk#n : {α₀ : Set} → (r₁ : α₀ → α₀ → Set) → α₀ → Quot#n {α₀} r₁
postulate Quot:lift#nn : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {β₂ : Set} → (f₃ : α₀ → β₂) → ((a₄ : α₀) → (b₅ : α₀) → r₁ a₄ b₅ → Eq#n {β₂} (f₃ a₄) (f₃ b₅)) → Quot#n {α₀} r₁ → β₂
postulate Quot:lift#nn-β : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {β₂ : Set} → (f₃ : α₀ → β₂) → (h₄ : (a₄ : α₀) → (b₅ : α₀) → r₁ a₄ b₅ → Eq#n {β₂} (f₃ a₄) (f₃ b₅)) → (a₅ : α₀) → Eq#n {β₂} (Quot:lift#nn {α₀} {r₁} {β₂} f₃ h₄ (Quot:mk#n {α₀} r₁ a₅)) (f₃ a₅)
{-# REWRITE Quot:lift#nn-β #-}

module Inner where
  postulate Unit#z : Set
  postulate Unit:unit#z : Unit#z

use : Inner.Unit#z
use = Inner.Unit:unit#z
