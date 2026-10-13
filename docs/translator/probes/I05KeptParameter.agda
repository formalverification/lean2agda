-- Outcome on 2026-10-13 with Agda 2.8.0: rejected, [CannotApply] Eq:refl {α₀} has type Eq _a₁ _a₁, not a function type
{-# OPTIONS --type-in-type #-}
module I05KeptParameter where

-- Lean's promotion kept: a is a parameter, so Agda's constructor binds
-- it implicitly, and the printer's explicit argument is refused.
data Eq {α₀ : Set} (a₁ : α₀) : α₀ → Set where
  Eq:refl : Eq {α₀} a₁ a₁

rfl : {α₀ : Set} → {a₁ : α₀} → Eq {α₀} a₁ a₁
rfl {α₀} {a₁} = Eq:refl {α₀} a₁
