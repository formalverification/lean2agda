{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of OrderHom:map~ulfp
-- Lean module Mathlib.Order.Notation
module U.Mathlib.Order.Notation where

record Bot (α₀ : Set) : Set where
  constructor Bot:mk
  field
    bot₁ : α₀

-- recursor
Bot:rec : {α₀ : Set} → {motive₁ : Bot α₀ → Set} → ((bot₂ : α₀) → motive₁ (Bot:mk {α₀} bot₂)) → (t₂ : Bot α₀) → motive₁ t₂
Bot:rec {α₀} {motive₁} mk₂ (Bot:mk bot₃) = mk₂ bot₃

Bot:bot : {α₀ : Set} → ⦃ _ : Bot α₀ ⦄ → α₀
Bot:bot {α₀} ⦃ self₁ ⦄ = Bot.bot₁ {α₀} self₁

record Top (α₀ : Set) : Set where
  constructor Top:mk
  field
    top₁ : α₀

-- recursor
Top:rec : {α₀ : Set} → {motive₁ : Top α₀ → Set} → ((top₂ : α₀) → motive₁ (Top:mk {α₀} top₂)) → (t₂ : Top α₀) → motive₁ t₂
Top:rec {α₀} {motive₁} mk₂ (Top:mk top₃) = mk₂ top₃

Top:top : {α₀ : Set} → ⦃ _ : Top α₀ ⦄ → α₀
Top:top {α₀} ⦃ self₁ ⦄ = Top.top₁ {α₀} self₁
