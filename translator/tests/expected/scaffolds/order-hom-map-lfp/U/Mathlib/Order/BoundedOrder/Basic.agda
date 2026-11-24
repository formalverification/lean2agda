{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of OrderHom:map~ulfp
-- Lean module Mathlib.Order.BoundedOrder.Basic
module U.Mathlib.Order.BoundedOrder.Basic where
import U.Init.Prelude
import U.Mathlib.Order.Notation

record OrderBot (α₀ : Set) ⦃ inst₁ : U.Init.Prelude.LE α₀ ⦄ : Set where
  constructor OrderBot:mk
  field
    ⦃ toBot₂ ⦄ : U.Mathlib.Order.Notation.Bot α₀
    botle₃ : (a₃ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ inst₁ ⦄ (U.Mathlib.Order.Notation.Bot:bot {α₀} ⦃ toBot₂ ⦄) a₃

-- recursor
OrderBot:rec : {α₀ : Set} → ⦃ inst₁ : U.Init.Prelude.LE α₀ ⦄ → {motive₂ : OrderBot α₀ ⦃ inst₁ ⦄ → Set} → (⦃ toBot₃ : U.Mathlib.Order.Notation.Bot α₀ ⦄ → (botle₄ : (a₄ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ inst₁ ⦄ (U.Mathlib.Order.Notation.Bot:bot {α₀} ⦃ toBot₃ ⦄) a₄) → motive₂ (OrderBot:mk {α₀} ⦃ inst₁ ⦄ ⦃ toBot₃ ⦄ botle₄)) → (t₃ : OrderBot α₀ ⦃ inst₁ ⦄) → motive₂ t₃
OrderBot:rec {α₀} ⦃ inst₁ ⦄ {motive₂} mk₃ (OrderBot:mk ⦃ toBot₄ ⦄ botle₅) = mk₃ ⦃ toBot₄ ⦄ botle₅

record OrderTop (α₀ : Set) ⦃ inst₁ : U.Init.Prelude.LE α₀ ⦄ : Set where
  constructor OrderTop:mk
  field
    ⦃ toTop₂ ⦄ : U.Mathlib.Order.Notation.Top α₀
    letop₃ : (a₃ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ inst₁ ⦄ a₃ (U.Mathlib.Order.Notation.Top:top {α₀} ⦃ toTop₂ ⦄)

-- recursor
OrderTop:rec : {α₀ : Set} → ⦃ inst₁ : U.Init.Prelude.LE α₀ ⦄ → {motive₂ : OrderTop α₀ ⦃ inst₁ ⦄ → Set} → (⦃ toTop₃ : U.Mathlib.Order.Notation.Top α₀ ⦄ → (letop₄ : (a₄ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ inst₁ ⦄ a₄ (U.Mathlib.Order.Notation.Top:top {α₀} ⦃ toTop₃ ⦄)) → motive₂ (OrderTop:mk {α₀} ⦃ inst₁ ⦄ ⦃ toTop₃ ⦄ letop₄)) → (t₃ : OrderTop α₀ ⦃ inst₁ ⦄) → motive₂ t₃
OrderTop:rec {α₀} ⦃ inst₁ ⦄ {motive₂} mk₃ (OrderTop:mk ⦃ toTop₄ ⦄ letop₅) = mk₃ ⦃ toTop₄ ⦄ letop₅

record BoundedOrder (α₀ : Set) ⦃ inst₁ : U.Init.Prelude.LE α₀ ⦄ : Set where
  constructor BoundedOrder:mk
  field
    ⦃ toOrderTop₂ ⦄ : OrderTop α₀ ⦃ inst₁ ⦄
    ⦃ toOrderBot₃ ⦄ : OrderBot α₀ ⦃ inst₁ ⦄

-- recursor
BoundedOrder:rec : {α₀ : Set} → ⦃ inst₁ : U.Init.Prelude.LE α₀ ⦄ → {motive₂ : BoundedOrder α₀ ⦃ inst₁ ⦄ → Set} → (⦃ toOrderTop₃ : OrderTop α₀ ⦃ inst₁ ⦄ ⦄ → ⦃ toOrderBot₄ : OrderBot α₀ ⦃ inst₁ ⦄ ⦄ → motive₂ (BoundedOrder:mk {α₀} ⦃ inst₁ ⦄ ⦃ toOrderTop₃ ⦄ ⦃ toOrderBot₄ ⦄)) → (t₃ : BoundedOrder α₀ ⦃ inst₁ ⦄) → motive₂ t₃
BoundedOrder:rec {α₀} ⦃ inst₁ ⦄ {motive₂} mk₃ (BoundedOrder:mk ⦃ toOrderTop₄ ⦄ ⦃ toOrderBot₅ ⦄) = mk₃ ⦃ toOrderTop₄ ⦄ ⦃ toOrderBot₅ ⦄
