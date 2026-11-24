-- Outcome on 2026-11-24 with Agda 2.8.0: accepted
{-# OPTIONS --prop --type-in-type --rewriting #-}
module L03PropRewriteRelation where

-- Under the measurement's `Prop` printing, Lean's `Eq` is `Prop`-valued
-- at both instances: over a proposition (`Eq#z`) and over a type
-- (`Eq#n`).  This file asks whether such relations can be
-- `BUILTIN REWRITE` relations, and whether a rule over one fires.
data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat

data Eq#n {α₀ : Set} : α₀ → α₀ → Prop where
  Eq:refl#n : (a₁ : α₀) → Eq#n {α₀} a₁ a₁
{-# BUILTIN REWRITE Eq#n #-}

data Eq#z {α₀ : Prop} : α₀ → α₀ → Prop where
  Eq:refl#z : (a₁ : α₀) → Eq#z {α₀} a₁ a₁
{-# BUILTIN REWRITE Eq#z #-}

postulate f : Nat → Nat
postulate f-β : (n₀ : Nat) → Eq#n {Nat} (f (Nat:succ n₀)) n₀
{-# REWRITE f-β #-}

fires : (n₀ : Nat) → Eq#n {Nat} (f (Nat:succ n₀)) n₀
fires n₀ = Eq:refl#n n₀
