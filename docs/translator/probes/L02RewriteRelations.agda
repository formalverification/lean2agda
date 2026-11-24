-- Outcome on 2026-11-24 with Agda 2.8.0: accepted
{-# OPTIONS --type-in-type --rewriting #-}
module L02RewriteRelations where

-- Each instance of Lean's `Eq` is a relation of its own, and the
-- quotient's computation rules are stated over more than one of them:
-- `Quot.lift`'s over the instance at its result's level, `Quot.ind`'s
-- over the instance at zero.  Agda takes several `BUILTIN REWRITE`
-- relations, one pragma each, and a rule over either fires.
data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat

data Eq#n {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl#n : (a₁ : α₀) → Eq#n {α₀} a₁ a₁
{-# BUILTIN REWRITE Eq#n #-}

data Eq#z {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl#z : (a₁ : α₀) → Eq#z {α₀} a₁ a₁
{-# BUILTIN REWRITE Eq#z #-}

postulate f : Nat → Nat
postulate g : Nat → Nat
postulate f-β : (n₀ : Nat) → Eq#n {Nat} (f (Nat:succ n₀)) n₀
postulate g-β : (n₀ : Nat) → Eq#z {Nat} (g (Nat:succ n₀)) n₀
{-# REWRITE f-β #-}
{-# REWRITE g-β #-}

-- Both rules fire: each side reduces to n₀.
fires-n : (n₀ : Nat) → Eq#n {Nat} (f (Nat:succ n₀)) n₀
fires-n n₀ = Eq:refl#n n₀

fires-z : (n₀ : Nat) → Eq#n {Nat} (g (Nat:succ n₀)) n₀
fires-z n₀ = Eq:refl#n n₀
