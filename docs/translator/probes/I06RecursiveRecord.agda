-- Outcome on 2026-10-13 with Agda 2.8.0: accepted
{-# OPTIONS --type-in-type #-}
module I06RecursiveRecord where

data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

data List (α₀ : Set) : Set where
  List:nil : List α₀
  List:cons : α₀ → List α₀ → List α₀

data Eq {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁

-- A recursive structure as an inductive record without eta: its
-- projections compute on the constructor, as Lean's do.
record Tree : Set where
  inductive
  no-eta-equality
  pattern
  constructor Tree:mk
  field
    label₀ : Nat
    children₁ : List Tree

computes : Eq {List Tree} (Tree.children₁ (Tree:mk 1 List:nil)) List:nil
computes = Eq:refl List:nil

plus : Nat → Nat → Nat
plus Nat:zero n = n
plus (Nat:succ m) n = Nat:succ (plus m n)

-- Pattern matching on its constructor, recursion through the nested
-- list, as the recursors of issue M2-5 will need.
mutual
  size : Tree → Nat
  size (Tree:mk l cs) = Nat:succ (sizes cs)

  sizes : List Tree → Nat
  sizes List:nil = Nat:zero
  sizes (List:cons t ts) = plus (size t) (sizes ts)

-- A one-constructor type recursive through a function type.
record Stream′ : Set where
  inductive
  no-eta-equality
  pattern
  constructor Stream′:mk
  field
    head₀ : Nat
    tail₁ : Nat → Stream′

depth : Stream′ → Nat → Nat
depth (Stream′:mk h t) Nat:zero = h
depth (Stream′:mk h t) (Nat:succ n) = depth (t n) n
