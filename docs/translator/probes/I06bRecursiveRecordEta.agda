-- Outcome on 2026-10-13 with Agda 2.8.0: rejected, [UnequalTerms] t != Tree:mk (Tree.label₀ t) (Tree.children₁ t) of type Tree
{-# OPTIONS --type-in-type #-}
module I06bRecursiveRecordEta where

postulate Nat : Set

data List (α₀ : Set) : Set where
  List:nil : List α₀
  List:cons : α₀ → List α₀ → List α₀

data Eq {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁

-- A recursive record declared without eta has none, as Lean's recursive
-- structures have none.
record Tree : Set where
  inductive
  no-eta-equality
  pattern
  constructor Tree:mk
  field
    label₀ : Nat
    children₁ : List Tree

noEta : (t : Tree) → Eq {Tree} t (Tree:mk (Tree.label₀ t) (Tree.children₁ t))
noEta t = Eq:refl t
