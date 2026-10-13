-- Outcome on 2026-10-13 with Agda 2.8.0: rejected, [SplitOnNonEtaRecord] Pattern matching on no-eta record type Tree is not allowed
{-# OPTIONS --type-in-type #-}
module I06cNoEtaPattern where

postulate Nat : Set

data List (α₀ : Set) : Set where
  List:nil : List α₀
  List:cons : α₀ → List α₀ → List α₀

-- Without the `pattern` declaration, a no-eta record's constructor is no
-- pattern, which the recursors of issue M2-5 will need.
record Tree : Set where
  inductive
  no-eta-equality
  constructor Tree:mk
  field
    label₀ : Nat
    children₁ : List Tree

label : Tree → Nat
label (Tree:mk l cs) = l
