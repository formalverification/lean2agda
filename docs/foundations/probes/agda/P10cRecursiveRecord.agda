-- Outcome on 2026-10-07 with Agda 2.8.0: accepted
{-# OPTIONS --safe --cubical-compatible #-}
module P10cRecursiveRecord where
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List using (List)
-- a recursive record: does Agda give it eta?
record Tree : Set where
  inductive
  field children : List Tree
open Tree
etaTree : (t : Tree) → t ≡ record { children = children t }
etaTree t = refl
