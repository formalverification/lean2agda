-- Outcome on 2026-10-07 with Agda 2.8.0: accepted
{-# OPTIONS --safe --cubical --guardedness --prop #-}
module P18PropCubical where
open import Cubical.Foundations.Prelude
data Squash (A : Type) : Prop where
  sq : A → Squash A
module _ (P : Prop) (A : Type) (f : P → A) where
  irr : (p q : P) → f p ≡ f q
  irr p q = refl
