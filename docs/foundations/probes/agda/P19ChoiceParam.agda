-- Outcome on 2026-10-07 with Agda 2.8.0: accepted
{-# OPTIONS --safe --cubical --guardedness #-}
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)
-- Lean's Classical.choice as a module parameter: accepted, since a parameter proves nothing
module P19ChoiceParam (choice : (A : Type) → ∥ A ∥₁ → A) where
_ : (A : Type) → ∥ A ∥₁ → A
_ = choice
