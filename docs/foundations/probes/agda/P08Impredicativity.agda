-- Outcome on 2026-10-07 with Agda 2.8.0: rejected, [UnequalSorts] Prop₁ != Prop
{-# OPTIONS --safe --prop #-}
module P08Impredicativity where
data Squash (A : Set) : Prop where
  sq : A → Squash A
-- Lean: ∀ (α : Type), Nonempty α : Prop.  Agda's Prop is predicative:
AllInhabited : Prop
AllInhabited = (A : Set) → Squash A
