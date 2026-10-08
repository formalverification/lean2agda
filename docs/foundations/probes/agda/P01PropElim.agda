-- Outcome on 2026-10-07 with Agda 2.8.0: rejected, [SplitInProp] Cannot split on datatype in Prop unless target is in Prop
{-# OPTIONS --safe --prop #-}
module P01PropElim where
data Bool : Set where true false : Bool
data Squash (A : Set) : Prop where
  sq : A → Squash A
-- eliminating a Prop with a constructor into Set is rejected
unsq : Squash Bool → Bool
unsq (sq b) = b
