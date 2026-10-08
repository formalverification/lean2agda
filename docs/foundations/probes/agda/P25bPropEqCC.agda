-- Outcome on 2026-10-07 with Agda 2.8.0: rejected, [CannotGenerateTransportClause] Could not generate a transport clause for substP
{-# OPTIONS --safe --cubical-compatible --prop #-}
module P25bPropEqCC where
data _≐_ {A : Set} (x : A) : A → Prop where
  refl : x ≐ x
-- a Prop motive, which --prop alone accepts (P01b): under --cubical-compatible it is rejected
substP : {A : Set} (P : A → Prop) {x y : A} → x ≐ y → P x → P y
substP P refl px = px
