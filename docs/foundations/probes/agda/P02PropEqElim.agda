-- Outcome on 2026-10-07 with Agda 2.8.0: rejected, [SplitInProp] Cannot split on datatype in Prop unless target is in Prop
{-# OPTIONS --safe --prop #-}
module P02PropEqElim where
data _≐_ {A : Set} (x : A) : A → Prop where
  refl : x ≐ x
-- Lean's Eq.rec into Sort u; Agda rejects the Set-valued motive
subst : {A : Set} (P : A → Set) {x y : A} → x ≐ y → P x → P y
subst P refl px = px
