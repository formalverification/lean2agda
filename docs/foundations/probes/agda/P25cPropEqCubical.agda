-- Outcome on 2026-10-07 with Agda 2.8.0: rejected, [CannotGenerateTransportClause] Could not generate a transport clause for substP
{-# OPTIONS --safe --cubical --guardedness --prop #-}
module P25cPropEqCubical where
open import Cubical.Foundations.Prelude using (Type)
data _≐_ {A : Type} (x : A) : A → Prop where
  refl : x ≐ x
substP : {A : Type} (P : A → Prop) {x y : A} → x ≐ y → P x → P y
substP P refl px = px
