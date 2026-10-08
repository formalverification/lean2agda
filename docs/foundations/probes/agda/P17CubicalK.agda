-- Outcome on 2026-10-07 with Agda 2.8.0: rejected, [SplitError.UnificationStuck] I'm not sure if there should be a case for the constructor refl,
{-# OPTIONS --safe --cubical --guardedness #-}
module P17CubicalK where
open import Agda.Builtin.Equality using (_≡_; refl)
-- --cubical also disables K
uip : {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
uip refl refl = refl
