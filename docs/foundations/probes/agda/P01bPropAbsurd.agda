-- Outcome on 2026-10-07 with Agda 2.8.0: accepted
{-# OPTIONS --safe --prop #-}
module P01bPropAbsurd where
data ⊥ : Prop where
data Bool : Set where true false : Bool
-- the absurd pattern is the one elimination from Prop into Set Agda allows
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()
-- a Prop motive is fine, and two proofs of a Prop are definitionally equal
data Squash (A : Set) : Prop where
  sq : A → Squash A
data _≐_ {A : Set} (x : A) : A → Prop where
  refl : x ≐ x
substP : {A : Set} (P : A → Prop) {x y : A} → x ≐ y → P x → P y
substP P refl px = px
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
module _ (P : Prop) (f : P → Bool) where
  irr : (p q : P) → f p ≡ f q
  irr p q = refl
