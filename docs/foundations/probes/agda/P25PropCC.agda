-- Outcome on 2026-10-07 with Agda 2.8.0: accepted
{-# OPTIONS --safe --cubical-compatible --prop #-}
module P25PropCC where
data ⊥ : Prop where
data Bool : Set where true false : Bool
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()
data Squash (A : Set) : Prop where
  sq : A → Squash A
squash-elim : {A : Set} {P : Prop} → (A → P) → Squash A → P
squash-elim f (sq a) = f a
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
module _ (P : Prop) (f : P → Bool) where
  irr : (p q : P) → f p ≡ f q
  irr p q = refl
