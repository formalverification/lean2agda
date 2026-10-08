-- Outcome on 2026-10-07 with Agda 2.8.0: accepted
{-# OPTIONS --safe --cubical --guardedness #-}
module P16CubicalQuotient where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence using (hPropExt)
open import Cubical.HITs.SetQuotients as SQ using (_/_; [_]; eq/)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Properties using (isSetℕ)
module _ {A : Type} (R : A → A → Type) (f : A → ℕ) (feq : ∀ a b → R a b → f a ≡ f b) where
  -- Quot.lift: rec computes definitionally on points, like Lean's Quot.lift on Quot.mk
  liftQ : A / R → ℕ
  liftQ = SQ.rec isSetℕ f feq
  _ : (a : A) → liftQ [ a ] ≡ f a
  _ = λ a → refl
  -- Quot.sound is the constructor eq/, Quot.ind is elimProp
  sound : (a b : A) → R a b → [ a ] ≡ [ b ]
  sound = eq/
  ind : {P : A / R → Type} → (∀ q → isProp (P q)) → (∀ a → P [ a ]) → ∀ q → P q
  ind = SQ.elimProp
-- funext and propositional extensionality are theorems
_ : {A B : Type} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
_ = funExt
_ : {P Q : Type} → isProp P → isProp Q → (P → Q) → (Q → P) → P ≡ Q
_ = hPropExt
