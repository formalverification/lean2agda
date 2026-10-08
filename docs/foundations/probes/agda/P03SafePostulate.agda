-- Outcome on 2026-10-07 with Agda 2.8.0: rejected, [SafeFlagPostulate] Cannot postulate funext with safe flag
{-# OPTIONS --safe #-}
module P03SafePostulate where
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
postulate funext : {A : Set} {B : A → Set} {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
