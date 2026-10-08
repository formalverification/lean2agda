-- Outcome on 2026-10-07 with Agda 2.8.0: rejected, [UnequalTerms] w != wrap (unwrap w) of type Wrap A
{-# OPTIONS --safe --cubical-compatible #-}
module P10bDataNoEta where
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
-- a one-constructor data type has no eta
data Wrap (A : Set) : Set where
  wrap : A → Wrap A
unwrap : {A : Set} → Wrap A → A
unwrap (wrap a) = a
etaWrap : {A : Set} (w : Wrap A) → w ≡ wrap (unwrap w)
etaWrap w = refl
