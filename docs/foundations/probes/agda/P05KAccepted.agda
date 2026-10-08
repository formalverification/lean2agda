-- Outcome on 2026-10-07 with Agda 2.8.0: accepted
{-# OPTIONS --safe #-}
module P05KAccepted where
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
-- Agda's default theory has K: both pass by pattern matching
K : {A : Set} {x : A} (P : x ≡ x → Set) → P refl → (p : x ≡ x) → P p
K P pr refl = pr
uip : {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
uip refl refl = refl
