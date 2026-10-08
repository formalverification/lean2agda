-- Outcome on 2026-10-07 with Agda 2.8.0: accepted
{-# OPTIONS --safe --cubical-compatible #-}
module P10RecordEta where
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
-- records have definitional eta, the unit record included
eta× : {A B : Set} (p : A × B) → p ≡ (proj₁ p , proj₂ p)
eta× p = refl
eta⊤ : (u : ⊤) → u ≡ tt
eta⊤ u = refl
