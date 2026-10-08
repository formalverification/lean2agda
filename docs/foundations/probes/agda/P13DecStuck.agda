-- Outcome on 2026-10-07 with Agda 2.8.0: rejected, [UnequalTerms] if does (lem ⊤) then 1 else 0 != 1 of type ℕ
{-# OPTIONS --safe --cubical-compatible #-}
open import Relation.Nullary.Decidable using (Dec; does)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤)
open import Data.Bool using (if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
-- excluded middle as a module parameter, as the classical layer will take it
module P13DecStuck (lem : (P : Set) → Dec P) where
f : ℕ
f = if does (lem ⊤) then 1 else 0
-- the decision is stuck on the parameter, so f does not compute
_ : f ≡ 1
_ = refl
