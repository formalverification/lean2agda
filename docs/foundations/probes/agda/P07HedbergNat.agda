-- Outcome on 2026-10-07 with Agda 2.8.0: accepted
{-# OPTIONS --safe --cubical-compatible #-}
module P07HedbergNat where
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (≡-irrelevant)
-- UIP for a type with decidable equality is a theorem without K (Hedberg), which is the
-- `isSet` proof that justifies a use of K on ℕ under profile CC
uipℕ : {m n : ℕ} (p q : m ≡ n) → p ≡ q
uipℕ = ≡-irrelevant
