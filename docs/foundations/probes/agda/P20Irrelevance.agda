-- Outcome on 2026-10-07 with Agda 2.8.0: accepted
{-# OPTIONS --safe --cubical-compatible #-}
module P20Irrelevance where
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; _<_; suc; zero)
-- an irrelevant argument: proofs are not compared, so the two applications are equal by refl
f : (n : ℕ) → .(0 < n) → ℕ
f n _ = n
irr : (n : ℕ) (p q : 0 < n) → f n p ≡ f n q
irr n p q = refl
