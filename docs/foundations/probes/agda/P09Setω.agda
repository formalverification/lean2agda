-- Outcome on 2026-10-07 with Agda 2.8.0: rejected, [UnequalSorts] Setω != Set₁
{-# OPTIONS --safe #-}
module P09Setω where
open import Agda.Primitive
-- a universe-polymorphic function type is in Setω, not in any Set ℓ
Poly : Setω
Poly = (ℓ : Level) → Set ℓ → Set ℓ
-- forcing it into a Set ℓ fails
Poly' : Set₁
Poly' = (ℓ : Level) → Set ℓ → Set ℓ
