-- Outcome on 2026-10-07 with Agda 2.8.0: rejected, [SafeFlagNonTerminating] Cannot use NON_TERMINATING pragma with safe flag.
{-# OPTIONS --safe #-}
module P12SafeNonTerminating where
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# NON_TERMINATING #-}
loop : ℕ → ℕ
loop n = loop (suc n)
