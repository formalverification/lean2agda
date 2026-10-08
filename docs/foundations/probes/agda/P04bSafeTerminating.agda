-- Outcome on 2026-10-07 with Agda 2.8.0: rejected, [SafeFlagTerminating] Cannot use TERMINATING pragma with safe flag.
{-# OPTIONS --safe #-}
module P04bSafeTerminating where
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# TERMINATING #-}
loop : ℕ → ℕ
loop n = loop (suc n)
