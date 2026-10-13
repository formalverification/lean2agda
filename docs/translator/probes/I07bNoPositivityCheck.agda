-- Outcome on 2026-10-13 with Agda 2.8.0: accepted
{-# OPTIONS --type-in-type #-}
module I07bNoPositivityCheck where

postulate Nat : Set

-- Lean's kernel accepts this type only as an unsafe one, since it checks
-- no unsafe type for positivity; the pragma has Agda skip it too.
{-# NO_POSITIVITY_CHECK #-}
data Bad : Set where
  Bad:mk : (Bad → Nat) → Bad
