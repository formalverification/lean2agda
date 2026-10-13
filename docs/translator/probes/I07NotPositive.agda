-- Outcome on 2026-10-13 with Agda 2.8.0: rejected, [NotStrictlyPositive] Bad is not strictly positive, because it occurs to the left of an arrow
{-# OPTIONS --type-in-type #-}
module I07NotPositive where

postulate Nat : Set

-- Lean's kernel accepts this type only as an unsafe one, since it checks
-- no unsafe type for positivity; Agda checks every type.
data Bad : Set where
  Bad:mk : (Bad → Nat) → Bad
