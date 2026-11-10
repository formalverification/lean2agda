-- Outcome on 2026-10-13 with Agda 2.8.0: rejected, [TerminationIssue] at the signature line, 11.1-13.38
{-# OPTIONS --type-in-type #-}
module R04NotStructural where

data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat

-- What a refusal of Agda's termination checker looks like to the
-- scaffold's checker: a recursive call on the major premise itself.
bad : (t₀ : Nat) → Nat
bad Nat:zero = Nat:zero
bad (Nat:succ n₁) = bad (Nat:succ n₁)
