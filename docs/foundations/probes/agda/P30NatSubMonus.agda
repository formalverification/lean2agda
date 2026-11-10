-- Outcome on 2026-11-09 with Agda 2.8.0: rejected, [UnequalTerms] Nat:sub-builtin n (Nat:succ m) != Nat:pred (Nat:sub-builtin n m), the intended rejection
{-# OPTIONS --safe --cubical-compatible #-}
module P30NatSubMonus where
-- Lean's Nat.sub recurses on its second argument, Nat.sub n (succ m) = pred (Nat.sub n m), and
-- Lean's kernel accepts that equation on variables; Agda's builtin monus matches on its second
-- argument and then its first, so for a variable n the left side is stuck and differs from the
-- right.  No definition can be both: one that keeps the equation recurses on the second argument,
-- which Agda then unfolds once per unit of a numeral.

data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

Nat:sub-builtin : Nat → Nat → Nat
Nat:sub-builtin n Nat:zero = n
Nat:sub-builtin Nat:zero (Nat:succ m) = Nat:zero
Nat:sub-builtin (Nat:succ n) (Nat:succ m) = Nat:sub-builtin n m
{-# BUILTIN NATMINUS Nat:sub-builtin #-}

Nat:pred : Nat → Nat
Nat:pred Nat:zero = Nat:zero
Nat:pred (Nat:succ n) = n

-- Lean's other equation, Nat.sub n zero = n, holds.
_ : (n : Nat) → Nat:sub-builtin n Nat:zero ≡ n
_ = λ n → refl

_ : (n m : Nat) → Nat:sub-builtin n (Nat:succ m) ≡ Nat:pred (Nat:sub-builtin n m)
_ = λ n m → refl
