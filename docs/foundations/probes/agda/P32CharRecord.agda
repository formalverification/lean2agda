-- Outcome on 2026-11-10 with Agda 2.8.0: rejected, [BuiltinMustBePostulate] The argument to BUILTIN CHAR must be a postulated name, the intended rejection
{-# OPTIONS --safe --cubical-compatible #-}
module P32CharRecord where
-- Lean's Char is a structure, its UInt32 value and a proof that the value is a Unicode scalar;
-- Agda's primitive strings need BUILTIN CHAR, which binds only a postulate, so that a profile
-- that keeps Agda's primitive String must postulate Char and lose its recursor.  Here the
-- structure's shape, the value as a Nat for brevity, under BUILTIN CHAR.

data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

record Char : Set where
  constructor Char:mk
  field
    val : Nat
{-# BUILTIN CHAR Char #-}
