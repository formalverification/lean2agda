{-# OPTIONS --safe --cubical-compatible #-}

-- File: corpus/nat-gcd-self/agda/NatGcdSelf.agda
--
-- Lean's Nat.gcd_self (Init.Data.Nat.Gcd, Lean v4.33.1):
--
--     @[simp] theorem gcd_self (n : Nat) : gcd n n = n
--
-- stated over agda-stdlib's ℕ and gcd, and proved twice: from the
-- characterization of gcd by divisibility, the idiomatic proof, and by
-- computing agda-stdlib's gcd at two equal arguments, for comparison with
-- Lean's proof, which computes Lean's gcd (see ../notes.md).  agda-stdlib
-- has no lemma gcd n n ≡ n.

module NatGcdSelf where

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Divisibility using (∣-antisym; ∣-refl)
open import Data.Nat.GCD using (gcd; gcd[m,n]∣m; gcd-greatest)
open import Data.Nat.Properties using (<-cmp; <-irrefl)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Nullary.Negation.Core using (contradiction)

-- The idiomatic translation.  gcd n n divides n (gcd[m,n]∣m), n divides
-- gcd n n because it divides both arguments (gcd-greatest), and
-- divisibility on ℕ is antisymmetric.  agda-stdlib proves its own gcd
-- lemmas this way, from gcd[m,n]∣m, gcd[m,n]∣n and gcd-greatest alone, so
-- the proof does not depend on how gcd is computed.

gcd-self : (n : ℕ) → gcd n n ≡ n
gcd-self n = ∣-antisym (gcd[m,n]∣m n n) (gcd-greatest ∣-refl ∣-refl)

-- The direct proof.  agda-stdlib's gcd first compares its arguments with
-- <-cmp and returns m when they are equal, so at gcd n n the equal case
-- holds by computation and the other two contradict irreflexivity.  Lean's
-- proof has a different shape because Lean's gcd recurses on the first
-- argument: it splits n into 0 and k + 1, and at k + 1 it rewrites with
-- gcd_succ, mod_self and gcd_zero_left, closing the goal with eq_self.

gcd-self-direct : (n : ℕ) → gcd n n ≡ n
gcd-self-direct n with <-cmp n n
... | tri< n<n _ _ = contradiction n<n (<-irrefl refl)
... | tri≈ _ _ _   = refl
... | tri> _ _ n<n = contradiction n<n (<-irrefl refl)
