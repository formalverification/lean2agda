{-# OPTIONS --safe --cubical-compatible #-}

-- File: corpus/nat-gcd-succ/agda/NatGcdSucc.agda
--
-- Lean's Nat.gcd and its equation Nat.gcd_succ (Init.Data.Nat.Gcd, Lean
-- v4.33.1):
--
--     def gcd (m n : @& Nat) : Nat :=
--       if m = 0 then n else gcd (n % m) m
--       termination_by m
--
--     theorem gcd_succ (x y : Nat) : gcd (succ x) y = gcd (y % succ x) (succ x)
--
-- The definition is translated twice: by well-founded recursion on the
-- first argument, the idiomatic translation, and by recursion on fuel, the
-- way Lean's kernel term computes it, for comparison.  Each satisfies the
-- equation by an induction that uses neither K nor function
-- extensionality (see ../notes.md).

module NatGcdSucc where

open import Data.Nat.Base using (ℕ; zero; suc; _<_; s≤s⁻¹; _%_)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded-fast)
open import Data.Nat.Properties using (≤-refl; <-≤-trans)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

------------------------------------------------------------------------
-- The idiomatic translation

-- Well-founded recursion on the first argument, by pattern matching on a
-- proof that it is accessible, the way agda-stdlib writes its own gcd′ in
-- Data.Nat.GCD.  Lean's step is `if h : m = 0 then n else gcd (n % m) m`,
-- deciding m = 0 by Nat.decEq; here the decision is a split on zero and
-- suc, and the pattern suc _ supplies the NonZero instance that _%_ and
-- m%n<n need, where Lean passes the hypothesis ¬ m = 0 to its termination
-- proof.  The accessibility proof is agda-stdlib's <-wellFounded-fast,
-- as in its own gcd: the plain <-wellFounded builds each proof in unary,
-- so that gcd 1000000007 998244353 does not finish in two minutes, while
-- with the fast one it takes a few seconds.

gcd-acc : (m n : ℕ) → Acc _<_ m → ℕ
gcd-acc zero      n _        = n
gcd-acc m@(suc _) n (acc rs) = gcd-acc (n % m) m (rs (m%n<n n m))

gcd : ℕ → ℕ → ℕ
gcd m n = gcd-acc m n (<-wellFounded-fast m)

-- The result does not depend on the accessibility proof, by induction on
-- Acc.  Lean's kernel would get this for free from definitional proof
-- irrelevance if its gcd recursed on Acc, which at this version it does not.

gcd-acc-irrelevant : (m n : ℕ) (a b : Acc _<_ m) → gcd-acc m n a ≡ gcd-acc m n b
gcd-acc-irrelevant zero      n _        _         = refl
gcd-acc-irrelevant m@(suc _) n (acc rs) (acc rs′) =
  gcd-acc-irrelevant (n % m) m (rs (m%n<n n m)) (rs′ (m%n<n n m))

-- The equation.  <-wellFounded-fast (suc x) computes to acc _, so the left side
-- unfolds once by computation, to gcd-acc (y % suc x) (suc x) a for an
-- accessibility proof a other than the one the right side uses.

gcd-succ : (x y : ℕ) → gcd (suc x) y ≡ gcd (y % suc x) (suc x)
gcd-succ x y =
  gcd-acc-irrelevant (y % suc x) (suc x) _ (<-wellFounded-fast (y % suc x))

-- Closed instances compute.

_ : gcd 12 18 ≡ 6
_ = refl

------------------------------------------------------------------------
-- The direct translation

-- Lean's kernel term computes gcd through WellFounded.Nat.fix, which at
-- this version recurses on fuel, a natural number larger than the measure:
-- fix x = go (h x + 1) x _, where go is defined by Nat.rec on the fuel and
-- its zero case is unreachable.  Lean also packs the two arguments into
-- one, the pair ⟨m, n⟩ of Nat.gcd._unary, because its fixpoint takes one;
-- here they stay two.  The zero case is an absurd pattern.  The bound is
-- passed along, never matched on: a clause that matched s≤s would rely on
-- the injectivity of suc in an index, which --cubical-compatible accepts
-- with the warning UnsupportedIndexedMatch, so its predecessor is taken by
-- agda-stdlib's s≤s⁻¹ instead.

gcd-go : (fuel m n : ℕ) → m < fuel → ℕ
gcd-go zero       m         n ()
gcd-go (suc fuel) zero      n _        = n
gcd-go (suc fuel) m@(suc _) n m<1+fuel =
  gcd-go fuel (n % m) m (<-≤-trans (m%n<n n m) (s≤s⁻¹ m<1+fuel))

gcd-fuel : ℕ → ℕ → ℕ
gcd-fuel m n = gcd-go (suc m) m n ≤-refl

-- The two sides of the equation unfold with different fuel, so the
-- equation does not hold by computation, in Lean or here.  Lean bridges
-- the gap with WellFounded.Nat.fix.go_congr, by induction on the fuel and
-- funext; here the same induction needs no funext, because gcd's step
-- applies its recursive argument at one point.

gcd-go-congr : (f₁ f₂ m n : ℕ) (h₁ : m < f₁) (h₂ : m < f₂) →
               gcd-go f₁ m n h₁ ≡ gcd-go f₂ m n h₂
gcd-go-congr zero     _        m         n ()  _
gcd-go-congr (suc f₁) zero     m         n _   ()
gcd-go-congr (suc f₁) (suc f₂) zero      n _   _   = refl
gcd-go-congr (suc f₁) (suc f₂) m@(suc _) n _   _   =
  gcd-go-congr f₁ f₂ (n % m) m _ _

gcd-fuel-succ : (x y : ℕ) → gcd-fuel (suc x) y ≡ gcd-fuel (y % suc x) (suc x)
gcd-fuel-succ x y =
  gcd-go-congr (suc x) (suc (y % suc x)) (y % suc x) (suc x) _ _

_ : gcd-fuel 12 18 ≡ 6
_ = refl
