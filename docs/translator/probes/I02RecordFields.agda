-- Outcome on 2026-10-13 with Agda 2.8.0: accepted
{-# OPTIONS --type-in-type #-}
module I02RecordFields where

postulate N : Set
postulate C : N → Set

-- Fields bound implicitly and as instances in the constructor, as a
-- Lean class's parent fields are (Monad.mk binds [toApplicative]).
record R : Set where
  constructor R:mk
  field
    {n₀} : N
    ⦃ i₁ ⦄ : C n₀
    v₂ : N

q4 : (n : N) → C n → N → R
q4 n c v = R:mk {n} ⦃ c ⦄ v

q5 : R → N
q5 r = R.n₀ r

q6 : (r : R) → C (R.n₀ r)
q6 r = R.i₁ r

-- A record with no fields, and its eta.
record U : Set where
  constructor U:unit

data Eq {A : Set} (a : A) : A → Set where
  Eq:refl : Eq a a

q7 : (u : U) → Eq u U:unit
q7 u = Eq:refl

-- Names: a constructor with colons, a record whose name has colons and
-- escapes, and qualified projections of subscripted fields.
record Lean:Syntax:Preresolved~ux (α₀ : Set) : Set where
  constructor Lean:Syntax:Preresolved~ux:mk
  field
    data₁ : α₀
    field₂ : α₀

q8 : {α : Set} → Lean:Syntax:Preresolved~ux α → α
q8 {α} p = Lean:Syntax:Preresolved~ux.data₁ {α} p

-- Eta for a two-field record.
q9 : {α : Set} → (p : Lean:Syntax:Preresolved~ux α) →
  Eq p (Lean:Syntax:Preresolved~ux:mk (Lean:Syntax:Preresolved~ux.data₁ p) (Lean:Syntax:Preresolved~ux.field₂ p))
q9 p = Eq:refl
