{-# OPTIONS --safe --cubical-compatible --prop #-}

-- File: corpus/subtype-coe-eta/agda/SubtypeCoeEtaProp.agda
--
-- Mathlib's Subtype.coe_eta (Mathlib.Data.Subtype, Mathlib v4.33.1):
--
--     theorem coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a :=
--       Subtype.ext rfl
--
-- under encoding B of Lean's Prop (issue #27): a proposition is a type of
-- Agda's Prop universe, whose elements are equal by definition, as Lean's
-- proofs are.  The theorem then holds by refl, through record eta and the
-- definitional irrelevance of Prop together (see ../notes.md).

module SubtypeCoeEtaProp where

open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst)

private
  variable
    a p : Level

-- Lean's Subtype {α : Sort u} (p : α → Prop) at u ≥ 1, where α is a type.

record Subtype {A : Set a} (P : A → Prop p) : Set (a ⊔ p) where
  constructor mk
  field
    val      : A
    property : P val

open Subtype

-- Lean's Subtype.ext.  Lean proves it by matching both subtypes and the
-- equation of their values.  The same match is accepted here, but with the
-- warning UnsupportedIndexedMatch: under --cubical-compatible its clause
-- would have to transport the Prop field, which Agda cannot generate
-- (../notes.md, The Agda version).  So the proof is a substitution along
-- the equation instead; its final refl identifies the two proofs by
-- definition, as Lean's rfl does.

ext : {A : Set a} {P : A → Prop p} {a₁ a₂ : Subtype P} → val a₁ ≡ val a₂ → a₁ ≡ a₂
ext {P = P} {a₁ = mk v h₁} {a₂ = mk w h₂} e =
  subst (λ w → (h₂ : P w) → mk v h₁ ≡ mk w h₂) e (λ _ → refl) h₂

-- The theorem, by Lean's proof.

coe-eta : {A : Set a} {P : A → Prop p} (x : Subtype P) (h : P (val x))
        → mk (val x) h ≡ x
coe-eta x h = ext refl

-- The direct proof: refl, by record eta (x is mk (val x) (property x)) and
-- the irrelevance of Prop (h is property x).

coe-eta-direct : {A : Set a} {P : A → Prop p} (x : Subtype P) (h : P (val x))
               → mk (val x) h ≡ x
coe-eta-direct x h = refl

-- Lean's Subtype at u = 0, where α is itself a proposition.  Lean's one
-- declaration covers both cases because α : Sort u ranges over Prop as
-- well; under this encoding a proposition lives in Prop, not Set, so the
-- case needs its own record and its own copy of the theorem, which is the
-- specialization by zero level parameters of issue #28.  Lean's Subtype at
-- u = 0 lives in Sort (max 1 0) = Type, a type and not a proposition, and so
-- does this record.

record SubtypeP {A : Prop a} (P : A → Prop p) : Set (a ⊔ p) where
  constructor mkP
  field
    valP      : A
    propertyP : P valP

open SubtypeP

coe-eta-P : {A : Prop a} {P : A → Prop p} (x : SubtypeP P) (h : P (valP x))
          → mkP (valP x) h ≡ x
coe-eta-P x h = refl
