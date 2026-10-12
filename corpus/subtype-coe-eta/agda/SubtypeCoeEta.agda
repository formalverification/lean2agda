{-# OPTIONS --safe --cubical-compatible #-}

-- File: corpus/subtype-coe-eta/agda/SubtypeCoeEta.agda
--
-- Mathlib's Subtype.coe_eta (Mathlib.Data.Subtype, Mathlib v4.33.1):
--
--     theorem coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a :=
--       Subtype.ext rfl
--
-- under encoding A of Lean's Prop (issue #27): a proposition is a type of
-- Set p with a proof that any two of its elements are equal, the Ω of the
-- corpus entries multiset-map-map and set-ext.  Lean proves the theorem by
-- Subtype.ext, whose pattern match is accepted by definitional proof
-- irrelevance; here that step uses the proof carried by Ω (see ../notes.md).

module SubtypeCoeEta where

open import Level using (Level; _⊔_; suc)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary.Irrelevant using (Irrelevant)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong)

private
  variable
    a p : Level
    A : Set a

-- Lean's Prop, read as the propositions among the types of Set p: a type
-- with a proof that any two of its elements are equal.  Lean has this proof
-- for free, by definitional proof irrelevance; here it is data.

Ω : (p : Level) → Set (suc p)
Ω p = Σ (Set p) Irrelevant

-- Lean's structure Subtype {α : Sort u} (p : α → Prop), with fields val and
-- property.  Lean's structure is a record here, so Agda's eta for records
-- holds of it, as Lean's structure eta holds of the structure.  Lean's α
-- may be a proposition (Sort u at u = 0); under this encoding a proposition
-- is a type with a proof of irrelevance, so A : Set a covers that case too.

record Subtype {A : Set a} (P : A → Ω p) : Set (a ⊔ p) where
  constructor mk
  field
    val      : A
    property : proj₁ (P val)

open Subtype

-- Lean's Subtype.ext (Init.Core), proved by matching both subtypes and the
-- equation of their values:
--
--     protected theorem ext : ∀ {a1 a2 : {x // p x}}, val a1 = val a2 → a1 = a2
--       | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
--
-- Lean's kernel accepts the final rfl, at type ⟨v, h₁⟩ = ⟨v, h₂⟩, by
-- identifying the proofs h₁ and h₂.  Here the two proofs are equal by the
-- irrelevance carried by Ω, a propositional step where Lean has a
-- definitional one.

ext : {P : A → Ω p} {a₁ a₂ : Subtype P} → val a₁ ≡ val a₂ → a₁ ≡ a₂
ext {P = P} {a₁ = mk v h₁} {a₂ = mk .v h₂} refl = cong (mk v) (proj₂ (P v) h₁ h₂)

-- The theorem, by Lean's proof: Subtype.ext at the reflexive equation of
-- the values.

coe-eta : {P : A → Ω p} (x : Subtype P) (h : proj₁ (P (val x))) → mk (val x) h ≡ x
coe-eta x h = ext refl

-- The direct proof, which Lean's kernel would also accept as rfl (eta and
-- proof irrelevance together; ../notes.md, What the kernel term needed).
-- Record eta makes mk (val x) (property x) equal to x by definition, so the
-- one step left is the irrelevance of the two proofs.

coe-eta-direct : {P : A → Ω p} (x : Subtype P) (h : proj₁ (P (val x)))
               → mk (val x) h ≡ x
coe-eta-direct {P = P} x h = cong (mk (val x)) (proj₂ (P (val x)) h (property x))
