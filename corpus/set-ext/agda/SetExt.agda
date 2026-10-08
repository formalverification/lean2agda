{-# OPTIONS --safe --cubical-compatible #-}

-- File: corpus/set-ext/agda/SetExt.agda
--
-- Mathlib's Set.ext (Mathlib.Data.Set.Defs, Mathlib v4.33.1):
--
--     theorem ext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b :=
--       funext (fun x ↦ propext (h x))
--
-- under profile CC, where propositional and function extensionality are
-- module parameters, each a record with one field.  With Lean's Prop read
-- as Ω below, the proof is Lean's term, word for word (see ../notes.md).

module SetExt where

open import Level using (Level; _⊔_; suc; Setω)
open import Data.Product.Base using (Σ; proj₁)
open import Function.Bundles using (_⇔_)
open import Relation.Nullary.Irrelevant using (Irrelevant)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

private
  variable
    a p : Level
    A : Set a

-- Lean's Prop, read as the propositions among the types of Set p: a type
-- with a proof that any two of its elements are equal.  Lean has this proof
-- for free, by definitional proof irrelevance; here it is data.

Ω : (p : Level) → Set (suc p)
Ω p = Σ (Set p) Irrelevant

-- Lean's axiom propext : {a b : Prop} → (a ↔ b) → a = b, with Prop read as
-- Ω p and Lean's Iff as agda-stdlib's _⇔_.  Stated for all of Set p instead
-- of Ω p, it would be refutable: Bool ⇔ ⊤ holds, and Bool ≡ ⊤ would make
-- Bool a proposition.

record PropExt : Setω where
  field
    propext : {p : Level} {P Q : Ω p} → proj₁ P ⇔ proj₁ Q → P ≡ Q

-- Lean's funext, which Lean proves from Quot.sound.  That proof computes
-- with Quot.lift under a binder, which a propositional computation rule
-- cannot do without funext itself, so here funext is its own parameter, in
-- agda-stdlib's form.

record FunExt : Setω where
  field
    funext : {a b : Level} → Extensionality a b

-- Lean's Set α := α → Prop, and membership, x ∈ s := s x, which Lean
-- reaches through the instance Set.instMembership.  Lean's Set α lives in
-- the universe of α, because Prop : Type; here ℙ A p lives one universe
-- above p, because Ω p does.

ℙ : Set a → (p : Level) → Set (a ⊔ suc p)
ℙ A p = A → Ω p

_∈_ : A → ℙ A p → Set p
x ∈ s = proj₁ (s x)

module _ (pe : PropExt) (fe : FunExt) where
  open PropExt pe
  open FunExt fe

  ext : {s t : ℙ A p} → ((x : A) → x ∈ s ⇔ x ∈ t) → s ≡ t
  ext h = funext (λ x → propext (h x))
