{-# OPTIONS --safe --cubical --guardedness #-}

-- File: corpus/set-ext/agda/SetExtCubical.agda
--
-- Mathlib's Set.ext (Mathlib.Data.Set.Defs, Mathlib v4.33.1):
--
--     theorem ext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b :=
--       funext (fun x ↦ propext (h x))
--
-- under profile CU, where Lean's Prop is read as the cubical library's hProp,
-- Lean's Set α as its powerset ℙ A, and funext and propext are theorems:
-- funExt, and hPropExt, which the library packages for hProp as ⇔toPath.
-- The statement is proved twice: by the library's ⊆-extensionality, and by
-- Lean's term.  The last section instantiates the records of SetExt.agda,
-- the profile CC version, with the same theorems (see ../notes.md).

module SetExtCubical where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset using (ℙ; _∈_; ⊆-extensionality)
open import Cubical.Functions.Logic using (⇔toPath)
open import Cubical.Data.Sigma using (_×_)

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

-- Lean's Iff, a structure with the two fields mp and mpr.

infix 3 _↔_

_↔_ : Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
P ↔ Q = (P → Q) × (Q → P)

-- The idiomatic proof.  The cubical library's ℙ A is A → hProp ℓ, which
-- lives in Type (ℓ-suc ℓ); Lean's Set α lives in the universe of α.

ext : {s t : ℙ A} → ((x : A) → x ∈ s ↔ x ∈ t) → s ≡ t
ext {s = s} {t} h = ⊆-extensionality s t ((λ x → fst (h x)) , (λ x → snd (h x)))

-- The direct proof, Lean's term: funext (fun x ↦ propext (h x)).

ext-direct : {s t : ℙ A} → ((x : A) → x ∈ s ↔ x ∈ t) → s ≡ t
ext-direct h = funExt (λ x → ⇔toPath (fst (h x)) (snd (h x)))

------------------------------------------------------------------------
-- The parameterized version, instantiated
--
-- The records PropExt and FunExt of SetExt.agda can be built from funExt
-- and hPropExt, with the conversions between paths and the inductive
-- equality _≡ᵢ_ that agda-stdlib uses.  That shows the records ask for no
-- more than a univalent setting proves, and it turns the profile CC proof
-- into a third cubical one.

open import Agda.Builtin.Equality using () renaming (_≡_ to _≡ᵢ_)
open import Cubical.Foundations.HLevels
  using (isPropΠ2; isOfHLevelRetractFromIso)
open import Cubical.Foundations.Isomorphism using (invIso)
open import Cubical.Foundations.Univalence using (hPropExt)
open import Cubical.Data.Sigma using (Σ≡Prop)
open import Cubical.Data.Equality
  using (pathToEq; PathIsoEq; isPropToIsPropPath)
  renaming (funExt to funExtᵢ)
open import Data.Product.Base using (proj₁; proj₂)
open import Function.Bundles using (Equivalence; _⇔_)
open import Relation.Nullary.Irrelevant using (Irrelevant)
import SetExt as CC

-- agda-stdlib's Irrelevant T is a proposition: two proofs that T is one are
-- equal, since T is then a set.

isPropIrrelevant : {T : Type ℓ} → isProp (Irrelevant T)
isPropIrrelevant {T = T} i j = isPropΠ2 isPropEq i j
  where
  isPropEq : (x y : T) → isProp (x ≡ᵢ y)
  isPropEq x y = isOfHLevelRetractFromIso 1 (invIso PathIsoEq)
                   (isProp→isSet (isPropToIsPropPath i) x y)

cubicalPropExt : CC.PropExt
cubicalPropExt = record { propext = λ {P = P} {Q} e → pathToEq
  (Σ≡Prop (λ _ → isPropIrrelevant)
    (hPropExt (isPropToIsPropPath (proj₂ P)) (isPropToIsPropPath (proj₂ Q))
      (Equivalence.to e) (Equivalence.from e))) }

cubicalFunExt : CC.FunExt
cubicalFunExt = record { funext = funExtᵢ }

-- The profile CC theorem, for sets of propositions in agda-stdlib's form.

extᶜᶜ : {s t : CC.ℙ A ℓ'} → ((x : A) → x CC.∈ s ⇔ x CC.∈ t) → s ≡ᵢ t
extᶜᶜ = CC.ext cubicalPropExt cubicalFunExt
