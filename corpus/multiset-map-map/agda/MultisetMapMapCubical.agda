{-# OPTIONS --safe --cubical --guardedness #-}

-- File: corpus/multiset-map-map/agda/MultisetMapMapCubical.agda
--
-- Mathlib's Multiset.map_map (Mathlib.Data.Multiset.MapFold, Mathlib v4.33.1):
--
--     theorem map_map (g : β → γ) (f : α → β) (s : Multiset α) :
--       map g (map f s) = map (g ∘ f) s :=
--       Quot.inductionOn s fun _l => congr_arg _ List.map_map
--
-- under profile CU, where a quotient is a higher inductive type: Multiset is
-- the cubical library's set quotient of lists by permutation, map is defined
-- by SQ.rec, which computes on [ l ] as Lean's Quot.lift does on Quot.mk, and
-- map_map is proved by SQ.elimProp, Lean's Quot.ind, with no rewrite.  The
-- last section instantiates the records of MultisetMapMap.agda, the profile
-- CC version, with the same set quotients (see ../notes.md).

module MultisetMapMapCubical where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.List using (List; []; _∷_)
import Cubical.Data.List as List
open import Cubical.Data.List.Properties using (map-∘)
open import Cubical.HITs.SetQuotients as SQ using (_/_; [_]; eq/; squash/)

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'
    C : Type ℓ''

-- Lean's List.Perm, constructor for constructor.  The cubical library has
-- no permutation relation on lists.

data Perm {A : Type ℓ} : List A → List A → Type ℓ where
  nil   : Perm [] []
  cons  : (x : A) {l₁ l₂ : List A} → Perm l₁ l₂ → Perm (x ∷ l₁) (x ∷ l₂)
  swap  : (x y : A) (l : List A) → Perm (y ∷ x ∷ l) (x ∷ y ∷ l)
  trans : {l₁ l₂ l₃ : List A} → Perm l₁ l₂ → Perm l₂ l₃ → Perm l₁ l₃

-- Lean's List.Perm.map, by induction on the permutation.  Lean's proof goes
-- through List.filterMap and the equation filterMap (some ∘ f) = map f.

Perm-map : (f : A → B) {l₁ l₂ : List A}
         → Perm l₁ l₂ → Perm (List.map f l₁) (List.map f l₂)
Perm-map f nil          = nil
Perm-map f (cons x p)   = cons (f x) (Perm-map f p)
Perm-map f (swap x y l) = swap (f x) (f y) (List.map f l)
Perm-map f (trans p q)  = trans (Perm-map f p) (Perm-map f q)

-- Lean's Multiset α, Quot (Setoid.r (List.isSetoid α)), as a set quotient.
-- It lives in the universe of A, as Lean's does.

Multiset : Type ℓ → Type ℓ
Multiset A = List A / Perm

-- Lean: map f s = Quot.liftOn s (fun l => (l.map f : Multiset β))
--                   fun _l₁ _l₂ p => Quot.sound (p.map f)
-- SQ.rec asks that the target be a set, which squash/ says Multiset B is.

map : (A → B) → Multiset A → Multiset B
map f = SQ.rec squash/ (λ l → [ List.map f l ])
                (λ _ _ p → eq/ _ _ (Perm-map f p))

-- The theorem.  As in Lean's kernel, map g (map f [ l ]) and
-- map (g ∘ f) [ l ] reduce to [ List.map g (List.map f l) ] and
-- [ List.map (g ∘ f) l ], so the image of List.map_map under [_] is accepted
-- as it stands.  The motive is a proposition because Multiset C is a set.

map-map : (g : B → C) (f : A → B) (s : Multiset A)
        → map g (map f s) ≡ map (g ∘ f) s
map-map g f = SQ.elimProp (λ _ → squash/ _ _) (λ l → cong [_] (map-∘ g f l))

------------------------------------------------------------------------
-- The parameterized version, instantiated
--
-- The record Quotients of MultisetMapMap.agda can be built from the cubical
-- library's set quotients, with the conversions between paths and the
-- inductive equality _≡ᵢ_ that agda-stdlib uses.  That shows the record
-- asks for no more than a constructive, univalent setting provides, and it
-- turns the profile CC proof into a second cubical one.  Its computation
-- rule lift-β holds by reflexivity, since SQ.rec computes on points.

open import Agda.Builtin.Equality using () renaming (_≡_ to _≡ᵢ_; refl to reflᵢ)
open import Cubical.Data.Equality
  using (eqToPath; pathToEq; eqToPath-pathToEq; pathToEq-eqToPath;
         isPropToIsPropPath)
open import Data.Product.Base using (proj₂)
open import Axiom.UniquenessOfIdentityProofs using (UIP)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
import MultisetMapMap as CC

UIP→isSet : UIP A → isSet A
UIP→isSet uip x y p q =
  sym (eqToPath-pathToEq p)
    ∙∙ cong eqToPath (eqToPath (uip (pathToEq p) (pathToEq q)))
    ∙∙ eqToPath-pathToEq q

isSet→UIP : isSet A → UIP A
isSet→UIP set {x} {y} p q = pathToEq
  (sym (pathToEq-eqToPath p)
    ∙∙ cong pathToEq (set x y (eqToPath p) (eqToPath q))
    ∙∙ pathToEq-eqToPath q)

setQuotients : CC.Quotients
setQuotients = record
  { Quot   = λ {A = A} R → A / R
  ; mk     = λ R → [_]
  ; lift   = λ uip f h → SQ.rec (UIP→isSet uip) f (λ x y r → eqToPath (h x y r))
  ; ind    = λ {P = P} base →
               SQ.elimProp (λ q → isPropToIsPropPath (proj₂ (P q))) base
  ; sound  = λ r → pathToEq (eq/ _ _ r)
  ; squash = isSet→UIP squash/
  ; lift-β = λ uip f h x → reflᵢ
  }

-- The profile CC theorem, for the set quotient of lists by agda-stdlib's _↭_.

map-mapᶜᶜ : (g : B → C) (f : A → B) (s : List A / _↭_)
          → CC.map setQuotients g (CC.map setQuotients f s)
            ≡ᵢ CC.map setQuotients (g ∘ f) s
map-mapᶜᶜ = CC.map-map setQuotients
