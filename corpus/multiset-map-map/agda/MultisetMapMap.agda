{-# OPTIONS --safe --cubical-compatible #-}

-- File: corpus/multiset-map-map/agda/MultisetMapMap.agda
--
-- Mathlib's Multiset.map_map (Mathlib.Data.Multiset.MapFold, Mathlib v4.33.1):
--
--     theorem map_map (g : β → γ) (f : α → β) (s : Multiset α) :
--       map g (map f s) = map (g ∘ f) s :=
--       Quot.inductionOn s fun _l => congr_arg _ List.map_map
--
-- under profile CC, where Lean's quotient primitives are a module parameter:
-- a record of Quot, mk, lift, ind and sound, with the computation rule of
-- lift as a propositional equation, and the proof that Lean's quotients are
-- sets.  Lean checks map_map's proof by computing with Quot.lift three
-- times; here each computation is a rewrite by lift-β (see ../notes.md).

module MultisetMapMap where

open import Level using (Level; _⊔_; suc; Setω)
open import Function.Base using (_∘_)
open import Data.Product.Base using (Σ; _,_; proj₁)
open import Data.List.Base using (List)
import Data.List.Base as List
open import Data.List.Properties using (map-∘)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (map⁺)
open import Relation.Nullary.Irrelevant using (Irrelevant)
open import Axiom.UniquenessOfIdentityProofs using (UIP)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; cong; sym)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

-- Lean's Prop, read as the propositions among the types of Set p: a type
-- with a proof that any two of its elements are equal.  Lean has this proof
-- for free, by definitional proof irrelevance; here it is data.

Ω : (p : Level) → Set (suc p)
Ω p = Σ (Set p) Irrelevant

-- Lean's quotient primitives, one record for every quotient, as Lean has
-- one Quot for every type and relation.  Lean's are as follows:
--
--     Quot       : {α : Sort u} → (α → α → Prop) → Sort u
--     Quot.mk    : {α : Sort u} → (r : α → α → Prop) → α → Quot r
--     Quot.lift  : {α : Sort u} → {r : α → α → Prop} → {β : Sort v}
--                → (f : α → β) → (∀ a b, r a b → f a = f b) → Quot r → β
--     Quot.ind   : {α : Sort u} → {r : α → α → Prop} → {β : Quot r → Prop}
--                → (∀ a, β (Quot.mk r a)) → ∀ q, β q
--     Quot.sound : {α : Sort u} → {r : α → α → Prop} → {a b : α}
--                → r a b → Quot.mk r a = Quot.mk r b
--
-- with the kernel's rule Quot.lift f h (Quot.mk r a) ⇝ f a.  Three fields
-- differ from a word-for-word rendering, each because Lean's Prop is proof
-- irrelevant and Agda's Set is not (../notes.md, The Agda version):
--
-- +  ind's motive takes values in Ω: with a motive in all of Set, ind would
--    give every quotient map a section, Mathlib's Quot.out, which Mathlib
--    defines with Classical.choice;
-- +  lift asks that its target be a set (UIP B), which every Lean type is;
-- +  squash says that Quot R is a set, which every Lean type is, and which
--    makes an equation between elements of a quotient a motive for ind.
--
-- The relation R is any Set-valued relation, not only an Ω-valued one: a
-- Lean inductive proposition such as List.Perm becomes a family in Set whose
-- proofs are not all equal, and the quotient does not need them to be.

record Quotients : Setω where
  field
    Quot   : {a r : Level} {A : Set a} → (A → A → Set r) → Set (a ⊔ r)
    mk     : {a r : Level} {A : Set a} (R : A → A → Set r) → A → Quot R
    lift   : {a r b : Level} {A : Set a} {R : A → A → Set r} {B : Set b}
           → UIP B → (f : A → B) → (∀ x y → R x y → f x ≡ f y)
           → Quot R → B
    ind    : {a r p : Level} {A : Set a} {R : A → A → Set r}
             {P : Quot R → Ω p}
           → ((x : A) → proj₁ (P (mk R x))) → (q : Quot R) → proj₁ (P q)
    sound  : {a r : Level} {A : Set a} {R : A → A → Set r} {x y : A}
           → R x y → mk R x ≡ mk R y
    squash : {a r : Level} {A : Set a} {R : A → A → Set r} → UIP (Quot R)

    -- The computation rule, which Lean's kernel applies by reduction.
    lift-β : {a r b : Level} {A : Set a} {R : A → A → Set r} {B : Set b}
           → (uip : UIP B) (f : A → B) (h : ∀ x y → R x y → f x ≡ f y)
           → (x : A) → lift uip f h (mk R x) ≡ f x

module _ (Q : Quotients) where
  open Quotients Q

  -- Lean's Multiset α is Quotient (List.isSetoid α), that is,
  -- Quot (Setoid.r (List.isSetoid α)), whose relation is List.Perm.  Here
  -- the relation is agda-stdlib's propositional permutation _↭_, and the
  -- quotient is taken by it directly, with no setoid in between.

  Multiset : Set a → Set a
  Multiset A = Quot (_↭_ {A = A})

  -- Lean's coercion of a list to a multiset, Multiset.ofList, is Quot.mk.

  ⟦_⟧ : List A → Multiset A
  ⟦_⟧ = mk _↭_

  -- Lean: map f s = Quot.liftOn s (fun l => (l.map f : Multiset β))
  --                   fun _l₁ _l₂ p => Quot.sound (p.map f)

  map : (A → B) → Multiset A → Multiset B
  map f = lift squash (λ l → ⟦ List.map f l ⟧) (λ _ _ p → sound (map⁺ f p))

  -- What Lean has by computation: map f ⟦ l ⟧ reduces to ⟦ List.map f l ⟧.

  map-β : (f : A → B) (l : List A) → map f ⟦ l ⟧ ≡ ⟦ List.map f l ⟧
  map-β f = lift-β squash (λ l → ⟦ List.map f l ⟧) (λ _ _ p → sound (map⁺ f p))

  -- The theorem.  Lean's proof is Quot.inductionOn s (fun l => congr_arg
  -- Quot.mk (List.map_map ...)), and its kernel accepts congr_arg's equation
  -- between ⟦ List.map g (List.map f l) ⟧ and ⟦ List.map (g ∘ f) l ⟧ as one
  -- between map g (map f ⟦ l ⟧) and map (g ∘ f) ⟦ l ⟧ by reducing Quot.lift
  -- on Quot.mk three times.  Each reduction is a step by map-β below.

  map-map : (g : B → C) (f : A → B) (s : Multiset A)
          → map g (map f s) ≡ map (g ∘ f) s
  map-map g f = ind {P = λ s → (map g (map f s) ≡ map (g ∘ f) s) , squash} step
    where
    open ≡-Reasoning
    step : (l : List _) → map g (map f ⟦ l ⟧) ≡ map (g ∘ f) ⟦ l ⟧
    step l = begin
      map g (map f ⟦ l ⟧)               ≡⟨ cong (map g) (map-β f l) ⟩
      map g ⟦ List.map f l ⟧            ≡⟨ map-β g (List.map f l) ⟩
      ⟦ List.map g (List.map f l) ⟧     ≡⟨ cong ⟦_⟧ (sym (map-∘ l)) ⟩
      ⟦ List.map (g ∘ f) l ⟧            ≡⟨ sym (map-β (g ∘ f) l) ⟩
      map (g ∘ f) ⟦ l ⟧                 ∎
