{-# OPTIONS --safe --cubical-compatible #-}

-- File: corpus/substructure-closure-le/agda/SubstructureClosureLe.agda
--
-- Mathlib's FirstOrder.Language.Substructure.closure_le
-- (Mathlib.ModelTheory.Substructures, Mathlib v4.33.1):
--
--     theorem closure_le : closure L s ≤ S ↔ s ⊆ S :=
--       (closure L).closure_le_closed_iff_le s S.closed
--
-- under profile CC, with no module parameters.  Mathlib defines the closure
-- of s as the infimum of all substructures containing s, a subset of M that
-- Lean's impredicative Prop keeps in the universe of M.  Predicatively, the
-- infimum lives one universe above the substructures it quantifies over; the
-- substructure generated inductively, as agda-algebras's Sg generates a
-- subuniverse, stays at their level.  The file defines both, proves
-- closure_le for each by its universal property, and shows that the two
-- have the same elements wherever both are defined (see ../notes.md).

module SubstructureClosureLe where

open import Level using (Level; _⊔_; suc; 0ℓ)
open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Function.Base using (_∘_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Unary using (Pred; _∈_; _⊆_)

------------------------------------------------------------------------
-- First-order languages and structures

-- Lean: structure Language where
--         Functions : ℕ → Type u
--         Relations : ℕ → Type v

record Language (u v : Level) : Set (suc (u ⊔ v)) where
  field
    Functions : ℕ → Set u
    Relations : ℕ → Set v

open Language

-- Lean: class Structure (L : Language) (M : Type w) where
--         funMap : ∀ {n}, L.Functions n → (Fin n → M) → M
--         RelMap : ∀ {n}, L.Relations n → (Fin n → M) → Prop
--
-- Lean's class becomes a record that the definitions below take as an
-- instance argument, as Lean's take [L.Structure M].  Lean's RelMap is
-- Prop-valued; here relations take values in Set ρ.  Nothing below uses
-- them: a substructure is closed under the function symbols only.

record Structure {u v : Level} (L : Language u v) (ρ : Level) {w : Level}
                 (M : Set w) : Set (u ⊔ v ⊔ w ⊔ suc ρ) where
  field
    funMap : {n : ℕ} → Functions L n → (Fin n → M) → M
    RelMap : {n : ℕ} → Relations L n → (Fin n → M) → Set ρ

module _ {u v w ρ : Level} {L : Language u v} {M : Set w}
         ⦃ 𝑴 : Structure L ρ M ⦄ where
  open Structure 𝑴

  ----------------------------------------------------------------------
  -- Substructures

  -- Lean's Set M is M → Prop; here a subset is agda-stdlib's Pred M p, a
  -- predicate with values in Set p.  Its proofs of membership need not be
  -- all equal, and closure_le never asks them to be (../notes.md, under
  -- impredicative-prop, says what Lean's Prop-valued sets would cost).

  -- Lean: def ClosedUnder (f : L.Functions n) (s : Set M) : Prop :=
  --         ∀ x : Fin n → M, (∀ i : Fin n, x i ∈ s) → funMap f x ∈ s

  ClosedUnder : {n : ℕ} {p : Level} → Functions L n → Pred M p → Set (w ⊔ p)
  ClosedUnder f s = (x : Fin _ → M) → (∀ i → x i ∈ s) → funMap f x ∈ s

  -- Lean: structure Substructure where
  --         carrier : Set M
  --         fun_mem : ∀ {n}, ∀ f : L.Functions n, ClosedUnder f carrier

  record Substructure (p : Level) : Set (u ⊔ w ⊔ suc p) where
    field
      carrier : Pred M p
      fun-mem : {n : ℕ} (f : Functions L n) → ClosedUnder f carrier

  open Substructure

  -- Lean orders substructures by inclusion of carriers (SetLike, with
  -- PartialOrder.ofSetLike).  The order relates substructures of any two
  -- levels, which the infimum below needs.

  infix 4 _≤_

  _≤_ : {p q : Level} → Substructure p → Substructure q → Set (w ⊔ p ⊔ q)
  S ≤ T = carrier S ⊆ carrier T

  ----------------------------------------------------------------------
  -- Mathlib's closure: the infimum of the substructures containing s

  -- Lean: instance : InfSet (L.Substructure M) :=
  --         ⟨fun s => { carrier := ⋂ t ∈ s, (t : Set M), fun_mem := ... }⟩
  --
  -- The infimum of a family T of substructures of level p quantifies over
  -- all of them, so its carrier lives at level u ⊔ w ⊔ suc p ⊔ q, above p.
  -- Lean's carrier is a Set M again, because a Prop may quantify over any
  -- universe.  Lean's proof of fun_mem splits on t ∈ s with by_cases, which
  -- takes its Decidable instance from Classical.propDecidable and so makes
  -- the closure, and closure_le, depend on Classical.choice; the proof here
  -- needs no case split.

  sInf : {p q : Level} → Pred (Substructure p) q
       → Substructure (u ⊔ w ⊔ suc p ⊔ q)
  sInf {p} T = record
    { carrier = λ x → (S : Substructure p) → S ∈ T → x ∈ carrier S
    ; fun-mem = λ f x x∈ S S∈T → fun-mem S f x (λ i → x∈ i S S∈T)
    }

  -- Lean: def closure : LowerAdjoint ((↑) : L.Substructure M → Set M) :=
  --         ⟨fun s => sInf { S | s ⊆ S }, ...⟩
  --
  -- With s at level p and the infimum taken over substructures of level p,
  -- the closure lands at level u ⊔ w ⊔ suc p.

  closureᵢ : {p : Level} → Pred M p → Substructure (u ⊔ w ⊔ suc p)
  closureᵢ {p} s = sInf {p = p} (λ S → s ⊆ carrier S)

  -- closure_le for the infimum, by its universal property: the closure
  -- contains s, and is contained in every substructure of level p that
  -- contains s.  S must have level p, the level the infimum ranges over.

  closureᵢ-le : {p : Level} {s : Pred M p} {S : Substructure p}
              → closureᵢ s ≤ S ⇔ s ⊆ carrier S
  closureᵢ-le {s = s} {S} = mk⇔ to from
    where
    to : closureᵢ s ≤ S → s ⊆ carrier S
    to h x∈s = h (λ T s⊆T → s⊆T x∈s)

    from : s ⊆ carrier S → closureᵢ s ≤ S
    from s⊆S x∈cl = x∈cl S s⊆S

  ----------------------------------------------------------------------
  -- agda-algebras's closure: the substructure generated inductively

  -- agda-algebras (src/Setoid/Subalgebras/Subuniverses.lagda.md):
  --
  --     data Sg (G : Pred A ℓ) : Pred A (𝓞 ⊔ 𝓥 ⊔ α ⊔ ℓ) where
  --       var : ∀ {v} → v ∈ G → v ∈ Sg G
  --       app : ∀ f a → Im a ⊆ Sg G → (f ^ 𝑨) a ∈ Sg G
  --
  -- transcribed for a first-order language: the arity of a function symbol
  -- is a natural number n, and its arguments a tuple Fin n → M.  Sg s lives
  -- at level u ⊔ w ⊔ p, with no suc: the constructors quantify over
  -- function symbols and tuples of elements, never over subsets.

  data Sg {p : Level} (s : Pred M p) : Pred M (u ⊔ w ⊔ p) where
    var : {x : M} → x ∈ s → x ∈ Sg s
    app : {n : ℕ} (f : Functions L n) (x : Fin n → M)
        → (∀ i → x i ∈ Sg s) → funMap f x ∈ Sg s

  closureₛ : {p : Level} → Pred M p → Substructure (u ⊔ w ⊔ p)
  closureₛ s = record { carrier = Sg s ; fun-mem = app }

  -- agda-algebras's sgIsSmallest: Sg s is contained in every substructure,
  -- of any level, that contains s.

  sg-smallest : {p q : Level} {s : Pred M p} (S : Substructure q)
              → s ⊆ carrier S → Sg s ⊆ carrier S
  sg-smallest S s⊆S (var x∈s)     = s⊆S x∈s
  sg-smallest S s⊆S (app f x x∈) = fun-mem S f x (λ i → sg-smallest S s⊆S (x∈ i))

  closureₛ-le : {p q : Level} {s : Pred M p} {S : Substructure q}
              → closureₛ s ≤ S ⇔ s ⊆ carrier S
  closureₛ-le {s = s} {S} = mk⇔ to (sg-smallest S)
    where
    to : closureₛ s ≤ S → s ⊆ carrier S
    to h x∈s = h (var x∈s)

  ----------------------------------------------------------------------
  -- The statement in Lean's shape: a lower adjoint of the carrier map

  -- Lean: structure LowerAdjoint [Preorder α] [Preorder β] (u : β → α) where
  --         toFun : α → β
  --         gc'   : GaloisConnection toFun u
  --
  -- with GaloisConnection l u := ∀ a b, l a ≤ b ↔ a ≤ u b, here for u the
  -- carrier map of substructures of one level 𝓁.  closure_le, as Lean states
  -- it, is the Galois connection itself.

  record LowerAdjoint (𝓁 : Level) : Set (u ⊔ w ⊔ suc 𝓁) where
    field
      toFun : Pred M 𝓁 → Substructure 𝓁
      gc    : (s : Pred M 𝓁) (S : Substructure 𝓁) → toFun s ≤ S ⇔ s ⊆ carrier S

  open LowerAdjoint

  -- The inductive closure is a lower adjoint at every level 𝓁 that contains
  -- u ⊔ w, written u ⊔ w ⊔ p, since Sg maps Pred M 𝓁 into Pred M 𝓁 there.
  -- The infimum is a lower adjoint at no level: it maps Pred M p into
  -- Pred M (u ⊔ w ⊔ suc p).

  closure : (p : Level) → LowerAdjoint (u ⊔ w ⊔ p)
  closure _ = record { toFun = closureₛ ; gc = λ s S → closureₛ-le {s = s} {S} }

  -- The theorem, as Lean states it:
  --
  --     closure_le : (closure L).toFun s ≤ S ↔ s ⊆ ↑S

  closure-le : {p : Level} {S : Substructure (u ⊔ w ⊔ p)} {s : Pred M (u ⊔ w ⊔ p)}
             → toFun (closure p) s ≤ S ⇔ s ⊆ carrier S
  closure-le {p} {S} {s} = gc (closure p) s S

  ----------------------------------------------------------------------
  -- The two closures agree

  -- Each closure is contained in the other whenever the infimum ranges over
  -- the level at which Sg s lives, which is u ⊔ w ⊔ p for s at that level.

  sg⊆inf : {p : Level} {s : Pred M p} → closureₛ s ≤ closureᵢ s
  sg⊆inf {s = s} = sg-smallest (closureᵢ s) (λ x∈s T s⊆T → s⊆T x∈s)

  inf⊆sg : {p : Level} {s : Pred M (u ⊔ w ⊔ p)} → closureᵢ s ≤ closureₛ s
  inf⊆sg {s = s} x∈cl = x∈cl (closureₛ s) var

------------------------------------------------------------------------
-- Languages as agda-algebras's signatures

-- agda-algebras (src/Legacy/Base/Structures/Basic.lagda.md) has a signature
-- as a type of symbols with an arity type for each, and a structure as a
-- carrier with an operation for each symbol of one signature and a relation
-- for each symbol of another:
--
--     record signature (𝓞 𝓥 : Level) : Type (suc (𝓞 ⊔ 𝓥)) where
--       field symbol : Type 𝓞 ; arity : symbol → Type 𝓥
--
-- A Mathlib language is the pair of signatures whose symbols are the pairs
-- of an arity n and a symbol of that arity, and whose arity types are Fin n.
-- The converse direction does not exist in general: agda-algebras allows any
-- type as an arity, infinitary operations included, and a Mathlib language
-- only Fin n.

record Signature (𝓞 𝓥 : Level) : Set (suc (𝓞 ⊔ 𝓥)) where
  field
    symbol : Set 𝓞
    arity  : symbol → Set 𝓥

functions relations : {u v : Level} → Language u v → Signature _ 0ℓ
functions L = record { symbol = Σ ℕ (Functions L) ; arity = Fin ∘ proj₁ }
relations L = record { symbol = Σ ℕ (Relations L) ; arity = Fin ∘ proj₁ }

-- An L-structure gives the operations of an agda-algebras structure over
-- the signature `functions L`, and its substructures are exactly
-- agda-algebras's subuniverses (Subuniverses B = ∀ f a → Im a ⊆ B →
-- (f ᵒ 𝑨) a ∈ B), symbol by symbol.

module _ {u v w ρ : Level} {L : Language u v} {M : Set w}
         ⦃ 𝑴 : Structure L ρ M ⦄ where
  open Structure 𝑴
  open Signature (functions L)

  op : (f : symbol) → (arity f → M) → M
  op (_ , f) = funMap f

  Subuniverses : {p : Level} → Pred M p → Set (u ⊔ w ⊔ p)
  Subuniverses B = (f : symbol) (a : arity f → M) → (∀ i → a i ∈ B) → op f a ∈ B

  substructure→subuniverse : {p : Level} (S : Substructure p)
                           → Subuniverses (Substructure.carrier S)
  substructure→subuniverse S (_ , f) = Substructure.fun-mem S f

  subuniverse→substructure : {p : Level} (B : Pred M p) → Subuniverses B
                           → Substructure p
  subuniverse→substructure B isSub =
    record { carrier = B ; fun-mem = λ f → isSub (_ , f) }
