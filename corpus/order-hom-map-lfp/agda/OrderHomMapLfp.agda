{-# OPTIONS --safe --cubical-compatible #-}

-- File: corpus/order-hom-map-lfp/agda/OrderHomMapLfp.agda
--
-- Mathlib's OrderHom.map_lfp (Mathlib.Order.FixedPoints, Mathlib v4.33.1),
-- the fixed-point half of Knaster and Tarski:
--
--     theorem map_lfp : f f.lfp = f.lfp :=
--       have h : f f.lfp ≤ f.lfp := f.map_le_lfp le_rfl
--       h.antisymm <| f.lfp_le <| f.mono h
--
-- for a monotone map f of a complete lattice, where lfp f = sInf {a | f a ≤ a}.
-- Lean's complete lattice takes the infimum of every subset, and a subset
-- of α is a predicate α → Prop, a small type because Lean's Prop is
-- impredicative.  Here a subset is a predicate into Ω ℓ, and the lattice is
-- complete for the predicates of one level, the level ℓ of its order (see
-- ../notes.md).  No classical principle and no extensionality is needed.

module OrderHomMapLfp where

open import Level using (Level; _⊔_; suc)
open import Data.Product.Base using (Σ; _,_; proj₁)
open import Relation.Nullary.Irrelevant using (Irrelevant)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

private
  variable
    a b ℓ ℓ′ : Level
    A : Set a
    B : Set b

-- Lean's Prop, read as the propositions among the types of Set p, as in the
-- corpus entries multiset-map-map and set-ext; and Lean's Set α := α → Prop,
-- the ℙ of set-ext.

Ω : (p : Level) → Set (suc p)
Ω p = Σ (Set p) Irrelevant

ℙ : Set a → (p : Level) → Set (a ⊔ suc p)
ℙ A p = A → Ω p

_∈_ : {p : Level} → A → ℙ A p → Set p
x ∈ S = proj₁ (S x)

-- Lean's classes, as records, with the fields the theorem's proof uses.
-- Lean's Preorder also has lt and lt_iff_le_not_ge, and its CompleteLattice
-- has 22 fields, sup, inf, sSup, top and bot with their laws among them
-- (../notes.md, Instance arguments); a structure with fewer fields is a
-- weaker hypothesis, so the theorem below implies Lean's for every Lean
-- instance.

record Preorder (A : Set a) (ℓ : Level) : Set (a ⊔ suc ℓ) where
  infix 4 _≤_
  field
    _≤_     : A → A → Set ℓ
    ≤-refl  : (x : A) → x ≤ x
    ≤-trans : {x y z : A} → x ≤ y → y ≤ z → x ≤ z

record PartialOrder (A : Set a) (ℓ : Level) : Set (a ⊔ suc ℓ) where
  field
    preorder : Preorder A ℓ
  open Preorder preorder public
  field
    ≤-antisym : {x y : A} → x ≤ y → y ≤ x → x ≡ y

-- The infimum of a subset, sInf, with its law.  Lean's law is one field,
-- isGLB_sInf s : IsGLB s (sInf s), that sInf s is the greatest element of
-- lowerBounds s = {x | ∀ ⦃a⦄, a ∈ s → x ≤ a}; its two halves, Lean's lemmas
-- sInf_le and le_sInf, are the two fields ⋀-lower and ⋀-greatest here.
-- ≤-prop says that x ≤ y is a proposition, as Lean's Prop-valued order is,
-- so that {x | f x ≤ x} is a subset in ℙ A ℓ.  The level of the subsets ⋀
-- accepts is the level of the order: Lean's one sInf for every subset
-- becomes one ⋀ for the subsets of that level.

record CompleteLattice (A : Set a) (ℓ : Level) : Set (a ⊔ suc ℓ) where
  field
    partialOrder : PartialOrder A ℓ
  open PartialOrder partialOrder public
  field
    ≤-prop     : {x y : A} → Irrelevant (x ≤ y)
    ⋀          : ℙ A ℓ → A
    ⋀-lower    : {S : ℙ A ℓ} {x : A} → x ∈ S → ⋀ S ≤ x
    ⋀-greatest : {S : ℙ A ℓ} {y : A} → ((x : A) → x ∈ S → y ≤ x) → y ≤ ⋀ S

-- Lean's OrderHom α β, the bundled monotone maps between two preorders,
-- with its fields toFun and monotone'.  Lean applies a bundled map through
-- the coercion DFunLike.coe and the instance OrderHom.instFunLike, which
-- unfold to the projection toFun; here _⟨$⟩_ is that projection.

record OrderHom {A : Set a} {B : Set b} (P : Preorder A ℓ) (Q : Preorder B ℓ′)
                : Set (a ⊔ b ⊔ ℓ ⊔ ℓ′) where
  field
    toFun    : A → B
    monotone : {x y : A} → Preorder._≤_ P x y → Preorder._≤_ Q (toFun x) (toFun y)

open OrderHom

_⟨$⟩_ : {P : Preorder A ℓ} {Q : Preorder B ℓ′} → OrderHom P Q → A → B
_⟨$⟩_ = toFun

infixl 5 _⟨$⟩_

-- Lean's instance OrderHom.instPreorder: bundled maps ordered pointwise.
-- The order on maps quantifies over A, so it lives at a ⊔ ℓ′, above the
-- order of the target; Lean's lives in Prop like every other.

pointwise : {A : Set a} {B : Set b} (P : Preorder A ℓ) (Q : Preorder B ℓ′)
          → Preorder (OrderHom P Q) (a ⊔ ℓ′)
pointwise P Q = record
  { _≤_     = λ f g → ∀ x → f ⟨$⟩ x ≤ g ⟨$⟩ x
  ; ≤-refl  = λ f x → ≤-refl (f ⟨$⟩ x)
  ; ≤-trans = λ f≤g g≤h x → ≤-trans (f≤g x) (g≤h x)
  }
  where open Preorder Q

module _ (L : CompleteLattice A ℓ) where
  open CompleteLattice L

  -- Lean: def lfp : (α →o α) →o α where
  --         toFun f := sInf { a | f a ≤ a }
  --         monotone' _ _ hle := sInf_le_sInf fun a ha => (hle a).trans ha

  lfp : OrderHom (pointwise preorder preorder) preorder
  lfp = record
    { toFun    = λ f → ⋀ (λ x → (f ⟨$⟩ x ≤ x) , ≤-prop)
    ; monotone = λ f≤g → ⋀-greatest (λ x gx≤x → ⋀-lower (≤-trans (f≤g x) gx≤x))
    }

  module _ (f : OrderHom preorder preorder) where

    lfp-le : {x : A} → f ⟨$⟩ x ≤ x → lfp ⟨$⟩ f ≤ x
    lfp-le = ⋀-lower

    le-lfp : {x : A} → ((y : A) → f ⟨$⟩ y ≤ y → x ≤ y) → x ≤ lfp ⟨$⟩ f
    le-lfp = ⋀-greatest

    -- Lean: f.le_lfp fun _ hb => (f.mono <| le_sInf_iff.1 ha _ hb).trans hb.
    -- The step le_sInf_iff.1 ha _ hb : a ≤ b is ≤-trans ha (lfp-le hb) here.

    map-le-lfp : {x : A} → x ≤ lfp ⟨$⟩ f → f ⟨$⟩ x ≤ lfp ⟨$⟩ f
    map-le-lfp x≤lfp = le-lfp (λ y fy≤y → ≤-trans (monotone f (≤-trans x≤lfp (lfp-le fy≤y))) fy≤y)

    -- The theorem, by Lean's proof.

    map-lfp : f ⟨$⟩ (lfp ⟨$⟩ f) ≡ lfp ⟨$⟩ f
    map-lfp = ≤-antisym h (lfp-le (monotone f h))
      where
      h : f ⟨$⟩ (lfp ⟨$⟩ f) ≤ lfp ⟨$⟩ f
      h = map-le-lfp (≤-refl (lfp ⟨$⟩ f))
