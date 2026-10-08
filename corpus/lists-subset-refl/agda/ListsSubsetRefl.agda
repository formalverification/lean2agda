{-# OPTIONS --safe --cubical-compatible #-}

-- File: corpus/lists-subset-refl/agda/ListsSubsetRefl.agda
--
-- Mathlib's Lists'.Subset.refl (Mathlib.SetTheory.Lists, Mathlib v4.33.1):
--
--     @[refl]
--     theorem Subset.refl {l : Lists' α true} : l ⊆ l := by
--       rw [← Lists'.of_toList l]; exact ofList_subset (List.Subset.refl _)
--
-- with the definitions it needs: the Bool-indexed family Lists', the sum
-- Lists, and the mutual block of Lists.Equiv and Lists'.Subset.  The
-- statement is proved twice: by induction on the list, the idiomatic
-- proof, and through of_toList and ofList_subset, the way Lean's kernel
-- term does, for comparison.  Lean's recursor for the mutual block follows,
-- written by mutual pattern matching (see ../notes.md).

module ListsSubsetRefl where

open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Data.Bool.Base using (Bool; true; false)
import Data.Bool.Properties as Bool
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Subset.Propositional
  renaming (_⊆_ to _⊆ᴸ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product.Base using (Σ; _,_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; sym; subst)

private
  variable
    a ℓ : Level
    A : Set a

------------------------------------------------------------------------
-- The definitions

-- Lean's inductive Lists'.{u} (α : Type u) : Bool → Type u.  The index
-- false holds the atoms and true the proper lists.

data Lists′ (A : Set a) : Bool → Set a where
  atom  : A → Lists′ A false
  nil   : Lists′ A true
  cons′ : {b : Bool} → Lists′ A b → Lists′ A true → Lists′ A true

-- Lean's Lists α := Σ b, Lists' α b, in Type (max 0 u), which is Set a.

Lists : Set a → Set a
Lists A = Σ Bool (Lists′ A)

cons : Lists A → Lists′ A true → Lists′ A true
cons (_ , x) l = cons′ x l

toList : {b : Bool} → Lists′ A b → List (Lists A)
toList (atom _)    = []
toList nil         = []
toList (cons′ x l) = (_ , x) ∷ toList l

ofList : List (Lists A) → Lists′ A true
ofList []      = nil
ofList (x ∷ l) = cons x (ofList l)

-- Lean's mutual block of two inductive propositions.  In Agda both live
-- in Set a, and the membership a′ ∈ toList l′, Lean's List.Mem, is
-- agda-stdlib's _∈_, that is, Any (a′ ≡_).  Lean's constructors are
-- Lists.Equiv.refl, Lists.Equiv.antisymm, Lists'.Subset.nil and
-- Lists'.Subset.cons; the last two are renamed ⊆-nil and ⊆-cons, since
-- Agda would not tell the constructor cons from the function cons.  The
-- constructor refl shares its name with that of _≡_, and Agda tells the
-- two apart by the expected type.

mutual
  data Equiv {A : Set a} : Lists A → Lists A → Set a where
    refl     : (l : Lists A) → Equiv l l
    antisymm : {l₁ l₂ : Lists′ A true} →
               l₁ ⊆ l₂ → l₂ ⊆ l₁ → Equiv (true , l₁) (true , l₂)

  data _⊆_ {A : Set a} : Lists′ A true → Lists′ A true → Set a where
    ⊆-nil  : {l : Lists′ A true} → nil ⊆ l
    ⊆-cons : {x x′ : Lists A} {l l′ : Lists′ A true} →
             Equiv x x′ → x′ ∈ toList l′ → l ⊆ l′ → cons x l ⊆ l′

------------------------------------------------------------------------
-- The idiomatic proof

-- Weakening, by induction on the proof of l ⊆ l′.  In Lean this would be
-- an induction through Lists'.Subset.rec, whose motive for Lists.Equiv
-- would have to be supplied too; here the Equiv proof is only carried.

⊆-weaken : {l l′ : Lists′ A true} {b : Bool} {x : Lists′ A b} →
           l ⊆ l′ → l ⊆ cons′ x l′
⊆-weaken ⊆-nil          = ⊆-nil
⊆-weaken (⊆-cons e m s) = ⊆-cons e (there m) (⊆-weaken s)

-- Reflexivity, by induction on the list, matched at index true directly:
-- the case atom is excluded because false and true are different
-- constructors, and no K is needed.  Agda 2.8.0 warns here under
-- --cubical-compatible (UnsupportedIndexedMatch: the clauses rely on the
-- injectivity of true in an index, so they will not compute on transports
-- in Cubical Agda); agda-stdlib and the cubical library turn that warning
-- off for all their modules.

⊆-refl : (l : Lists′ A true) → l ⊆ l
⊆-refl nil         = ⊆-nil
⊆-refl (cons′ x l) = ⊆-cons (refl _) (here refl) (⊆-weaken (⊆-refl l))

------------------------------------------------------------------------
-- The direct proof

-- Lean's of_toList.  Lean's induction tactic needs the index of
-- Lists' α true to be a variable, so Mathlib generalizes it to
-- ∀ b (h : true = b) (l : Lists' α b) and transports l along h.  In the
-- cases nil and cons' the proof h : true = true is a variable, and Lean's
-- kernel removes the transport by K-like reduction.  K is not available
-- here; Bool has decidable equality, so by Hedberg's theorem (agda-stdlib's
-- Decidable⇒UIP) any two proofs of true ≡ true are equal, and transport
-- along one is the identity.

open Decidable⇒UIP Bool._≟_ using () renaming (≡-irrelevant to Bool-UIP)

subst-true : (h : true ≡ true) (l : Lists′ A true) → subst (Lists′ A) h l ≡ l
subst-true {A = A} h l = cong (λ h → subst (Lists′ A) h l) (Bool-UIP h refl)

-- The generalized statement, with Lean's let l' := h.symm ▸ l.  The case
-- atom is excluded because h : true ≡ false is absurd.

of-toList-gen : {b : Bool} (h : true ≡ b) (l : Lists′ A b) →
                let l′ = subst (Lists′ A) (sym h) l in ofList (toList l′) ≡ l′
of-toList-gen () (atom _)
of-toList-gen h nil =
  subst (λ l′ → ofList (toList l′) ≡ l′) (sym (subst-true (sym h) nil)) refl
of-toList-gen h (cons′ x l) =
  subst (λ l′ → ofList (toList l′) ≡ l′) (sym (subst-true (sym h) (cons′ x l)))
        (cong (cons′ x) (of-toList-gen refl l))

of-toList : (l : Lists′ A true) → ofList (toList l) ≡ l
of-toList = of-toList-gen refl

-- Lean's to_ofList, which ofList_subset uses to place an element.  The
-- step holds by computation only because of eta for pairs: cons x l is
-- cons′ (proj₂ x) l, so toList (cons x l) is (proj₁ x , proj₂ x) ∷ toList l,
-- which is x ∷ toList l because Σ is a record with eta.  Lean's kernel
-- takes the same step by structure eta for Sigma.

to-ofList : (xs : List (Lists A)) → toList (ofList xs) ≡ xs
to-ofList []       = refl
to-ofList (x ∷ xs) = cong (x ∷_) (to-ofList xs)

-- Lean's ofList_subset, by induction on the first list, with
-- agda-stdlib's list inclusion _⊆ᴸ_ for Lean's List.Subset.

ofList-⊆ : {xs ys : List (Lists A)} → xs ⊆ᴸ ys → ofList xs ⊆ ofList ys
ofList-⊆ {xs = []}     h = ⊆-nil
ofList-⊆ {xs = x ∷ xs} {ys} h =
  ⊆-cons (refl x) (subst (x ∈_) (sym (to-ofList ys)) (h (here refl)))
         (ofList-⊆ (λ i → h (there i)))

-- Lean's Subset.refl: rewrite l as ofList (toList l), and apply
-- ofList_subset to List.Subset.refl, which is the identity on membership
-- proofs.

⊆-refl-direct : (l : Lists′ A true) → l ⊆ l
⊆-refl-direct l = subst (λ l → l ⊆ l) (of-toList l) (ofList-⊆ (λ i → i))

------------------------------------------------------------------------
-- The mutual recursor

-- Lean's recursor for the block, Lists'.Subset.rec, takes two motives,
-- one per type, and a minor premise per constructor of either type;
-- Lists.Equiv.rec takes the same arguments and differs in its target.
-- Because the block is a pair of propositions, Lean's motives must land in
-- Prop.  Mutual pattern matching gives both recursors at once, with
-- motives in any Set ℓ.  The kernel term of Subset.refl never applies
-- either recursor; this is how a term that did would translate.

module _ {A : Set a}
  (P : {x x′ : Lists A} → Equiv x x′ → Set ℓ)
  (Q : {l l′ : Lists′ A true} → l ⊆ l′ → Set ℓ)
  (p-refl     : (x : Lists A) → P (refl x))
  (p-antisymm : {l₁ l₂ : Lists′ A true} (s : l₁ ⊆ l₂) (t : l₂ ⊆ l₁) →
                Q s → Q t → P (antisymm s t))
  (q-nil      : {l : Lists′ A true} → Q (⊆-nil {l = l}))
  (q-cons     : {x x′ : Lists A} {l l′ : Lists′ A true}
                (e : Equiv x x′) (m : x′ ∈ toList l′) (s : l ⊆ l′) →
                P e → Q s → Q (⊆-cons e m s))
  where

  mutual
    Equiv-rec : {x x′ : Lists A} (e : Equiv x x′) → P e
    Equiv-rec (refl x)       = p-refl x
    Equiv-rec (antisymm s t) = p-antisymm s t (Subset-rec s) (Subset-rec t)

    Subset-rec : {l l′ : Lists′ A true} (s : l ⊆ l′) → Q s
    Subset-rec ⊆-nil          = q-nil
    Subset-rec (⊆-cons e m s) = q-cons e m s (Equiv-rec e) (Subset-rec s)
