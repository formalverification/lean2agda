{-# OPTIONS --safe --cubical-compatible #-}

-- File: corpus/finset-card-image/agda/FinsetCardImage.agda
--
-- Mathlib's Finset.card_image_of_injective (Mathlib.Data.Finset.Card,
-- Mathlib v4.33.1):
--
--     theorem card_image_of_injective [DecidableEq β] (s : Finset α) (H : Injective f) :
--         #(s.image f) = #s :=
--       card_image_of_injOn fun _ _ _ _ h => H h
--
-- under profile CC.  Lean's Finset α is a structure of a multiset and a
-- proof that it has no duplicates, and its Multiset α is the quotient of
-- List α by permutation; here the quotient primitives, propositional
-- extensionality and function extensionality are module parameters, in the
-- shape of the corpus entries multiset-map-map and set-ext.  The decidable
-- equality of β is a hypothesis in Lean's statement and a module parameter
-- here.  No classical principle is needed: Lean's proof is T2 only through
-- lemmas proved classically, and their constructive proofs are below (see
-- ../notes.md).

module FinsetCardImage where

open import Level using (Level; _⊔_; suc; Setω)
open import Function.Base using (_∘_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Function.Definitions using (Injective)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using () renaming (≡-irrelevant to ℕ-uip)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.List.Base using (List; []; _∷_; length; filter; deduplicate)
import Data.List.Base as List
open import Data.List.Properties using (length-map; filter-all; filter-accept; filter-reject)
open import Data.List.Relation.Unary.All using ([]; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
import Data.List.Relation.Unary.AllPairs as AllPairs
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as Unique
import Data.List.Relation.Unary.Unique.DecPropositional.Properties as UniqueDec
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-sym)
import Data.List.Relation.Binary.Permutation.Propositional as ↭
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (map⁺; ↭-length; filter-↭; All-resp-↭)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary.Decidable.Core using (Dec; _because_; ¬?)
open import Relation.Nullary.Reflects using (invert)
open import Data.Bool.Base using (true; false)
open import Relation.Nullary.Irrelevant using (Irrelevant)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Axiom.UniquenessOfIdentityProofs using (UIP; module Constant⇒UIP)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)

private
  variable
    a b p q : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- The parameters, as in multiset-map-map and set-ext

-- Lean's Prop, read as the propositions among the types of Set p: a type
-- with a proof that any two of its elements are equal.

Ω : (p : Level) → Set (suc p)
Ω p = Σ (Set p) Irrelevant

-- Lean's quotient primitives, the record of multiset-map-map: ind's motive
-- takes values in Ω, lift asks that its target be a set, squash says that
-- every quotient is one, and lift-β is the computation rule that Lean's
-- kernel applies by reduction (../../multiset-map-map/notes.md).

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
    lift-β : {a r b : Level} {A : Set a} {R : A → A → Set r} {B : Set b}
           → (uip : UIP B) (f : A → B) (h : ∀ x y → R x y → f x ≡ f y)
           → (x : A) → lift uip f h (mk R x) ≡ f x

-- Lean's axiom propext over Ω, and Lean's funext, the records of set-ext.

record PropExt : Setω where
  field
    propext : {p : Level} {P Q : Ω p} → proj₁ P ⇔ proj₁ Q → P ≡ Q

record FunExt : Setω where
  field
    funext : {a b : Level} → Extensionality a b

------------------------------------------------------------------------
-- Lists: Lean's List.Nodup and List.dedup, constructively

-- Lean's List.Nodup is Pairwise (· ≠ ·); agda-stdlib's Unique is
-- AllPairs _≢_, the same relation.  Lean's List.Perm.nodup_iff:

--
-- The proof takes Unique's components apart with head and tail rather than
-- by patterns: a pattern at the index x ∷ xs makes Agda warn
-- UnsupportedIndexedMatch under --cubical-compatible.

Unique-resp-↭ : {xs ys : List A} → xs ↭ ys → Unique xs → Unique ys
Unique-resp-↭ ↭.refl u = u
Unique-resp-↭ (↭.prep x xs↭ys) u =
  All-resp-↭ xs↭ys (AllPairs.head u) ∷ Unique-resp-↭ xs↭ys (AllPairs.tail u)
Unique-resp-↭ (↭.swap x y xs↭ys) u =
  (All.head x∉ ∘ sym ∷ All-resp-↭ xs↭ys (AllPairs.head u′))
  ∷ All-resp-↭ xs↭ys (All.tail x∉) ∷ Unique-resp-↭ xs↭ys (AllPairs.tail u′)
  where
  x∉ = AllPairs.head u
  u′ = AllPairs.tail u
Unique-resp-↭ (↭.trans xs↭ys ys↭zs) u = Unique-resp-↭ ys↭zs (Unique-resp-↭ xs↭ys u)

-- Two filters commute.  The case split is on the Boolean field of each
-- decision, with invert for its proof: the patterns yes and no match the
-- indexed family Reflects, which makes Agda warn as above.

module _ {P : Pred A p} {Q : Pred A q} (P? : Decidable P) (Q? : Decidable Q) where

  filter-comm : (xs : List A) → filter P? (filter Q? xs) ≡ filter Q? (filter P? xs)
  filter-comm []       = refl
  filter-comm (x ∷ xs) = by-cases (P? x) (Q? x)
    where
    open ≡-Reasoning
    ih = filter-comm xs
    by-cases : Dec (P x) → Dec (Q x)
             → filter P? (filter Q? (x ∷ xs)) ≡ filter Q? (filter P? (x ∷ xs))
    by-cases (true because px) (true because qx) = begin
      filter P? (filter Q? (x ∷ xs))  ≡⟨ cong (filter P?) (filter-accept Q? (invert qx)) ⟩
      filter P? (x ∷ filter Q? xs)    ≡⟨ filter-accept P? (invert px) ⟩
      x ∷ filter P? (filter Q? xs)    ≡⟨ cong (x ∷_) ih ⟩
      x ∷ filter Q? (filter P? xs)    ≡⟨ filter-accept Q? (invert qx) ⟨
      filter Q? (x ∷ filter P? xs)    ≡⟨ cong (filter Q?) (filter-accept P? (invert px)) ⟨
      filter Q? (filter P? (x ∷ xs))  ∎
    by-cases (true because px) (false because ¬qx) = begin
      filter P? (filter Q? (x ∷ xs))  ≡⟨ cong (filter P?) (filter-reject Q? (invert ¬qx)) ⟩
      filter P? (filter Q? xs)        ≡⟨ ih ⟩
      filter Q? (filter P? xs)        ≡⟨ filter-reject Q? (invert ¬qx) ⟨
      filter Q? (x ∷ filter P? xs)    ≡⟨ cong (filter Q?) (filter-accept P? (invert px)) ⟨
      filter Q? (filter P? (x ∷ xs))  ∎
    by-cases (false because ¬px) (true because qx) = begin
      filter P? (filter Q? (x ∷ xs))  ≡⟨ cong (filter P?) (filter-accept Q? (invert qx)) ⟩
      filter P? (x ∷ filter Q? xs)    ≡⟨ filter-reject P? (invert ¬px) ⟩
      filter P? (filter Q? xs)        ≡⟨ ih ⟩
      filter Q? (filter P? xs)        ≡⟨ cong (filter Q?) (filter-reject P? (invert ¬px)) ⟨
      filter Q? (filter P? (x ∷ xs))  ∎
    by-cases (false because ¬px) (false because ¬qx) = begin
      filter P? (filter Q? (x ∷ xs))  ≡⟨ cong (filter P?) (filter-reject Q? (invert ¬qx)) ⟩
      filter P? (filter Q? xs)        ≡⟨ ih ⟩
      filter Q? (filter P? xs)        ≡⟨ cong (filter Q?) (filter-reject P? (invert ¬px)) ⟨
      filter Q? (filter P? (x ∷ xs))  ∎

-- Lean's List.dedup is pwFilter (· ≠ ·), which keeps the last copy of each
-- element; agda-stdlib's deduplicate keeps the first.  The two results are
-- permutations of each other, so they are the same multiset.

module _ (_≟_ : DecidableEquality A) where

  private
    dedup : List A → List A
    dedup = deduplicate _≟_

    -- The filter in deduplicate's second clause: the elements other than x.
    ≢? : (x : A) → Decidable (x ≢_)
    ≢? x = ¬? ∘ (x ≟_)

  -- Lean's List.dedup_eq_self, one direction: a list without duplicates
  -- is its own deduplication.

  dedup-unique : {xs : List A} → Unique xs → dedup xs ≡ xs
  dedup-unique [] = refl
  dedup-unique {x ∷ xs} (x∉ ∷ u) =
    cong (x ∷_) (trans (cong (filter (≢? x)) (dedup-unique u)) (filter-all (≢? x) x∉))

  -- Lean's List.Perm.dedup, by induction on the permutation.  Lean proves
  -- it through List.perm_iff_count, whose `by_cases h : b = a` falls back
  -- on Classical.propDecidable; here the case split is on _≟_.

  dedup-↭ : {xs ys : List A} → xs ↭ ys → dedup xs ↭ dedup ys
  dedup-↭ ↭.refl = ↭.refl
  dedup-↭ (↭.prep x xs↭ys) = ↭.prep x (filter-↭ (≢? x) (dedup-↭ xs↭ys))
  dedup-↭ (↭.trans xs↭ys ys↭zs) = ↭.trans (dedup-↭ xs↭ys) (dedup-↭ ys↭zs)
  dedup-↭ (↭.swap {xs = xs} {ys = ys} x y xs↭ys) = by-cases (x ≟ y)
    where
    D = dedup xs
    E = dedup ys
    ih : D ↭ E
    ih = dedup-↭ xs↭ys

    by-cases : Dec (x ≡ y) → dedup (x ∷ y ∷ xs) ↭ dedup (y ∷ x ∷ ys)
    by-cases (true because x≡y) =
      subst (λ z → dedup (x ∷ z ∷ xs) ↭ dedup (z ∷ x ∷ ys)) (invert x≡y)
            (↭.prep x (filter-↭ (≢? x) (↭.prep x (filter-↭ (≢? x) ih))))
    by-cases (false because x≢y) =
      ↭.trans (↭.↭-reflexive left) (↭.trans middle (↭.↭-reflexive (sym right)))
      where
      left : dedup (x ∷ y ∷ xs) ≡ x ∷ y ∷ filter (≢? x) (filter (≢? y) D)
      left = cong (x ∷_) (filter-accept (≢? x) (invert x≢y))
      right : dedup (y ∷ x ∷ ys) ≡ y ∷ x ∷ filter (≢? y) (filter (≢? x) E)
      right = cong (y ∷_) (filter-accept (≢? y) (invert x≢y ∘ sym))
      middle : x ∷ y ∷ filter (≢? x) (filter (≢? y) D) ↭ y ∷ x ∷ filter (≢? y) (filter (≢? x) E)
      middle = ↭.swap x y (↭.trans (filter-↭ (≢? x) (filter-↭ (≢? y) ih))
                                   (↭.↭-reflexive (filter-comm (≢? x) (≢? y) E)))

------------------------------------------------------------------------
-- Multisets and finite sets

module _ (Q : Quotients) (pe : PropExt) (fe : FunExt) where
  open Quotients Q
  open PropExt pe
  open FunExt fe

  -- Ω p is a set: Hedberg's argument, since every equation P ≡ Q has a
  -- constant endomap, through propext.  Lean has this for every type; here
  -- it is what lets Multiset.Nodup lift into Ω.

  Ω-uip : UIP (Ω p)
  Ω-uip = Constant⇒UIP.≡-irrelevant f f-constant
    where
    f : {P Q : Ω _} → P ≡ Q → P ≡ Q
    f e = propext (mk⇔ (subst proj₁ e) (subst proj₁ (sym e)))
    f-constant : {P Q : Ω _} (e e′ : P ≡ Q) → f e ≡ f e′
    f-constant {P} {Q} e e′ =
      cong propext (cong₂ mk⇔ (funext λ _ → proj₂ Q _ _) (funext λ _ → proj₂ P _ _))

  -- Unique xs is a proposition: its proofs are lists of functions into ⊥,
  -- equal by funext.

  Unique-irrelevant : (xs : List A) → Irrelevant (Unique xs)
  Unique-irrelevant xs = AllPairs.irrelevant (λ u v → funext λ e → ⊥-elim (u e))

  -- Lean: def Multiset (α) := Quotient (List.isSetoid α), as in
  -- multiset-map-map, and Multiset.ofList, the coercion ↑, as ⟦_⟧.

  Multiset : Set a → Set a
  Multiset A = Quot (_↭_ {A = A})

  ⟦_⟧ : List A → Multiset A
  ⟦_⟧ = mk _↭_

  -- Lean: def map (f : α → β) (s : Multiset α) : Multiset β :=
  --         Quot.liftOn s (fun l : List α => (l.map f : Multiset β)) fun _l₁ _l₂ p => Quot.sound (p.map f)

  map : (A → B) → Multiset A → Multiset B
  map f = lift squash (λ l → ⟦ List.map f l ⟧) (λ _ _ p → sound (map⁺ f p))

  map-β : (f : A → B) (l : List A) → map f ⟦ l ⟧ ≡ ⟦ List.map f l ⟧
  map-β f = lift-β squash (λ l → ⟦ List.map f l ⟧) (λ _ _ p → sound (map⁺ f p))

  -- Lean: def card : Multiset α → ℕ := Quot.lift length fun _l₁ _l₂ => Perm.length_eq

  card : Multiset A → ℕ
  card = lift ℕ-uip length (λ _ _ → ↭-length)

  card-β : (l : List A) → card ⟦ l ⟧ ≡ length l
  card-β = lift-β ℕ-uip length (λ _ _ → ↭-length)

  -- Lean: def Nodup (s : Multiset α) : Prop :=
  --         Quot.liftOn s List.Nodup fun _ _ p => propext p.nodup_iff
  --
  -- a lift into Prop, which here is a lift into Ω a, whose target is a set by
  -- Ω-uip and whose respect proof is propext, as in Lean.

  Nodup : Multiset A → Ω _
  Nodup = lift Ω-uip (λ l → Unique l , Unique-irrelevant l)
               (λ _ _ p → propext (mk⇔ (Unique-resp-↭ p) (Unique-resp-↭ (↭-sym p))))

  IsNodup : {A : Set a} → Multiset A → Set a
  IsNodup m = proj₁ (Nodup m)

  -- What Lean has by computation, Nodup ↑l reducing to l.Nodup, is a
  -- transport along lift-β here, in each direction.

  nodup⁻ : {l : List A} → IsNodup ⟦ l ⟧ → Unique l
  nodup⁻ {l = l} = subst proj₁ (lift-β Ω-uip _ _ l)

  nodup⁺ : {l : List A} → Unique l → IsNodup ⟦ l ⟧
  nodup⁺ {l = l} = subst proj₁ (sym (lift-β Ω-uip _ _ l))

  -- Lean: structure Finset (α : Type*) where
  --         val : Multiset α
  --         nodup : Nodup val

  record Finset (A : Set a) : Set a where
    constructor mkFinset
    field
      val   : Multiset A
      nodup : IsNodup val

  open Finset

  -- Lean: def card (s : Finset α) : ℕ := Multiset.card s.1, written #s.

  #_ : Finset A → ℕ
  # s = card (val s)

  -- Lean: theorem card_map (f : α → β) (s) : card (map f s) = card s :=
  --         Quot.inductionOn s fun _ => length_map _
  --
  -- Lean's kernel reduces Quot.lift three times to check it; each
  -- reduction is a rewrite by map-β or card-β here.

  card-map : (f : A → B) (m : Multiset A) → card (map f m) ≡ card m
  card-map f = ind {P = λ m → (card (map f m) ≡ card m) , ℕ-uip} step
    where
    open ≡-Reasoning
    step : (l : List _) → card (map f ⟦ l ⟧) ≡ card ⟦ l ⟧
    step l = begin
      card (map f ⟦ l ⟧)       ≡⟨ cong card (map-β f l) ⟩
      card ⟦ List.map f l ⟧    ≡⟨ card-β (List.map f l) ⟩
      length (List.map f l)    ≡⟨ length-map f l ⟩
      length l                 ≡⟨ card-β l ⟨
      card ⟦ l ⟧               ∎

  -- Lean's Multiset.Nodup.map: an injective map keeps a multiset free of
  -- duplicates.  The motive is an implication, a proposition by funext.

  nodup-map : {f : A → B} → Injective _≡_ _≡_ f
            → (m : Multiset A) → IsNodup m → IsNodup (map f m)
  nodup-map {f = f} inj = ind {P = λ m → (IsNodup m → IsNodup (map f m)) , irr m} step
    where
    irr : (m : Multiset _) → Irrelevant (IsNodup m → IsNodup (map f m))
    irr m g h = funext λ n → proj₂ (Nodup (map f m)) (g n) (h n)
    step : (l : List _) → IsNodup ⟦ l ⟧ → IsNodup (map f ⟦ l ⟧)
    step l n = subst IsNodup (sym (map-β f l)) (nodup⁺ (Unique.map⁺ inj (nodup⁻ n)))

  -- The decidable equality of β, Lean's instance argument [DecidableEq β],
  -- is a module parameter, as Mathlib's `variable [DecidableEq β]` is a
  -- section variable.

  module _ (_≟_ : DecidableEquality B) where

    -- Lean: def dedup (s : Multiset α) : Multiset α :=
    --         Quot.liftOn s (fun l => (l.dedup : Multiset α)) fun _ _ p => Quot.sound p.dedup

    dedup : Multiset B → Multiset B
    dedup = lift squash (λ l → ⟦ deduplicate _≟_ l ⟧) (λ _ _ p → sound (dedup-↭ _≟_ p))

    dedup-β : (l : List B) → dedup ⟦ l ⟧ ≡ ⟦ deduplicate _≟_ l ⟧
    dedup-β = lift-β squash (λ l → ⟦ deduplicate _≟_ l ⟧) (λ _ _ p → sound (dedup-↭ _≟_ p))

    -- Lean: theorem nodup_dedup (s : Multiset α) : Nodup (dedup s) :=
    --         Quot.induction_on s fun _ => nodup_dedup _

    nodup-dedup : (m : Multiset B) → IsNodup (dedup m)
    nodup-dedup = ind {P = λ m → Nodup (dedup m)} λ l →
      subst IsNodup (sym (dedup-β l)) (nodup⁺ (UniqueDec.deduplicate-! _≟_ l))

    -- Lean's Multiset.Nodup.dedup: dedup s = s for a multiset without
    -- duplicates.

    dedup-nodup : (m : Multiset B) → IsNodup m → dedup m ≡ m
    dedup-nodup = ind {P = λ m → (IsNodup m → dedup m ≡ m) , irr m} step
      where
      irr : (m : Multiset B) → Irrelevant (IsNodup m → dedup m ≡ m)
      irr m g h = funext λ n → squash (g n) (h n)
      step : (l : List B) → IsNodup ⟦ l ⟧ → dedup ⟦ l ⟧ ≡ ⟦ l ⟧
      step l n = trans (dedup-β l) (cong ⟦_⟧ (dedup-unique _≟_ (nodup⁻ n)))

    -- Lean: def toFinset (s : Multiset α) : Finset α := ⟨_, nodup_dedup s⟩
    --       def image (f : α → β) (s : Finset α) : Finset β := (s.1.map f).toFinset

    toFinset : Multiset B → Finset B
    toFinset m = mkFinset (dedup m) (nodup-dedup m)

    image : (A → B) → Finset A → Finset B
    image f s = toFinset (map f (val s))

    -- The theorem.  Lean's proof is card_image_of_injOn, which rewrites
    -- (image f s).1 to s.1.map f by image_val_of_injOn, that is, by
    -- (s.2.map_on H).dedup, and then applies card_map.  The same two steps
    -- follow, with injectivity in place of injectivity on s.

    card-image-of-injective : {f : A → B} (s : Finset A) → Injective _≡_ _≡_ f
                            → # image f s ≡ # s
    card-image-of-injective {f = f} s inj = begin
      # image f s                     ≡⟨⟩
      card (dedup (map f (val s)))    ≡⟨ cong card (dedup-nodup (map f (val s))
                                                     (nodup-map inj (val s) (nodup s))) ⟩
      card (map f (val s))            ≡⟨ card-map f (val s) ⟩
      card (val s)                    ∎
      where open ≡-Reasoning
