{-# OPTIONS --safe --cubical-compatible #-}

-- File: corpus/subgroup-card-dvd/agda/SubgroupCardDvd.agda
--
-- Mathlib's Subgroup.card_subgroup_dvd_card (Mathlib.GroupTheory.Coset.Card,
-- Mathlib v4.33.1), Lagrange's theorem:
--
--     theorem card_subgroup_dvd_card (s : Subgroup α) : Nat.card s ∣ Nat.card α := by
--       simp [card_eq_card_quotient_mul_card_subgroup s, @dvd_mul_left ℕ]
--
-- under profile CC, with the classical principles Lean's proof uses as module
-- parameters, and Nat.card, which Mathlib defines classically, as one more: a
-- record of a cardinality function with the laws Lean's proof uses.  The
-- proof is Lean's: an equivalence α ≃ (α ⧸ s) × s, built from Lean's
-- quotient and a choice of representative in each coset (Quotient.out), then
-- Nat.card_congr and Nat.card_prod.  SubgroupCardDvdFinite.agda proves the
-- statement for finite groups with no parameters (see ../notes.md).

module SubgroupCardDvd where

open import Level using (Level; _⊔_; Setω) renaming (suc to lsuc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (1↔⊤; 2↔Bool)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Nat.Divisibility.Core using (_∣_; divides)
open import Data.Nat.Properties using (<-cmp)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Function.Bundles using (_↔_; _⇔_; mk↔ₛ′; mk⇔)
open import Function.Properties.Inverse using (↔-sym; ↔-trans)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Nullary.Irrelevant using (Irrelevant)
open import Axiom.UniquenessOfIdentityProofs using (UIP; module Constant⇒UIP)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)

------------------------------------------------------------------------
-- Lean's Prop, and subsets

-- As in the entries set-ext and multiset-map-map: a proposition is a type
-- with a proof that any two of its elements are equal, and Lean's Set α,
-- α → Prop, is ℙ A p.

Ω : (p : Level) → Set (lsuc p)
Ω p = Σ (Set p) Irrelevant

ℙ : {a : Level} → Set a → (p : Level) → Set (a ⊔ lsuc p)
ℙ A p = A → Ω p

infix 4 _∈_

_∈_ : {a p : Level} {A : Set a} → A → ℙ A p → Set p
x ∈ s = proj₁ (s x)

------------------------------------------------------------------------
-- Groups and subgroups

-- Lean: class Group (G : Type u) extends DivInvMonoid G where
--         inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1
--
-- Lean's class becomes a record over the carrier, taken as an instance
-- argument where Lean takes [Group α].  The record keeps the operations and
-- the laws of Lean's Group; it leaves out the data fields npow, zpow and div
-- that Lean's structure carries with default values (npowRec, zpowRec, and
-- a * b⁻¹), with their laws, which Lagrange's theorem does not touch.

record Group {a : Level} (A : Set a) : Set a where
  infixl 7 _*_
  infix  8 _⁻¹
  field
    _*_            : A → A → A
    1g             : A
    _⁻¹            : A → A
    mul-assoc      : (x y z : A) → (x * y) * z ≡ x * (y * z)
    one-mul        : (x : A) → 1g * x ≡ x
    mul-one        : (x : A) → x * 1g ≡ x
    inv-mul-cancel : (x : A) → x ⁻¹ * x ≡ 1g

module _ {a : Level} {A : Set a} ⦃ G : Group A ⦄ where
  open Group G
  open ≡-Reasoning

  -- The consequences of Lean's axioms that the proofs use; Mathlib proves
  -- each of them for every group.

  inv-mul-cancel-left : (x y : A) → x ⁻¹ * (x * y) ≡ y
  inv-mul-cancel-left x y = begin
    x ⁻¹ * (x * y)   ≡⟨ sym (mul-assoc (x ⁻¹) x y) ⟩
    (x ⁻¹ * x) * y   ≡⟨ cong (_* y) (inv-mul-cancel x) ⟩
    1g * y           ≡⟨ one-mul y ⟩
    y                ∎

  mul-left-cancel : {x y z : A} → x * y ≡ x * z → y ≡ z
  mul-left-cancel {x} {y} {z} e = begin
    y                ≡⟨ sym (inv-mul-cancel-left x y) ⟩
    x ⁻¹ * (x * y)   ≡⟨ cong (x ⁻¹ *_) e ⟩
    x ⁻¹ * (x * z)   ≡⟨ inv-mul-cancel-left x z ⟩
    z                ∎

  mul-inv-cancel : (x : A) → x * x ⁻¹ ≡ 1g
  mul-inv-cancel x = mul-left-cancel
    (trans (inv-mul-cancel-left x (x ⁻¹)) (sym (mul-one (x ⁻¹))))

  mul-inv-cancel-left : (x y : A) → x * (x ⁻¹ * y) ≡ y
  mul-inv-cancel-left x y = begin
    x * (x ⁻¹ * y)   ≡⟨ sym (mul-assoc x (x ⁻¹) y) ⟩
    (x * x ⁻¹) * y   ≡⟨ cong (_* y) (mul-inv-cancel x) ⟩
    1g * y           ≡⟨ one-mul y ⟩
    y                ∎

  inv-unique : {x y : A} → x * y ≡ 1g → x ⁻¹ ≡ y
  inv-unique {x} {y} e = begin
    x ⁻¹             ≡⟨ sym (mul-one (x ⁻¹)) ⟩
    x ⁻¹ * 1g        ≡⟨ cong (x ⁻¹ *_) (sym e) ⟩
    x ⁻¹ * (x * y)   ≡⟨ inv-mul-cancel-left x y ⟩
    y                ∎

  -- Lean: structure Subgroup (G : Type*) [Group G] extends Submonoid G where
  --         inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier
  --
  -- with Submonoid's carrier : Set G, mul_mem' and one_mem', flattened.

  record Subgroup (p : Level) : Set (a ⊔ lsuc p) where
    field
      carrier : ℙ A p
      mul-mem : {x y : A} → x ∈ carrier → y ∈ carrier → x * y ∈ carrier
      one-mem : 1g ∈ carrier
      inv-mem : {x : A} → x ∈ carrier → x ⁻¹ ∈ carrier

  open Subgroup

  -- Lean's coercion of a subgroup to a type, ↥s = { x // x ∈ s }, and the
  -- equality of its elements, which Lean has by proof irrelevance and Agda
  -- by the irrelevance that Ω carries.

  ⟨_⟩ : {p : Level} → Subgroup p → Set (a ⊔ p)
  ⟨ H ⟩ = Σ A (λ x → x ∈ carrier H)

  ⟨⟩-≡ : {p : Level} {H : Subgroup p} {x y : A}
         {x∈ : x ∈ carrier H} {y∈ : y ∈ carrier H}
       → x ≡ y → _≡_ {A = ⟨ H ⟩} (x , x∈) (y , y∈)
  ⟨⟩-≡ {H = H} {x} {x∈ = x∈} {y∈} refl = cong (x ,_) (proj₂ (carrier H x) x∈ y∈)

  -- Lean: def QuotientGroup.leftRel (s : Subgroup α) : Setoid α, whose
  -- relation is x⁻¹ * y ∈ s, an equivalence relation by the subgroup laws.

  module _ {p : Level} (H : Subgroup p) where

    leftRel : A → A → Ω p
    leftRel x y = carrier H (x ⁻¹ * y)

    _~_ : A → A → Set p
    x ~ y = proj₁ (leftRel x y)

    ~-refl : (x : A) → x ~ x
    ~-refl x = subst (_∈ carrier H) (sym (inv-mul-cancel x)) (one-mem H)

    ~-sym : {x y : A} → x ~ y → y ~ x
    ~-sym {x} {y} r = subst (_∈ carrier H) (inv-unique e) (inv-mem H r)
      where
      e : (x ⁻¹ * y) * (y ⁻¹ * x) ≡ 1g
      e = begin
        (x ⁻¹ * y) * (y ⁻¹ * x)   ≡⟨ mul-assoc (x ⁻¹) y (y ⁻¹ * x) ⟩
        x ⁻¹ * (y * (y ⁻¹ * x))   ≡⟨ cong (x ⁻¹ *_) (mul-inv-cancel-left y x) ⟩
        x ⁻¹ * x                  ≡⟨ inv-mul-cancel x ⟩
        1g                        ∎

    ~-trans : {x y z : A} → x ~ y → y ~ z → x ~ z
    ~-trans {x} {y} {z} r s = subst (_∈ carrier H) e (mul-mem H r s)
      where
      e : (x ⁻¹ * y) * (y ⁻¹ * z) ≡ x ⁻¹ * z
      e = begin
        (x ⁻¹ * y) * (y ⁻¹ * z)   ≡⟨ mul-assoc (x ⁻¹) y (y ⁻¹ * z) ⟩
        x ⁻¹ * (y * (y ⁻¹ * z))   ≡⟨ cong (x ⁻¹ *_) (mul-inv-cancel-left y z) ⟩
        x ⁻¹ * z                  ∎

  infix 4 _~⟨_⟩_

  _~⟨_⟩_ : {p : Level} → A → Subgroup p → A → Set p
  x ~⟨ H ⟩ y = _~_ H x y

------------------------------------------------------------------------
-- The parameters

-- Lean's propext and funext, as in the entry set-ext: propositional
-- extensionality over Ω (over all of Set it would be refutable), and
-- function extensionality, which Lean proves from Quot.sound.

record PropExt : Setω where
  field
    propext : {p : Level} {P Q : Ω p} → proj₁ P ⇔ proj₁ Q → P ≡ Q

record FunExt : Setω where
  field
    funext : {a b : Level} → Extensionality a b

-- Lean's quotient primitives, as in the entry multiset-map-map, whose notes
-- explain the three fields that differ from a word-for-word rendering (ind's
-- motive in Ω, lift's UIP B, squash).

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

-- Lean's Nonempty, the inductive proposition with the one constructor
-- intro : α → Nonempty α, which eliminates only into Prop.  Lean also
-- writes ∃ x, p x for an inductive proposition, and Classical.choose
-- passes from it to Nonempty { x // p x }, so one truncation serves both.
-- It is not a classical principle: the cubical library proves it (∥_∥₁),
-- and profile CC lacks it only because it has no higher inductive types.

record Truncation : Setω where
  field
    ∥_∥           : {a : Level} → Set a → Set a
    ∣_∣           : {a : Level} {A : Set a} → A → ∥ A ∥
    ∥∥-irrelevant : {a : Level} {A : Set a} → Irrelevant ∥ A ∥
    ∥∥-rec        : {a b : Level} {A : Set a} {B : Set b}
                  → Irrelevant B → (A → B) → ∥ A ∥ → B

-- Lean's axiom Classical.choice : {α : Sort u} → Nonempty α → α.

record Choice (T : Truncation) : Setω where
  field
    choice : {a : Level} {A : Set a} → Truncation.∥_∥ T A → A

-- Mathlib's Nat.card α = Cardinal.toNat (Cardinal.mk α): the number of
-- elements of a finite type, and 0 for an infinite one, which Mathlib
-- decides with Classical.propDecidable (through Function.extend in
-- Cardinal.toENatAux).  The record keeps the two laws Lean's proof uses,
-- Nat.card_congr and Nat.card_prod, and Nat.card_eq_fintype_card at Fin n
-- (with Fintype.card_fin), which the proof does not use and without which
-- the constant function 0 would satisfy the record.  With card-fin the
-- record is a classical principle: card-wlem below derives weak excluded
-- middle from it.  It leaves out the infinite case, Nat.card α = 0 for an
-- infinite α, which no proof here needs.

record Card : Setω where
  field
    card       : {a : Level} → Set a → ℕ
    card-congr : {a b : Level} {A : Set a} {B : Set b} → A ↔ B → card A ≡ card B
    card-prod  : {a b : Level} {A : Set a} {B : Set b}
               → card (A × B) ≡ card A ℕ.* card B
    card-fin   : (n : ℕ) → card (Fin n) ≡ n

------------------------------------------------------------------------
-- What propext and funext give: Ω is a set, and quotients are effective

module _ (pe : PropExt) (fe : FunExt) where
  open PropExt pe
  open FunExt fe

  -- Lean has UIP for Prop, as for every type.  Here it follows from propext
  -- and funext by Hedberg's argument as agda-stdlib packages it
  -- (Constant⇒UIP): the map sending a proof of P ≡ Q to propext of the
  -- logical equivalence it induces is constant, since the two functions of
  -- that equivalence are determined up to funext by the irrelevance of P
  -- and Q.  The quotient record's lift into Ω needs it.

  Ω-is-set : {p : Level} → UIP (Ω p)
  Ω-is-set {p} = Constant⇒UIP.≡-irrelevant f f-constant
    where
    f : {P Q : Ω p} → P ≡ Q → P ≡ Q
    f {P} {Q} e = propext {P = P} {Q} (mk⇔ (subst proj₁ e) (subst proj₁ (sym e)))

    f-constant : {P Q : Ω p} (e e′ : P ≡ Q) → f e ≡ f e′
    f-constant {P} {Q} e e′ =
      cong₂ (λ g h → propext {P = P} {Q} (mk⇔ g h))
            (funext (λ x → proj₂ Q (subst proj₁ e x) (subst proj₁ e′ x)))
            (funext (λ y → proj₂ P (subst proj₁ (sym e) y)
                                   (subst proj₁ (sym e′) y)))

  -- Lean: theorem Quotient.exact {s : Setoid α} {a b : α} :
  --         ⟦a⟧ = ⟦b⟧ → a ≈ b
  --
  -- proved, as Lean proves it, by lifting the proposition `x ≈ _` to the
  -- quotient (with propext for the proof that it respects the relation) and
  -- computing the lift at both points.

  module _ (Q : Quotients) where
    open Quotients Q

    exact : {a r : Level} {A : Set a} (R : A → A → Ω r)
          → (∀ x → proj₁ (R x x))
          → (∀ {x y z} → proj₁ (R x y) → proj₁ (R y z) → proj₁ (R x z))
          → (∀ {x y} → proj₁ (R x y) → proj₁ (R y x))
          → {x y : A} → mk (λ x y → proj₁ (R x y)) x ≡ mk _ y → proj₁ (R x y)
    exact R R-refl R-trans R-sym {x} {y} e = subst proj₁ Rx-x≡Rx-y (R-refl x)
      where
      open ≡-Reasoning
      R′ = λ x y → proj₁ (R x y)

      R-resp : ∀ y z → R′ y z → R x y ≡ R x z
      R-resp y z r = propext (mk⇔ (λ s → R-trans s r) (λ s → R-trans s (R-sym r)))

      Rx-x≡Rx-y : R x x ≡ R x y
      Rx-x≡Rx-y = begin
        R x x                              ≡⟨ sym (lift-β Ω-is-set (R x) R-resp x) ⟩
        lift Ω-is-set (R x) R-resp (mk R′ x) ≡⟨ cong (lift Ω-is-set (R x) R-resp) e ⟩
        lift Ω-is-set (R x) R-resp (mk R′ y) ≡⟨ lift-β Ω-is-set (R x) R-resp y ⟩
        R x y                              ∎

------------------------------------------------------------------------
-- Lagrange's theorem, with the parameters

module Lagrange (pe : PropExt) (fe : FunExt) (Q : Quotients)
                (T : Truncation) (C : Choice T) (K : Card) where
  open Quotients Q
  open Truncation T
  open Choice C
  open Card K

  -- Lean: theorem Quot.exists_rep (q : Quot r) : ∃ a, Quot.mk r a = q
  --       noncomputable def Quot.out (q : Quot r) : α :=
  --         Classical.choose (Quot.exists_rep q)
  --
  -- The motive of ind is a proposition because the truncation is one; out
  -- is the step that needs Classical.choice.

  module _ {a r : Level} {A : Set a} (R : A → A → Set r) where

    exists-rep : (q : Quot R) → ∥ Σ A (λ x → mk R x ≡ q) ∥
    exists-rep = ind {P = λ q → ∥ Σ A (λ x → mk R x ≡ q) ∥ , ∥∥-irrelevant}
                     (λ x → ∣ x , refl ∣)

    out : Quot R → A
    out q = proj₁ (choice (exists-rep q))

    out-eq : (q : Quot R) → mk R (out q) ≡ q
    out-eq q = proj₂ (choice (exists-rep q))

  module _ {a p : Level} {A : Set a} ⦃ G : Group A ⦄ (H : Subgroup p) where
    open Group G
    open Subgroup H

    -- Lean: instance : HasQuotient α (Subgroup α) := ⟨fun s => Quotient (leftRel s)⟩
    --
    -- Lean's α ⧸ s lives in the universe of α; here A ⧸ H lives in
    -- Set (a ⊔ p), which is Set a when p ≤ a.

    A⧸H : Set (a ⊔ p)
    A⧸H = Quot (_~_ H)

    ⟦_⟧ : A → A⧸H
    ⟦_⟧ = mk (_~_ H)

    rep : A⧸H → A
    rep = out (_~_ H)

    ⟦⟧-exact : {x y : A} → ⟦ x ⟧ ≡ ⟦ y ⟧ → x ~⟨ H ⟩ y
    ⟦⟧-exact = exact pe fe Q (leftRel H) (~-refl H) (~-trans H) (~-sym H)

    -- Lean: noncomputable def groupEquivQuotientProdSubgroup : α ≃ (α ⧸ s) × s
    --
    -- Lean composes four equivalences: α with the sum of the fibers of the
    -- quotient map, each fiber {x // ⟦x⟧ = L} with the coset (out L) • s,
    -- that coset with s (leftCosetEquivSubgroup, x ↦ (out L)⁻¹ * x), and the
    -- sum of copies of s with the product.  The composite is the map below:
    -- x goes to its coset and to (out ⟦x⟧)⁻¹ * x, and (q , h) back to
    -- out q * h.

    to : A → A⧸H × ⟨ H ⟩
    to x = ⟦ x ⟧ , (rep ⟦ x ⟧ ⁻¹ * x , ⟦⟧-exact (out-eq (_~_ H) ⟦ x ⟧))

    from : A⧸H × ⟨ H ⟩ → A
    from (q , h , _) = rep q * h

    from-to : (x : A) → from (to x) ≡ x
    from-to x = mul-inv-cancel-left (rep ⟦ x ⟧) x

    to-from : (y : A⧸H × ⟨ H ⟩) → to (from y) ≡ y
    to-from (q , h , h∈H) = cong₂ _,_ ⟦g⟧≡q (⟨⟩-≡ {H = H} h-eq)
      where
      open ≡-Reasoning
      g = rep q * h

      rep-q~g : rep q ~⟨ H ⟩ g
      rep-q~g = subst (_∈ carrier) (sym (inv-mul-cancel-left (rep q) h)) h∈H

      ⟦g⟧≡q : ⟦ g ⟧ ≡ q
      ⟦g⟧≡q = trans (sym (sound rep-q~g)) (out-eq (_~_ H) q)

      h-eq : rep ⟦ g ⟧ ⁻¹ * g ≡ h
      h-eq = begin
        rep ⟦ g ⟧ ⁻¹ * g    ≡⟨ cong (λ z → rep z ⁻¹ * g) ⟦g⟧≡q ⟩
        rep q ⁻¹ * g        ≡⟨ inv-mul-cancel-left (rep q) h ⟩
        h                   ∎

    group-equiv-quotient-prod-subgroup : A ↔ (A⧸H × ⟨ H ⟩)
    group-equiv-quotient-prod-subgroup = mk↔ₛ′ to from to-from from-to

    -- Lean: theorem card_eq_card_quotient_mul_card_subgroup (s : Subgroup α) :
    --         Nat.card α = Nat.card (α ⧸ s) * Nat.card s := by
    --       rw [← Nat.card_prod]; exact Nat.card_congr groupEquivQuotientProdSubgroup

    card-eq-card-quotient-mul-card-subgroup : card A ≡ card A⧸H ℕ.* card ⟨ H ⟩
    card-eq-card-quotient-mul-card-subgroup =
      trans (card-congr group-equiv-quotient-prod-subgroup) card-prod

  -- The theorem.  Lean's ∣ on ℕ is a ∣ b ↔ ∃ c, b = a * c, and the proof
  -- closes with dvd_mul_left a b : a ∣ b * a; agda-stdlib's _∣_ is the
  -- record of a quotient q and a proof that n ≡ q * m, the same shape.

  card-subgroup-dvd-card : {a p : Level} {A : Set a} ⦃ G : Group A ⦄
                           (H : Subgroup p) → card ⟨ H ⟩ ∣ card A
  card-subgroup-dvd-card H =
    divides (card (A⧸H H)) (card-eq-card-quotient-mul-card-subgroup H)

  -- The statement for a finite group, which SubgroupCardDvdFinite.agda
  -- proves with no parameters, follows from the theorem by card-fin.

  card-subgroup-dvd-card-fin : {a p : Level} {A : Set a} ⦃ G : Group A ⦄
                               (H : Subgroup p) {n m : ℕ}
                             → A ↔ Fin n → ⟨ H ⟩ ↔ Fin m → m ∣ n
  card-subgroup-dvd-card-fin H {n} {m} eA eH =
    subst₂ _∣_ (trans (card-congr eH) (card-fin m))
               (trans (card-congr eA) (card-fin n))
               (card-subgroup-dvd-card H)

------------------------------------------------------------------------
-- Card is a classical principle

-- For a proposition P, the type P ⊎ ⊤ has two elements if P holds and one
-- if it fails, so its cardinality, compared with 2, decides ¬ P or ¬ ¬ P.
-- Weak excluded middle is not provable in Agda without postulates, so no
-- Card can be built here; the constant function 0 satisfies card-congr and
-- card-prod, so card-fin is what makes the record classical.

module _ (K : Card) where
  open Card K

  private
    two-elements : {P : Set} → Irrelevant P → P → (P ⊎ ⊤) ↔ Bool
    two-elements {P} P-irr p = mk↔ₛ′ to from to-from from-to
      where
      to : P ⊎ ⊤ → Bool
      to (inj₁ _) = true
      to (inj₂ _) = false
      from : Bool → P ⊎ ⊤
      from true  = inj₁ p
      from false = inj₂ tt
      to-from : (b : Bool) → to (from b) ≡ b
      to-from true  = refl
      to-from false = refl
      from-to : (x : P ⊎ ⊤) → from (to x) ≡ x
      from-to (inj₁ q) = cong inj₁ (P-irr p q)
      from-to (inj₂ _) = refl

    one-element : {P : Set} → ¬ P → (P ⊎ ⊤) ↔ ⊤
    one-element {P} ¬p = mk↔ₛ′ (λ _ → tt) (λ _ → inj₂ tt) (λ _ → refl) from-to
      where
      from-to : (x : P ⊎ ⊤) → inj₂ tt ≡ x
      from-to (inj₁ q) = ⊥-elim (¬p q)
      from-to (inj₂ _) = refl

    one≢two : ¬ (1 ≡ 2)
    one≢two ()

  card-wlem : (P : Set) → Irrelevant P → ¬ P ⊎ ¬ ¬ P
  card-wlem P P-irr with <-cmp (card (P ⊎ ⊤)) 2
  ... | tri< _ c≢2 _ = inj₁ (λ p → c≢2 (card-two p))
    where
    card-two : P → card (P ⊎ ⊤) ≡ 2
    card-two p = trans (card-congr (↔-trans (two-elements P-irr p) (↔-sym 2↔Bool)))
                       (card-fin 2)
  ... | tri≈ _ c≡2 _ = inj₂ (λ ¬p → one≢two (trans (sym (card-one ¬p)) c≡2))
    where
    card-one : ¬ P → card (P ⊎ ⊤) ≡ 1
    card-one ¬p = trans (card-congr (↔-trans (one-element ¬p) (↔-sym 1↔⊤)))
                        (card-fin 1)
  ... | tri> _ c≢2 _ = inj₁ (λ p → c≢2 (card-two p))
    where
    card-two : P → card (P ⊎ ⊤) ≡ 2
    card-two p = trans (card-congr (↔-trans (two-elements P-irr p) (↔-sym 2↔Bool)))
                       (card-fin 2)
