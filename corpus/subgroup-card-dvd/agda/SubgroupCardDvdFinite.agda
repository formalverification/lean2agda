{-# OPTIONS --safe --cubical-compatible #-}

-- File: corpus/subgroup-card-dvd/agda/SubgroupCardDvdFinite.agda
--
-- Lagrange's theorem for finite groups, the de-classicalized form of Mathlib's
-- Subgroup.card_subgroup_dvd_card (Mathlib.GroupTheory.Coset.Card, Mathlib
-- v4.33.1):
--
--     theorem card_subgroup_dvd_card (s : Subgroup α) : Nat.card s ∣ Nat.card α
--
-- under profile CC, with no module parameters.  Nat.card is replaced by
-- enumerations: a group A with A ↔ Fin n and a subgroup H with ⟨ H ⟩ ↔ Fin m,
-- and the conclusion m ∣ n.  Lean's proof picks a representative of each
-- coset with Classical.choice (Quotient.out); here the representative of a
-- coset is its first element in the enumeration of A, which a finite search
-- finds because membership in H is decidable, and the cosets are counted as
-- the decidable subset of their representatives.  SubgroupCardDvd.agda
-- derives the same statement from its classical parameters
-- (card-subgroup-dvd-card-fin there; see ../notes.md).

module SubgroupCardDvdFinite where

open import Level using (Level; _⊔_)
open import Data.Bool.Base using (Bool; true; false; T)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Permutation using (↔⇒≡)
import Data.Fin.Properties as Fin
open import Data.Maybe.Base using (Maybe; just; nothing; fromMaybe)
import Data.Maybe.Base as Maybe
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Nat.Divisibility.Core using (_∣_; divides)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Product.Function.NonDependent.Propositional using (_×-↔_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Function.Base using (_∘_)
open import Function.Bundles using (_↔_; Inverse; mk↔ₛ′)
open import Function.Properties.Inverse using (↔-sym; ↔-trans)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable.Core using (Dec; does; map′; toWitness)
open import Relation.Nullary.Decidable using (dec-true; dec-false; isYes≗does)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Nullary.Irrelevant using (Irrelevant)
open import Relation.Unary using (Pred; Decidable)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)

open import SubgroupCardDvd
  using ( _∈_; Group; Subgroup; module Subgroup; ⟨_⟩; ⟨⟩-≡
        ; _~_; ~-refl; ~-sym; ~-trans
        ; inv-mul-cancel-left; mul-inv-cancel-left )

-- No clause below matches on a constructor of Fin or Dec, whose indices
-- would make --cubical-compatible warn [UnsupportedIndexedMatch]: cases on
-- Fin go through agda-stdlib's ∀-cons, and decisions through does.

------------------------------------------------------------------------
-- Decisions

true⇒ : {p : Level} {P : Set p} (d : Dec P) → does d ≡ true → P
true⇒ d e = toWitness {a? = d} (subst T (sym (trans (isYes≗does d) e)) tt)

does-cong : {p q : Level} {P : Set p} {Q : Set q}
          → (P → Q) → (Q → P) → (p? : Dec P) (q? : Dec Q) → does p? ≡ does q?
does-cong f g p? q? with does p? in e
... | true  = sym (dec-true q? (f (true⇒ p? e)))
... | false = sym (dec-false q? λ q →
                    false≢true (trans (sym e) (dec-true p? (g q))))
  where
  false≢true : ¬ (false ≡ true)
  false≢true ()

-- Equality of pairs whose second components are propositions.

Σ-≡ : {a p : Level} {A : Set a} {P : A → Set p} → (∀ {x} → Irrelevant (P x))
    → {u v : Σ A P} → proj₁ u ≡ proj₁ v → u ≡ v
Σ-≡ irr {_ , p} {_ , q} refl = cong (_ ,_) (irr p q)

------------------------------------------------------------------------
-- The first index at which a Boolean function holds

-- A step of the search: true at 0, or the search of the rest, shifted.

step : {n : ℕ} → Bool → Maybe (Fin n) → Maybe (Fin (ℕ.suc n))
step true  _ = just zero
step false m = Maybe.map suc m

first : {n : ℕ} → (Fin n → Bool) → Maybe (Fin n)
first {ℕ.zero}  f = nothing
first {ℕ.suc n} f = step (f zero) (first (f ∘ suc))

first-cong : {n : ℕ} {f g : Fin n → Bool} → (∀ i → f i ≡ g i) → first f ≡ first g
first-cong {ℕ.zero}  _ = refl
first-cong {ℕ.suc n} e = cong₂ step (e zero) (first-cong (e ∘ suc))

step-just : {n : ℕ} (b : Bool) (m : Maybe (Fin n)) {i : Fin (ℕ.suc n)}
          → step b m ≡ just i
          → (b ≡ true × zero ≡ i) ⊎ Σ (Fin n) (λ j → m ≡ just j × suc j ≡ i)
step-just true  _        e = inj₁ (refl , just-injective e)
step-just false (just j) e = inj₂ (j , refl , just-injective e)
step-just false nothing  ()

first-sound : {n : ℕ} (f : Fin n → Bool) {i : Fin n}
            → first f ≡ just i → f i ≡ true
first-sound {ℕ.zero}  f ()
first-sound {ℕ.suc n} f e with step-just (f zero) (first (f ∘ suc)) e
... | inj₁ (f0 , 0≡i)       = subst (λ i → f i ≡ true) 0≡i f0
... | inj₂ (j , m≡j , sj≡i) =
  subst (λ i → f i ≡ true) sj≡i (first-sound (f ∘ suc) m≡j)

step-some : {n : ℕ} (b : Bool) (m : Maybe (Fin n))
          → m ≢ nothing → step b m ≢ nothing
step-some true  _        _  ()
step-some false (just _) _  ()
step-some false nothing  m≢ _ = m≢ refl

first-complete : {n : ℕ} (f : Fin n → Bool) (i : Fin n)
               → f i ≡ true → first f ≢ nothing
first-complete {ℕ.zero}  f i = ⊥-elim (Fin.¬Fin0 i)
first-complete {ℕ.suc n} f =
  Fin.∀-cons {P = λ i → f i ≡ true → first f ≢ nothing} at-zero at-suc
  where
  at-zero : f zero ≡ true → first f ≢ nothing
  at-zero f0 = subst (λ b → step b (first (f ∘ suc)) ≢ nothing) (sym f0) (λ ())

  at-suc : (j : Fin n) → f (suc j) ≡ true → first f ≢ nothing
  at-suc j fj = step-some (f zero) (first (f ∘ suc))
                          (first-complete (f ∘ suc) j fj)

-- The search with a default: the first index at which f holds, or d.

first-or : {n : ℕ} → Fin n → (Fin n → Bool) → Fin n
first-or d f = fromMaybe d (first f)

first-or-holds : {n : ℕ} (d : Fin n) (f : Fin n → Bool) → f d ≡ true
               → f (first-or d f) ≡ true
first-or-holds d f fd with first f in e
... | just i  = first-sound f e
... | nothing = fd

-- Where f holds somewhere, the default does not matter.

first-or-default : {n : ℕ} (d d′ : Fin n) (f : Fin n → Bool) → f d ≡ true
                 → first-or d f ≡ first-or d′ f
first-or-default d d′ f fd with first f | first-complete f d fd
... | just _  | _  = refl
... | nothing | m≢ = ⊥-elim (m≢ refl)

------------------------------------------------------------------------
-- Counting a decidable subset of Fin n

-- A decidable family of propositions over Fin n has as many elements as
-- some Fin k.  The count is returned with the isomorphism, rather than
-- computed by a separate function, so that no goal has to unfold it.

count : {n : ℕ} {p : Level} {P : Pred (Fin n) p} → Decidable P
      → (∀ {i} → Irrelevant (P i)) → Σ ℕ (λ k → Σ (Fin n) P ↔ Fin k)
count {ℕ.zero} _ _ =
  0 , mk↔ₛ′ (λ u → ⊥-elim (Fin.¬Fin0 (proj₁ u))) (λ i → ⊥-elim (Fin.¬Fin0 i))
            (λ i → ⊥-elim (Fin.¬Fin0 i)) (λ u → ⊥-elim (Fin.¬Fin0 (proj₁ u)))
count {ℕ.suc n} {P = P} P? irr with count (P? ∘ suc) irr
... | k , e with does (P? zero) in d
...   | true  = ℕ.suc k , mk↔ₛ′ to from to-from from-to
  where
  open Inverse e using () renaming (to to to′; from to from′)
  p₀ : P zero
  p₀ = true⇒ (P? zero) d

  shift : Σ (Fin n) (P ∘ suc) → Σ (Fin (ℕ.suc n)) P
  shift u = suc (proj₁ u) , proj₂ u

  to : Σ (Fin (ℕ.suc n)) P → Fin (ℕ.suc k)
  to (i , q) = Fin.∀-cons {P = λ i → P i → Fin (ℕ.suc k)}
                 (λ _ → zero) (λ j q → suc (to′ (j , q))) i q

  from : Fin (ℕ.suc k) → Σ (Fin (ℕ.suc n)) P
  from = Fin.∀-cons (zero , p₀) (λ j → shift (from′ j))

  to-from : (j : Fin (ℕ.suc k)) → to (from j) ≡ j
  to-from = Fin.∀-cons refl (λ j → cong suc (Inverse.strictlyInverseˡ e j))

  from-to : (u : Σ (Fin (ℕ.suc n)) P) → from (to u) ≡ u
  from-to (i , q) = Fin.∀-cons {P = λ i → (q : P i) → from (to (i , q)) ≡ (i , q)}
    (λ q → cong (zero ,_) (irr p₀ q))
    (λ j q → cong shift (Inverse.strictlyInverseʳ e (j , q)))
    i q
...   | false = k , mk↔ₛ′ to from to-from from-to
  where
  open Inverse e using () renaming (to to to′; from to from′)
  ¬p₀ : ¬ P zero
  ¬p₀ p = false≢true (trans (sym d) (dec-true (P? zero) p))
    where
    false≢true : ¬ (false ≡ true)
    false≢true ()

  shift : Σ (Fin n) (P ∘ suc) → Σ (Fin (ℕ.suc n)) P
  shift u = suc (proj₁ u) , proj₂ u

  to : Σ (Fin (ℕ.suc n)) P → Fin k
  to (i , q) = Fin.∀-cons {P = λ i → P i → Fin k}
                 (λ q → ⊥-elim (¬p₀ q)) (λ j q → to′ (j , q)) i q

  from : Fin k → Σ (Fin (ℕ.suc n)) P
  from j = shift (from′ j)

  to-from : (j : Fin k) → to (from j) ≡ j
  to-from = Inverse.strictlyInverseˡ e

  from-to : (u : Σ (Fin (ℕ.suc n)) P) → from (to u) ≡ u
  from-to (i , q) = Fin.∀-cons {P = λ i → (q : P i) → from (to (i , q)) ≡ (i , q)}
    (λ q → ⊥-elim (¬p₀ q))
    (λ j q → cong shift (Inverse.strictlyInverseʳ e (j , q)))
    i q

------------------------------------------------------------------------
-- Lagrange's theorem for finite groups

module _ {a p : Level} {A : Set a} ⦃ G : Group A ⦄ (H : Subgroup p)
         {n m : ℕ} (eA : A ↔ Fin n) (eH : ⟨ H ⟩ ↔ Fin m) where
  open Group G
  open Subgroup H
  open Inverse eA using () renaming (to to index; from to element)
  open ≡-Reasoning

  element-index : (x : A) → element (index x) ≡ x
  element-index = Inverse.strictlyInverseʳ eA

  -- Equality on A is decidable, through the enumeration, and so A is a set
  -- (Hedberg's theorem, agda-stdlib's Decidable⇒UIP), as every Lean type is.

  _≟_ : DecidableEquality A
  x ≟ y = map′ (λ e → trans (sym (element-index x))
                            (trans (cong element e) (element-index y)))
               (cong index) (index x Fin.≟ index y)

  open Decidable⇒UIP _≟_ using () renaming (≡-irrelevant to A-is-set)

  -- Membership in H is decidable: search the enumeration of H.

  _∈H? : (x : A) → Dec (x ∈ carrier)
  x ∈H? = map′ found missing (Fin.any? (λ i → proj₁ (Inverse.from eH i) ≟ x))
    where
    found : Σ (Fin m) (λ i → proj₁ (Inverse.from eH i) ≡ x) → x ∈ carrier
    found (i , e) = subst (_∈ carrier) e (proj₂ (Inverse.from eH i))

    missing : x ∈ carrier → Σ (Fin m) (λ i → proj₁ (Inverse.from eH i) ≡ x)
    missing x∈ = Inverse.to eH (x , x∈)
               , cong proj₁ (Inverse.strictlyInverseʳ eH (x , x∈))

  -- The representative of the coset of x: the first element of the
  -- enumeration that lies in it, found by searching for the indices i with
  -- x⁻¹ * element i ∈ H.  It takes the place of Lean's Quotient.out.

  in-coset : A → Fin n → Bool
  in-coset x i = does ((x ⁻¹ * element i) ∈H?)

  in-coset-self : (x : A) → in-coset x (index x) ≡ true
  in-coset-self x = dec-true ((x ⁻¹ * element (index x)) ∈H?)
                      (subst (x ~⟨⟩_) (sym (element-index x)) (~-refl H x))
    where
    _~⟨⟩_ = _~_ H

  rep : A → A
  rep x = element (first-or (index x) (in-coset x))

  rep-mem : (x : A) → _~_ H x (rep x)
  rep-mem x = true⇒ ((x ⁻¹ * rep x) ∈H?)
                (first-or-holds (index x) (in-coset x) (in-coset-self x))

  rep-cong : {x y : A} → _~_ H x y → rep x ≡ rep y
  rep-cong {x} {y} x~y = cong element (begin
    first-or (index x) (in-coset x)  ≡⟨ first-or-default (index x) (index y) (in-coset x)
                                                         (in-coset-self x) ⟩
    first-or (index y) (in-coset x)  ≡⟨ cong (fromMaybe (index y))
                                             (first-cong same-coset) ⟩
    first-or (index y) (in-coset y)  ∎)
    where
    same-coset : ∀ i → in-coset x i ≡ in-coset y i
    same-coset i = does-cong (λ x~z → ~-trans H (~-sym H x~y) x~z)
                             (λ y~z → ~-trans H x~y y~z)
                             ((x ⁻¹ * element i) ∈H?) ((y ⁻¹ * element i) ∈H?)

  rep-idem : (x : A) → rep (rep x) ≡ rep x
  rep-idem x = sym (rep-cong (rep-mem x))

  -- The transversal: the representatives, one for each coset.  It plays the
  -- part of Lean's quotient α ⧸ s.

  Transversal : Set a
  Transversal = Σ A (λ x → rep x ≡ x)

  -- Lean's groupEquivQuotientProdSubgroup, with the transversal in place of
  -- the quotient: x goes to its representative and to (rep x)⁻¹ * x.

  equiv : A ↔ (Transversal × ⟨ H ⟩)
  equiv = mk↔ₛ′ to from to-from from-to
    where
    to : A → Transversal × ⟨ H ⟩
    to x = (rep x , rep-idem x) , (rep x ⁻¹ * x , ~-sym H (rep-mem x))

    from : Transversal × ⟨ H ⟩ → A
    from ((t , _) , (h , _)) = t * h

    from-to : (x : A) → from (to x) ≡ x
    from-to x = mul-inv-cancel-left (rep x) x

    to-from : (y : Transversal × ⟨ H ⟩) → to (from y) ≡ y
    to-from ((t , rep-t) , (h , h∈H)) =
      cong₂ _,_ (Σ-≡ A-is-set rep-th≡t) (⟨⟩-≡ {H = H} h-eq)
      where
      t~th : _~_ H t (t * h)
      t~th = subst (_∈ carrier) (sym (inv-mul-cancel-left t h)) h∈H

      rep-th≡t : rep (t * h) ≡ t
      rep-th≡t = trans (sym (rep-cong t~th)) rep-t

      h-eq : rep (t * h) ⁻¹ * (t * h) ≡ h
      h-eq = trans (cong (λ z → z ⁻¹ * (t * h)) rep-th≡t) (inv-mul-cancel-left t h)

  -- The transversal is a decidable subset of A, hence of Fin n, and so has
  -- as many elements as some Fin k.

  transversal-fin : Transversal ↔ Σ (Fin n) (λ i → rep (element i) ≡ element i)
  transversal-fin = mk↔ₛ′ to from to-from from-to
    where
    to : Transversal → Σ (Fin n) (λ i → rep (element i) ≡ element i)
    to (x , e) = index x , subst (λ y → rep y ≡ y) (sym (element-index x)) e

    from : Σ (Fin n) (λ i → rep (element i) ≡ element i) → Transversal
    from (i , e) = element i , e

    to-from : ∀ u → to (from u) ≡ u
    to-from (i , _) = Σ-≡ A-is-set (Inverse.strictlyInverseˡ eA i)

    from-to : ∀ u → from (to u) ≡ u
    from-to (x , _) = Σ-≡ A-is-set (element-index x)

  cosets : Σ ℕ (λ k → Transversal ↔ Fin k)
  cosets with count (λ i → rep (element i) ≟ element i) A-is-set
  ... | k , e = k , ↔-trans transversal-fin e

  -- The theorem: Fin n ↔ A ↔ Transversal × ⟨ H ⟩ ↔ Fin k × Fin m ↔ Fin (k * m),
  -- so n ≡ k * m by agda-stdlib's ↔⇒≡ (Fin is injective), and m ∣ n.

  card-subgroup-dvd-card-fin : m ∣ n
  card-subgroup-dvd-card-fin with cosets
  ... | k , eT = divides k (↔⇒≡ (↔-trans (↔-sym eA)
                                 (↔-trans equiv
                                 (↔-trans (eT ×-↔ eH) (↔-sym Fin.*↔×)))))

------------------------------------------------------------------------
-- An example that computes

-- The Klein four-group, Bool × Bool under componentwise exclusive or, and
-- its subgroup of the pairs whose second component is false.  The proof
-- above computes: the quotient of the divisibility it returns, the number
-- of cosets, reduces to 2, which `refl` checks.  Lean's Nat.card is
-- noncomputable, so Lean's theorem has no such content.

module Klein where
  open import Data.Bool.Base using (_xor_)
  open import Data.Bool.Properties using (xor-assoc; xor-same)
    renaming (_≟_ to _≟ᵇ_)
  open import Level using (0ℓ)

  V : Set
  V = Bool × Bool

  xor-false : (b : Bool) → b xor false ≡ b
  xor-false true  = refl
  xor-false false = refl

  instance
    klein : Group V
    klein = record
      { _*_            = λ u v → (proj₁ u xor proj₁ v) , (proj₂ u xor proj₂ v)
      ; 1g             = false , false
      ; _⁻¹            = λ u → u
      ; mul-assoc      = λ u v w → cong₂ _,_ (xor-assoc (proj₁ u) _ _)
                                             (xor-assoc (proj₂ u) _ _)
      ; one-mul        = λ _ → refl
      ; mul-one        = λ u → cong₂ _,_ (xor-false (proj₁ u)) (xor-false (proj₂ u))
      ; inv-mul-cancel = λ u → cong₂ _,_ (xor-same (proj₁ u)) (xor-same (proj₂ u))
      }

  open Decidable⇒UIP _≟ᵇ_ using () renaming (≡-irrelevant to Bool-is-set)

  H : Subgroup 0ℓ
  H = record
    { carrier = λ u → (proj₂ u ≡ false) , Bool-is-set
    ; mul-mem = λ {_} {v} e₁ e₂ → subst (λ b → (b xor proj₂ v) ≡ false) (sym e₁) e₂
    ; one-mem = refl
    ; inv-mem = λ e → e
    }

  eV : V ↔ Fin 4
  eV = ↔-trans (↔-sym Fin.2↔Bool ×-↔ ↔-sym Fin.2↔Bool) (↔-sym Fin.*↔×)

  eH : ⟨ H ⟩ ↔ Fin 2
  eH = ↔-trans (mk↔ₛ′ to from (λ _ → refl) from-to) (↔-sym Fin.2↔Bool)
    where
    to : ⟨ H ⟩ → Bool
    to u = proj₁ (proj₁ u)

    from : Bool → ⟨ H ⟩
    from x = (x , false) , refl

    from-to : (u : ⟨ H ⟩) → from (to u) ≡ u
    from-to ((_ , .false) , refl) = refl

  index : 2 ∣ 4
  index = card-subgroup-dvd-card-fin H eV eH

  _ : _∣_.quotient index ≡ 2
  _ = refl
