{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of Multiset:map~umap
-- Lean module Init.Core
module U.Init.Core where
import U.Init.Prelude

Eq:mpr : {α₀ : Set} → {β₁ : Set} → U.Init.Prelude.Eq {Set} α₀ β₁ → β₁ → α₀
Eq:mpr {α₀} {β₁} h₂ b₃ = U.Init.Prelude.Eq:rec {Set} {β₁} {λ (x₄ : Set) → λ (h₅ : U.Init.Prelude.Eq {Set} β₁ x₄) → x₄} b₃ {α₀} (U.Init.Prelude.Eq:symm {Set} {α₀} {β₁} h₂)

record Iff (a₀ : Set) (b₁ : Set) : Set where
  constructor Iff:intro
  field
    mp₂ : a₀ → b₁
    mpr₃ : b₁ → a₀

-- recursor
Iff:rec : {a₀ : Set} → {b₁ : Set} → {motive₂ : Iff a₀ b₁ → Set} → ((mp₃ : a₀ → b₁) → (mpr₄ : b₁ → a₀) → motive₂ (Iff:intro {a₀} {b₁} mp₃ mpr₄)) → (t₃ : Iff a₀ b₁) → motive₂ t₃
Iff:rec {a₀} {b₁} {motive₂} intro₃ (Iff:intro mp₄ mpr₅) = intro₃ mp₄ mpr₅

postulate propext : {a₀ : Set} → {b₁ : Set} → Iff a₀ b₁ → U.Init.Prelude.Eq {Set} a₀ b₁

-- theorem
opaque
  Eq:propIntro : {a₀ : Set} → {b₁ : Set} → (a₀ → b₁) → (b₁ → a₀) → U.Init.Prelude.Eq {Set} a₀ b₁
  Eq:propIntro {a₀} {b₁} h₂ h₃ = propext {a₀} {b₁} (Iff:intro {a₀} {b₁} h₂ h₃)

record Equivalence {α₀ : Set} (r₁ : α₀ → α₀ → Set) : Set where
  constructor Equivalence:mk
  field
    refl₂ : (x₂ : α₀) → r₁ x₂ x₂
    symm₃ : {x₃ : α₀} → {y₄ : α₀} → r₁ x₃ y₄ → r₁ y₄ x₃
    trans₄ : {x₄ : α₀} → {y₅ : α₀} → {z₆ : α₀} → r₁ x₄ y₅ → r₁ y₅ z₆ → r₁ x₄ z₆

-- recursor
Equivalence:rec : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {motive₂ : Equivalence {α₀} r₁ → Set} → ((refl₃ : (x₃ : α₀) → r₁ x₃ x₃) → (symm₄ : {x₄ : α₀} → {y₅ : α₀} → r₁ x₄ y₅ → r₁ y₅ x₄) → (trans₅ : {x₅ : α₀} → {y₆ : α₀} → {z₇ : α₀} → r₁ x₅ y₆ → r₁ y₆ z₇ → r₁ x₅ z₇) → motive₂ (Equivalence:mk {α₀} {r₁} refl₃ symm₄ trans₅)) → (t₃ : Equivalence {α₀} r₁) → motive₂ t₃
Equivalence:rec {α₀} {r₁} {motive₂} mk₃ (Equivalence:mk refl₄ symm₅ trans₆) = mk₃ refl₄ symm₅ trans₆

-- theorem
opaque
  trivial : U.Init.Prelude.True
  trivial = U.Init.Prelude.True:intro

-- theorem
opaque
  Option:some:inj : {α₀ : Set} → {val₁ : α₀} → {val₂ : α₀} → U.Init.Prelude.Eq {U.Init.Prelude.Option α₀} (U.Init.Prelude.Option:some {α₀} val₁) (U.Init.Prelude.Option:some {α₀} val₂) → U.Init.Prelude.Eq {α₀} val₁ val₂
  Option:some:inj {α₀} {val₁} {val₂} x₃ = U.Init.Prelude.Option:some:noConfusion {α₀} {U.Init.Prelude.Eq {α₀} val₁ val₂} {val₁} {val₂} x₃ (λ (valeq₄ : U.Init.Prelude.HEq {α₀} val₁ {α₀} val₂) → U.Init.Prelude.eq~uof~uheq {α₀} {val₁} {val₂} valeq₄)

-- theorem
opaque
  Option:some:injEq : {α₀ : Set} → (val₁ : α₀) → (val₂ : α₀) → U.Init.Prelude.Eq {Set} (U.Init.Prelude.Eq {U.Init.Prelude.Option α₀} (U.Init.Prelude.Option:some {α₀} val₁) (U.Init.Prelude.Option:some {α₀} val₂)) (U.Init.Prelude.Eq {α₀} val₁ val₂)
  Option:some:injEq {α₀} val₁ val₂ = Eq:propIntro {U.Init.Prelude.Eq {U.Init.Prelude.Option α₀} (U.Init.Prelude.Option:some {α₀} val₁) (U.Init.Prelude.Option:some {α₀} val₂)} {U.Init.Prelude.Eq {α₀} val₁ val₂} (Option:some:inj {α₀} {val₁} {val₂}) (U.Init.Prelude.Eq:ndrec {α₀} {val₁} {λ (val₃ : α₀) → U.Init.Prelude.Eq {U.Init.Prelude.Option α₀} (U.Init.Prelude.Option:some {α₀} val₁) (U.Init.Prelude.Option:some {α₀} val₃)} (U.Init.Prelude.Eq:refl {U.Init.Prelude.Option α₀} (U.Init.Prelude.Option:some {α₀} val₁)) {val₂})

Quot:liftOn : {α₀ : Set} → {β₁ : Set} → {r₂ : α₀ → α₀ → Set} → U.Init.Prelude.Quot {α₀} r₂ → (f₃ : α₀ → β₁) → ((a₄ : α₀) → (b₅ : α₀) → r₂ a₄ b₅ → U.Init.Prelude.Eq {β₁} (f₃ a₄) (f₃ b₅)) → β₁
Quot:liftOn {α₀} {β₁} {r₂} q₃ f₄ c₅ = U.Init.Prelude.Quot:lift {α₀} {r₂} {β₁} f₄ c₅ q₃

postulate Quot:sound : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {a₂ : α₀} → {b₃ : α₀} → r₁ a₂ b₃ → U.Init.Prelude.Eq {U.Init.Prelude.Quot {α₀} r₁} (U.Init.Prelude.Quot:mk {α₀} r₁ a₂) (U.Init.Prelude.Quot:mk {α₀} r₁ b₃)

-- theorem
opaque
  funext : {α₀ : Set} → {β₁ : α₀ → Set} → {f₂ : (x₂ : α₀) → β₁ x₂} → {g₃ : (x₃ : α₀) → β₁ x₃} → ((x₄ : α₀) → U.Init.Prelude.Eq {β₁ x₄} (f₂ x₄) (g₃ x₄)) → U.Init.Prelude.Eq {(x₄ : α₀) → β₁ x₄} f₂ g₃
  funext {α₀} {β₁} {f₂} {g₃} h₄ = let eqv₅ : ((x₅ : α₀) → β₁ x₅) → ((x₅ : α₀) → β₁ x₅) → Set; eqv₅ = λ (f₅ : (x₅ : α₀) → β₁ x₅) → λ (g₆ : (x₆ : α₀) → β₁ x₆) → (x₇ : α₀) → U.Init.Prelude.Eq {β₁ x₇} (f₅ x₇) (g₆ x₇) in let extfunApp₆ : U.Init.Prelude.Quot {(x₆ : α₀) → β₁ x₆} eqv₅ → (x₆ : α₀) → β₁ x₆; extfunApp₆ = λ (f₆ : U.Init.Prelude.Quot {(x₆ : α₀) → β₁ x₆} eqv₅) → λ (x₇ : α₀) → Quot:liftOn {(x₈ : α₀) → β₁ x₈} {β₁ x₇} {eqv₅} f₆ (λ (f₈ : (x₈ : α₀) → β₁ x₈) → f₈ x₇) (λ (x₈ : (x₈ : α₀) → β₁ x₈) → λ (x₉ : (x₉ : α₀) → β₁ x₉) → λ (h₁₀ : eqv₅ x₈ x₉) → h₁₀ x₇) in U.Init.Prelude.id {U.Init.Prelude.Eq {(x₇ : α₀) → β₁ x₇} f₂ g₃} (U.Init.Prelude.congrArg {U.Init.Prelude.Quot {(x₇ : α₀) → β₁ x₇} eqv₅} {(x₇ : α₀) → β₁ x₇} {U.Init.Prelude.Quot:mk {(x₇ : α₀) → β₁ x₇} eqv₅ f₂} {U.Init.Prelude.Quot:mk {(x₇ : α₀) → β₁ x₇} eqv₅ g₃} extfunApp₆ (Quot:sound {(x₇ : α₀) → β₁ x₇} {eqv₅} {f₂} {g₃} h₄))

record Setoid (α₀ : Set) : Set where
  constructor Setoid:mk
  field
    r₁ : α₀ → α₀ → Set
    iseqv₂ : Equivalence {α₀} r₁

-- recursor
Setoid:rec : {α₀ : Set} → {motive₁ : Setoid α₀ → Set} → ((r₂ : α₀ → α₀ → Set) → (iseqv₃ : Equivalence {α₀} r₂) → motive₁ (Setoid:mk {α₀} r₂ iseqv₃)) → (t₂ : Setoid α₀) → motive₁ t₂
Setoid:rec {α₀} {motive₁} mk₂ (Setoid:mk r₃ iseqv₄) = mk₂ r₃ iseqv₄

Setoid:r : {α₀ : Set} → ⦃ _ : Setoid α₀ ⦄ → α₀ → α₀ → Set
Setoid:r {α₀} ⦃ self₁ ⦄ = Setoid.r₁ {α₀} self₁

Quotient : {α₀ : Set} → Setoid α₀ → Set
Quotient {α₀} s₁ = U.Init.Prelude.Quot {α₀} (Setoid:r {α₀} ⦃ s₁ ⦄)

-- theorem
opaque
  Quot:inductionOn : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {motive₂ : U.Init.Prelude.Quot {α₀} r₁ → Set} → (q₃ : U.Init.Prelude.Quot {α₀} r₁) → ((a₄ : α₀) → motive₂ (U.Init.Prelude.Quot:mk {α₀} r₁ a₄)) → motive₂ q₃
  Quot:inductionOn {α₀} {r₁} {motive₂} q₃ h₄ = U.Init.Prelude.Quot:ind {α₀} {r₁} {motive₂} h₄ q₃
