{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of Lists~x27~:Subset:refl
-- Lean module Init.Core
module U.Init.Core where
import U.Init.Prelude

Eq:mp : {α₀ : Set} → {β₁ : Set} → U.Init.Prelude.Eq {Set} α₀ β₁ → α₀ → β₁
Eq:mp {α₀} {β₁} h₂ a₃ = U.Init.Prelude.Eq:rec {Set} {α₀} {λ (x₄ : Set) → λ (h₅ : U.Init.Prelude.Eq {Set} α₀ x₄) → x₄} a₃ {β₁} h₂

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

HEq:homo~undrec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : α₀ → Set} → motive₂ a₁ → {b₃ : α₀} → U.Init.Prelude.HEq {α₀} a₁ {α₀} b₃ → motive₂ b₃
HEq:homo~undrec {α₀} {a₁} {motive₂} m₃ {b₄} h₅ = U.Init.Prelude.Eq:ndrec {α₀} {a₁} {motive₂} m₃ {b₄} (U.Init.Prelude.eq~uof~uheq {α₀} {a₁} {b₄} h₅)

record HasSubset (α₀ : Set) : Set where
  constructor HasSubset:mk
  field
    Subset₁ : α₀ → α₀ → Set

-- recursor
HasSubset:rec : {α₀ : Set} → {motive₁ : HasSubset α₀ → Set} → ((Subset₂ : α₀ → α₀ → Set) → motive₁ (HasSubset:mk {α₀} Subset₂)) → (t₂ : HasSubset α₀) → motive₁ t₂
HasSubset:rec {α₀} {motive₁} mk₂ (HasSubset:mk Subset₃) = mk₂ Subset₃

HasSubset:Subset : {α₀ : Set} → ⦃ _ : HasSubset α₀ ⦄ → α₀ → α₀ → Set
HasSubset:Subset {α₀} ⦃ self₁ ⦄ = HasSubset.Subset₁ {α₀} self₁

-- theorem
opaque
  Iff:refl : (a₀ : Set) → Iff a₀ a₀
  Iff:refl a₀ = Iff:intro {a₀} {a₀} (λ (h₁ : a₀) → h₁) (λ (h₁ : a₀) → h₁)

-- theorem
opaque
  Iff:rfl : {a₀ : Set} → Iff a₀ a₀
  Iff:rfl {a₀} = Iff:refl a₀

~uprivate:Init:Core:~n0:Lean:injEq~uhelper:match~u1~u1 : {P₀ : Set} → {Q₁ : Set} → (motive₂ : U.Init.Prelude.And P₀ Q₁ → Set) → (h₃ : U.Init.Prelude.And P₀ Q₁) → ((h₄ : P₀) → (h₅ : Q₁) → motive₂ (U.Init.Prelude.And:intro {P₀} {Q₁} h₄ h₅)) → motive₂ h₃
~uprivate:Init:Core:~n0:Lean:injEq~uhelper:match~u1~u1 {P₀} {Q₁} motive₂ h₃ h1₄ = U.Init.Prelude.And:casesOn {P₀} {Q₁} {λ (x₅ : U.Init.Prelude.And P₀ Q₁) → motive₂ x₅} h₃ (λ (left₅ : P₀) → λ (right₆ : Q₁) → h1₄ left₅ right₆)

-- theorem
opaque
  Lean:injEq~uhelper : {P₀ : Set} → {Q₁ : Set} → {R₂ : Set} → (P₀ → Q₁ → R₂) → U.Init.Prelude.And P₀ Q₁ → R₂
  Lean:injEq~uhelper {P₀} {Q₁} {R₂} h₃ h₄ = ~uprivate:Init:Core:~n0:Lean:injEq~uhelper:match~u1~u1 {P₀} {Q₁} (λ (h₅ : U.Init.Prelude.And P₀ Q₁) → R₂) h₄ (λ (h₅ : P₀) → λ (h₆ : Q₁) → h₃ h₅ h₆)

-- theorem
opaque
  trivial : U.Init.Prelude.True
  trivial = U.Init.Prelude.True:intro

Quot:liftOn : {α₀ : Set} → {β₁ : Set} → {r₂ : α₀ → α₀ → Set} → U.Init.Prelude.Quot {α₀} r₂ → (f₃ : α₀ → β₁) → ((a₄ : α₀) → (b₅ : α₀) → r₂ a₄ b₅ → U.Init.Prelude.Eq {β₁} (f₃ a₄) (f₃ b₅)) → β₁
Quot:liftOn {α₀} {β₁} {r₂} q₃ f₄ c₅ = U.Init.Prelude.Quot:lift {α₀} {r₂} {β₁} f₄ c₅ q₃

postulate Quot:sound : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {a₂ : α₀} → {b₃ : α₀} → r₁ a₂ b₃ → U.Init.Prelude.Eq {U.Init.Prelude.Quot {α₀} r₁} (U.Init.Prelude.Quot:mk {α₀} r₁ a₂) (U.Init.Prelude.Quot:mk {α₀} r₁ b₃)

-- theorem
opaque
  funext : {α₀ : Set} → {β₁ : α₀ → Set} → {f₂ : (x₂ : α₀) → β₁ x₂} → {g₃ : (x₃ : α₀) → β₁ x₃} → ((x₄ : α₀) → U.Init.Prelude.Eq {β₁ x₄} (f₂ x₄) (g₃ x₄)) → U.Init.Prelude.Eq {(x₄ : α₀) → β₁ x₄} f₂ g₃
  funext {α₀} {β₁} {f₂} {g₃} h₄ = let eqv₅ : ((x₅ : α₀) → β₁ x₅) → ((x₅ : α₀) → β₁ x₅) → Set; eqv₅ = λ (f₅ : (x₅ : α₀) → β₁ x₅) → λ (g₆ : (x₆ : α₀) → β₁ x₆) → (x₇ : α₀) → U.Init.Prelude.Eq {β₁ x₇} (f₅ x₇) (g₆ x₇) in let extfunApp₆ : U.Init.Prelude.Quot {(x₆ : α₀) → β₁ x₆} eqv₅ → (x₆ : α₀) → β₁ x₆; extfunApp₆ = λ (f₆ : U.Init.Prelude.Quot {(x₆ : α₀) → β₁ x₆} eqv₅) → λ (x₇ : α₀) → Quot:liftOn {(x₈ : α₀) → β₁ x₈} {β₁ x₇} {eqv₅} f₆ (λ (f₈ : (x₈ : α₀) → β₁ x₈) → f₈ x₇) (λ (x₈ : (x₈ : α₀) → β₁ x₈) → λ (x₉ : (x₉ : α₀) → β₁ x₉) → λ (h₁₀ : eqv₅ x₈ x₉) → h₁₀ x₇) in U.Init.Prelude.id {U.Init.Prelude.Eq {(x₇ : α₀) → β₁ x₇} f₂ g₃} (U.Init.Prelude.congrArg {U.Init.Prelude.Quot {(x₇ : α₀) → β₁ x₇} eqv₅} {(x₇ : α₀) → β₁ x₇} {U.Init.Prelude.Quot:mk {(x₇ : α₀) → β₁ x₇} eqv₅ f₂} {U.Init.Prelude.Quot:mk {(x₇ : α₀) → β₁ x₇} eqv₅ g₃} extfunApp₆ (Quot:sound {(x₇ : α₀) → β₁ x₇} {eqv₅} {f₂} {g₃} h₄))

record Sigma {α₀ : Set} (β₁ : α₀ → Set) : Set where
  constructor Sigma:mk
  field
    fst₂ : α₀
    snd₃ : β₁ fst₂

-- recursor
Sigma:rec : {α₀ : Set} → {β₁ : α₀ → Set} → {motive₂ : Sigma {α₀} β₁ → Set} → ((fst₃ : α₀) → (snd₄ : β₁ fst₃) → motive₂ (Sigma:mk {α₀} {β₁} fst₃ snd₄)) → (t₃ : Sigma {α₀} β₁) → motive₂ t₃
Sigma:rec {α₀} {β₁} {motive₂} mk₃ (Sigma:mk fst₄ snd₅) = mk₃ fst₄ snd₅

Sigma:casesOn : {α₀ : Set} → {β₁ : α₀ → Set} → {motive₂ : Sigma {α₀} β₁ → Set} → (t₃ : Sigma {α₀} β₁) → ((fst₄ : α₀) → (snd₅ : β₁ fst₄) → motive₂ (Sigma:mk {α₀} {β₁} fst₄ snd₅)) → motive₂ t₃
Sigma:casesOn {α₀} {β₁} {motive₂} t₃ mk₄ = Sigma:rec {α₀} {β₁} {motive₂} (λ (fst₅ : α₀) → λ (snd₆ : β₁ fst₅) → mk₄ fst₅ snd₆) t₃
