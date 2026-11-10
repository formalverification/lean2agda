{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of RecursorFixtures:Doc RecursorFixtures:Doc:~usizeOf~u1 RecursorFixtures:Doc:~usizeOf~u2 RecursorFixtures:Doc:~usizeOf~u2~ueq RecursorFixtures:Doc:~usizeOf~u3 and 251 more
-- Lean module Init.Core
module U.Init.Core where
import U.Init.Prelude

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

Ne : {α₀ : Set} → α₀ → α₀ → Set
Ne {α₀} a₁ b₂ = U.Init.Prelude.Not (U.Init.Prelude.Eq {α₀} a₁ b₂)

HEq:homo~undrec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : α₀ → Set} → motive₂ a₁ → {b₃ : α₀} → U.Init.Prelude.HEq {α₀} a₁ {α₀} b₃ → motive₂ b₃
HEq:homo~undrec {α₀} {a₁} {motive₂} m₃ {b₄} h₅ = U.Init.Prelude.Eq:ndrec {α₀} {a₁} {motive₂} m₃ {b₄} (U.Init.Prelude.eq~uof~uheq {α₀} {a₁} {b₄} h₅)

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
