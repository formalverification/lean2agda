{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of RecursorFixtures:Doc RecursorFixtures:Doc:~usizeOf~u1 RecursorFixtures:Doc:~usizeOf~u2 RecursorFixtures:Doc:~usizeOf~u2~ueq RecursorFixtures:Doc:~usizeOf~u3 and 251 more
-- Lean module Init.SimpLemmas
module U.Init.SimpLemmas where
import U.Init.Core
import U.Init.Prelude

-- theorem
opaque
  eq~ufalse : {p₀ : Set} → U.Init.Prelude.Not p₀ → U.Init.Prelude.Eq {Set} p₀ U.Init.Prelude.False
  eq~ufalse {p₀} h₁ = U.Init.Core.propext {p₀} {U.Init.Prelude.False} (U.Init.Core.Iff:intro {p₀} {U.Init.Prelude.False} (λ (h₂ : p₀) → U.Init.Prelude.absurd {p₀} {U.Init.Prelude.False} h₂ h₁) (λ (h₂ : U.Init.Prelude.False) → U.Init.Prelude.False:elim {p₀} h₂))

-- theorem
opaque
  eq~ufalse~x27~ : {p₀ : Set} → (p₀ → U.Init.Prelude.False) → U.Init.Prelude.Eq {Set} p₀ U.Init.Prelude.False
  eq~ufalse~x27~ {p₀} h₁ = eq~ufalse {p₀} h₁

-- theorem
opaque
  eq~utrue : {p₀ : Set} → p₀ → U.Init.Prelude.Eq {Set} p₀ U.Init.Prelude.True
  eq~utrue {p₀} h₁ = U.Init.Core.propext {p₀} {U.Init.Prelude.True} (U.Init.Core.Iff:intro {p₀} {U.Init.Prelude.True} (λ (x₂ : p₀) → U.Init.Core.trivial) (λ (x₂ : U.Init.Prelude.True) → h₁))

-- theorem
opaque
  not~ufalse~ueq~utrue : U.Init.Prelude.Eq {Set} (U.Init.Prelude.Not U.Init.Prelude.False) U.Init.Prelude.True
  not~ufalse~ueq~utrue = eq~utrue {U.Init.Prelude.Not U.Init.Prelude.False} (U.Init.Prelude.False:elim {U.Init.Prelude.False})

-- theorem
opaque
  of~ueq~utrue : {p₀ : Set} → U.Init.Prelude.Eq {Set} p₀ U.Init.Prelude.True → p₀
  of~ueq~utrue {p₀} h₁ = U.Init.Prelude.Eq:rec {Set} {U.Init.Prelude.True} {λ (x₂ : Set) → λ (h₃ : U.Init.Prelude.Eq {Set} U.Init.Prelude.True x₂) → x₂} U.Init.Core.trivial {p₀} (U.Init.Prelude.Eq:symm {Set} {p₀} {U.Init.Prelude.True} h₁)
