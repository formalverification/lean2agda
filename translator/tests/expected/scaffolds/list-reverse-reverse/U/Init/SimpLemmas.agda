{-# OPTIONS --type-in-type #-}
-- lean2agda, profile U: the scaffold of the closure of List:reverse~ureverse
-- Lean module Init.SimpLemmas
module U.Init.SimpLemmas where
import U.Init.Core
import U.Init.Prelude

-- theorem
opaque
  eq~utrue : {p₀ : Set} → p₀ → U.Init.Prelude.Eq {Set} p₀ U.Init.Prelude.True
  eq~utrue {p₀} h₁ = U.Init.Core.propext {p₀} {U.Init.Prelude.True} (U.Init.Core.Iff:intro {p₀} {U.Init.Prelude.True} (λ (x₂ : p₀) → U.Init.Core.trivial) (λ (x₂ : U.Init.Prelude.True) → h₁))

-- theorem
opaque
  eq~uself : {α₀ : Set} → (a₁ : α₀) → U.Init.Prelude.Eq {Set} (U.Init.Prelude.Eq {α₀} a₁ a₁) U.Init.Prelude.True
  eq~uself {α₀} a₁ = eq~utrue {U.Init.Prelude.Eq {α₀} a₁ a₁} (U.Init.Prelude.rfl {α₀} {a₁})

-- theorem
opaque
  of~ueq~utrue : {p₀ : Set} → U.Init.Prelude.Eq {Set} p₀ U.Init.Prelude.True → p₀
  of~ueq~utrue {p₀} h₁ = U.Init.Prelude.Eq:rec {Set} {U.Init.Prelude.True} {λ (x₂ : Set) → λ (h₃ : U.Init.Prelude.Eq {Set} U.Init.Prelude.True x₂) → x₂} U.Init.Core.trivial {p₀} (U.Init.Prelude.Eq:symm {Set} {p₀} {U.Init.Prelude.True} h₁)
