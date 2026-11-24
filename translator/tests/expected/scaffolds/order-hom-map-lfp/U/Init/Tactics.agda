{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of OrderHom:map~ulfp
-- Lean module Init.Tactics
module U.Init.Tactics where
import U.Init.Prelude

autoParam : Set → U.Init.Prelude.Lean:Syntax → Set
autoParam α₀ tactic₁ = α₀
