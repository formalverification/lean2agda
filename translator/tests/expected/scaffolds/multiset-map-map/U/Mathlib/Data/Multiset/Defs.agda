{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of Multiset:map~umap
-- Lean module Mathlib.Data.Multiset.Defs
module U.Mathlib.Data.Multiset.Defs where
import U.Init.Core
import U.Init.Data.List.Perm
import U.Init.Prelude

Multiset : Set → Set
Multiset α₀ = U.Init.Core.Quotient {U.Init.Prelude.List α₀} (U.Init.Data.List.Perm.List:isSetoid α₀)

Multiset:ofList : {α₀ : Set} → U.Init.Prelude.List α₀ → Multiset α₀
Multiset:ofList {α₀} = U.Init.Prelude.Quot:mk {U.Init.Prelude.List α₀} (U.Init.Core.Setoid:r {U.Init.Prelude.List α₀} ⦃ U.Init.Data.List.Perm.List:isSetoid α₀ ⦄)
