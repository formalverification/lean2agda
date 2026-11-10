{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of Fixtures:selected
-- Lean module TranslatorTests.Input.Base
module U.TranslatorTests.Input.Base where
import U.Init.Prelude

Fixtures:token : U.Init.Prelude.Nat
Fixtures:token = U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 17 ⦃ U.Init.Prelude.instOfNatNat 17 ⦄
