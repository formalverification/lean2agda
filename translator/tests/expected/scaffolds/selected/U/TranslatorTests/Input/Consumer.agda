{-# OPTIONS --type-in-type #-}
-- lean2agda, profile U: the scaffold of the closure of Fixtures:selected
-- Lean module TranslatorTests.Input.Consumer
module U.TranslatorTests.Input.Consumer where
import U.Init.Prelude
import U.TranslatorTests.Input.Base

~uprivate:TranslatorTests:Input:Consumer:~n0:Fixtures:secret : U.Init.Prelude.Nat
~uprivate:TranslatorTests:Input:Consumer:~n0:Fixtures:secret = U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ U.TranslatorTests.Input.Base.Fixtures:token (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄)

Fixtures:selected : U.Init.Prelude.Nat
Fixtures:selected = ~uprivate:TranslatorTests:Input:Consumer:~n0:Fixtures:secret
