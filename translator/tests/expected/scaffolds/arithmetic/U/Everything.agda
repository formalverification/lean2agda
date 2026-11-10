{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of ArithmeticFixtures:add~uone ArithmeticFixtures:add~usucc ArithmeticFixtures:add~uzero ArithmeticFixtures:beq~usucc~usucc ArithmeticFixtures:beq~usucc~uzero and 49 more
-- every module of the tree
module U.Everything where
import U.Init.Core
import U.Init.Data.Nat.Basic
import U.Init.Data.Nat.Bitwise.Basic
import U.Init.Data.Nat.Coprime
import U.Init.Data.Nat.Div.Basic
import U.Init.Data.Nat.Gcd
import U.Init.Prelude
import U.Init.SimpLemmas
import U.Init.WF
import U.TranslatorTests.Input.Arithmetic
import U.TranslatorTests.Input.Numerals
