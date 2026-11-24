{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of StringFixtures:empty StringFixtures:escaped StringFixtures:first StringFixtures:mk~ua StringFixtures:ofList~uab and 4 more
-- Lean module TranslatorTests.Input.Strings
module U.TranslatorTests.Input.Strings where
import U.Init.Data.String.Bootstrap
import U.Init.Prelude

StringFixtures:empty : U.Init.Prelude.String
StringFixtures:empty = U.Init.Prelude.String:~ulit:~e

StringFixtures:escaped : U.Init.Prelude.String
StringFixtures:escaped = U.Init.Prelude.String:~ulit:a~x22~b~x5c~c~xa~

StringFixtures:first : U.Init.Prelude.String
StringFixtures:first = U.Init.Prelude.String:~ulit:shared

-- theorem
opaque
  StringFixtures:mk~ua : U.Init.Prelude.Eq {U.Init.Prelude.String} U.Init.Prelude.String:~ulit:a (U.Init.Data.String.Bootstrap.String:mk (U.Init.Prelude.List:cons {U.Init.Prelude.Char} (U.Init.Prelude.Char:ofNat 97) (U.Init.Prelude.List:nil {U.Init.Prelude.Char})))
  StringFixtures:mk~ua = U.Init.Prelude.rfl {U.Init.Prelude.String} {U.Init.Prelude.String:~ulit:a}

-- theorem
opaque
  StringFixtures:ofList~uab : U.Init.Prelude.Eq {U.Init.Prelude.String} U.Init.Prelude.String:~ulit:ab (U.Init.Prelude.String:ofList (U.Init.Prelude.List:cons {U.Init.Prelude.Char} (U.Init.Prelude.Char:ofNat 97) (U.Init.Prelude.List:cons {U.Init.Prelude.Char} (U.Init.Prelude.Char:ofNat 98) (U.Init.Prelude.List:nil {U.Init.Prelude.Char}))))
  StringFixtures:ofList~uab = U.Init.Prelude.rfl {U.Init.Prelude.String} {U.Init.Prelude.String:~ulit:ab}

StringFixtures:repeated:~ushare:~n1 : U.Init.Prelude.List (U.Init.Prelude.List U.Init.Prelude.String) → U.Init.Prelude.List (U.Init.Prelude.List U.Init.Prelude.String)
StringFixtures:repeated:~ushare:~n1 = U.Init.Prelude.List:cons {U.Init.Prelude.List U.Init.Prelude.String} (U.Init.Prelude.List:cons {U.Init.Prelude.String} U.Init.Prelude.String:~ulit:a (U.Init.Prelude.List:cons {U.Init.Prelude.String} U.Init.Prelude.String:~ulit:b (U.Init.Prelude.List:cons {U.Init.Prelude.String} U.Init.Prelude.String:~ulit:c (U.Init.Prelude.List:cons {U.Init.Prelude.String} U.Init.Prelude.String:~ulit:d (U.Init.Prelude.List:cons {U.Init.Prelude.String} U.Init.Prelude.String:~ulit:e (U.Init.Prelude.List:cons {U.Init.Prelude.String} U.Init.Prelude.String:~ulit:f (U.Init.Prelude.List:nil {U.Init.Prelude.String})))))))

StringFixtures:repeated : U.Init.Prelude.List (U.Init.Prelude.List U.Init.Prelude.String)
StringFixtures:repeated = StringFixtures:repeated:~ushare:~n1 (StringFixtures:repeated:~ushare:~n1 (U.Init.Prelude.List:nil {U.Init.Prelude.List U.Init.Prelude.String}))

StringFixtures:second : U.Init.Prelude.List U.Init.Prelude.String
StringFixtures:second = U.Init.Prelude.List:cons {U.Init.Prelude.String} U.Init.Prelude.String:~ulit:shared (U.Init.Prelude.List:cons {U.Init.Prelude.String} U.Init.Prelude.String:~ulit:ab (U.Init.Prelude.List:nil {U.Init.Prelude.String}))

-- theorem
opaque
  StringFixtures:toByteArray~uab : U.Init.Prelude.Eq {U.Init.Prelude.ByteArray} (U.Init.Prelude.String:toByteArray U.Init.Prelude.String:~ulit:ab) (U.Init.Prelude.List:utf8Encode (U.Init.Prelude.List:cons {U.Init.Prelude.Char} (U.Init.Prelude.Char:ofNat 97) (U.Init.Prelude.List:cons {U.Init.Prelude.Char} (U.Init.Prelude.Char:ofNat 98) (U.Init.Prelude.List:nil {U.Init.Prelude.Char}))))
  StringFixtures:toByteArray~uab = U.Init.Prelude.rfl {U.Init.Prelude.ByteArray} {U.Init.Prelude.String:toByteArray U.Init.Prelude.String:~ulit:ab}

StringFixtures:widths : U.Init.Prelude.String
StringFixtures:widths = U.Init.Prelude.String:~ulit:a~x3bb~~x271d~~x1d538~
