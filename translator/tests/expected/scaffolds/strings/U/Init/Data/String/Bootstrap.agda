{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of StringFixtures:empty StringFixtures:escaped StringFixtures:first StringFixtures:mk~ua StringFixtures:ofList~uab and 4 more
-- Lean module Init.Data.String.Bootstrap
module U.Init.Data.String.Bootstrap where
import U.Init.Prelude

-- theorem
opaque
  String:mk:~uproof~u1 : (data₀ : U.Init.Prelude.List U.Init.Prelude.Char) → U.Init.Prelude.ByteArray:IsValidUTF8 (U.Init.Prelude.List:utf8Encode data₀)
  String:mk:~uproof~u1 data₀ = U.Init.Prelude.ByteArray:IsValidUTF8:intro {U.Init.Prelude.List:utf8Encode data₀} data₀ (U.Init.Prelude.rfl {U.Init.Prelude.ByteArray} {U.Init.Prelude.List:utf8Encode data₀})

String:mk : U.Init.Prelude.List U.Init.Prelude.Char → U.Init.Prelude.String
String:mk data₀ = U.Init.Prelude.String:ofByteArray (U.Init.Prelude.List:utf8Encode data₀) (String:mk:~uproof~u1 data₀)
