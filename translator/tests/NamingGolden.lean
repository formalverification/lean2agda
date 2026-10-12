/-
File: translator/tests/NamingGolden.lean
-/
import Lean2Agda.Main

open Lean Lean2Agda

#eval show IO Unit from do
  let moduleName := `Init.Data.Nat.Gcd
  let env ← importEnvironment #[moduleName]
  let names ← IO.ofExcept (selectRoots env #[moduleName] #[])
  for n in names do IO.println s!"{n}\t{agdaIdent n}"
