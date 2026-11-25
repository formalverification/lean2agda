/-
File: translator/scripts/ModuleList.lean

The modules an import brings in, one name per line, sorted, to pass to
`lake exe lean2agda` as the modules whose declarations are the roots: the
translator takes the roots from the modules it is given, not from what
they import, so "every constant of `Init`" is every module `Init`
imports.  Run from translator/ inside the Nix shell, configured by the
environment:

+  `MODULE_IMPORTS` (default `Init`): the modules to import;
+  `MODULE_PREFIXES` (default the same): keep the modules whose names
   begin with one of these.

    lake exe lean2agda --specialize --stats $(lake env lean scripts/ModuleList.lean)

`docs/translator/levels.md` reports the run.
-/
import Lean2Agda.Main

open Lean Lean2Agda

def words (key fallback : String) : IO (List Name) := do
  let text := (← IO.getEnv key).getD fallback
  return text.splitOn " " |>.filter (!·.isEmpty) |>.map String.toName

#eval show IO Unit from do
  let imports ← words "MODULE_IMPORTS" "Init"
  let prefixes ← words "MODULE_PREFIXES" (" ".intercalate (imports.map toString))
  let env ← importEnvironment imports.toArray
  let kept := env.header.moduleNames.filter fun m => prefixes.any (·.isPrefixOf m)
  for m in sortNames kept do IO.println m
