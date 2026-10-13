/-
File: translator/scripts/InductiveTypes.lean

The inductive types of a set of declarations, one name per line, sorted,
to pass as roots to `lake exe lean2agda --out DIR MODULE -- …`: a scaffold
whose roots are inductive types declares every one of them, with their
constructors, while the definitions and theorems their types need stay
postulates.  Run from translator/ inside the Nix shell, configured by the
environment:

+  `INDUCTIVE_CLOSURE=Init.Core`: the inductive types of the closure of
   that module's declarations (the acceptance criterion of issue M2-4,
   which `tests/run.sh` checks);
+  otherwise those declared in modules under `INDUCTIVE_PREFIXES`
   (default `Init`), in the environment of `INDUCTIVE_IMPORTS` (default
   `Init`), and with `INDUCTIVE_FILTER=nested-or-mutual` only the nested
   or mutual ones.

    INDUCTIVE_CLOSURE=Init.Core lake env lean scripts/InductiveTypes.lean
    INDUCTIVE_IMPORTS=Lean INDUCTIVE_PREFIXES='Init Std Lean' \
      INDUCTIVE_FILTER=nested-or-mutual lake env lean scripts/InductiveTypes.lean

`docs/translator/inductives.md` reports the runs.
-/
import Lean2Agda.Main

open Lean Lean2Agda

def words (key fallback : String) : IO (List Name) := do
  let text := (← IO.getEnv key).getD fallback
  return text.splitOn " " |>.filter (!·.isEmpty) |>.map String.toName

def isInductive (env : Environment) (filter : String) (n : Name) : Bool :=
  match env.find? n with
  | some (.inductInfo v) => filter != "nested-or-mutual" || v.numNested > 0 || v.all.length > 1
  | _ => false

#eval show IO Unit from do
  let filter := (← IO.getEnv "INDUCTIVE_FILTER").getD ""
  let names ← match ← IO.getEnv "INDUCTIVE_CLOSURE" with
    | some module => do
      let module := module.toName
      let env ← importEnvironment #[module]
      let roots ← IO.ofExcept (selectRoots env #[module] #[])
      let closure ← IO.ofExcept (dependencyClosure env roots)
      pure (closure.declarations.map (·.name) |>.filter (isInductive env filter))
    | none => do
      let env ← importEnvironment (← words "INDUCTIVE_IMPORTS" "Init").toArray
      let prefixes ← words "INDUCTIVE_PREFIXES" "Init"
      pure <| env.constants.fold (init := #[]) fun acc n _ =>
        let inScope := (moduleOf env n).any fun m => prefixes.any (·.isPrefixOf m)
        if inScope && isInductive env filter n then acc.push n else acc
  for n in sortNames names do IO.println n
