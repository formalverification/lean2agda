/-
File: translator/Lean2Agda/Core/InductiveShape.lean
-/
import Lean.Environment

/-!
# The shape of an inductive type in Agda

How a Lean inductive type maps onto an Agda declaration: whether it
becomes a `record` or a `data` type.  A pure function of the environment,
for the emitter in `Inductive.lean`, which declares the types.
`docs/translator/inductives.md` gives the rules and the probes behind
them.
-/

namespace Lean2Agda

open Lean

/-- Whether a type becomes an Agda record: structure-like (one
constructor, no indices, not recursive), and not `String`, which
`BUILTIN STRING` needs as a postulate.  Records have eta in Agda, as
structure-like types have in Lean; everything else becomes `data`. -/
def isAgdaRecord (_env : Environment) (v : InductiveVal) : Bool :=
  v.ctors.length == 1 && v.numIndices == 0 && !v.isRec && v.name != ``String

def isAgdaRecordName (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.inductInfo v) => isAgdaRecord env v
  | _ => false

end Lean2Agda
