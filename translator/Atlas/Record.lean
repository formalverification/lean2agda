/-
File: translator/Atlas/Record.lean
-/
import Lean.Data.Json
import Atlas.Graph

/-!
# Atlas.Record

The pure core of the axiom atlas (issue M1-11): what the atlas records
about one constant, the tier its axioms imply, and the lines of the
NDJSON file, rendered with their fields in a fixed order.  Nothing here
reads an environment or a file; `Atlas.Collect` fills a record from the
environment and `Atlas.Main` writes the lines.
-/

namespace Atlas

open Lean

/-- The version of the record format, written in the file's first line.
Issue M4-1 defines version 1 in `atlas/SCHEMA.md`. -/
def formatVersion : Nat := 0

/-- The axioms that tiers T0 to T2 admit.  Any other axiom puts a constant
in T3: `sorryAx`, `Lean.ofReduceBool`, the compiler's `lcProof`, and the
axiom `native_decide` generates for each use. -/
def standardAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- A tier, as `corpus/SCHEMA.md` ("Tiers from axioms") computes it. -/
inductive Tier where
  | t0 | t1 | t2 | t3
  deriving BEq, Repr, Inhabited

/-- The tier's name, `T0` to `T3`. -/
def Tier.label : Tier → String
  | .t0 => "T0"
  | .t1 => "T1"
  | .t2 => "T2"
  | .t3 => "T3"

/-- The tier the axioms imply; the first rule that applies decides. -/
def tierOf (axioms : Array Name) : Tier :=
  if axioms.any (!standardAxioms.contains ·) then .t3
  else if axioms.contains ``Classical.choice then .t2
  else if axioms.isEmpty then .t0
  else .t1

/-- The kind of a constant, named after its `ConstantInfo` constructor. -/
def kindOf : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "definition"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "constructor"
  | .recInfo _    => "recursor"

/-- Names in the atlas's order: as strings, compared character by
character, which is UTF-8 byte order, so that any other tool can check
it and the file does not depend on Lean's hash order. -/
def sortNames (names : Array Name) : Array Name :=
  (names.map fun n => (toString n, n)).qsort (·.1 < ·.1) |>.map (·.2)

/-- What the atlas records about one constant.

`axioms` is the constant's exact axiom set (`Atlas.Graph.axiomSets`),
sorted by `sortNames`; `leanOmits` is the part of it that
`Lean.collectAxioms`, and so `#print axioms`, leaves out, empty for all
but a few constants.  The four flags about the name are as follows:
`isPrivate` is Lean's `isPrivateName`; `isInternal` is `Name.isInternal` (some component
begins with an underscore, as in `_private` and `_proof_1`), the filter
of Mendoza-Smith's graph and of lean4export's default export; `isAuto`
is Batteries' test (`Atlas.isAutoDecl`), which judges a private name by
the name it was written with.  Lean's own `isAutoDeclOrPrivate_Internal`
is `isAuto || isPrivate`. -/
structure Record where
  name            : Name
  module          : Name
  kind            : String
  axioms          : Array Name
  leanOmits       : Array Name
  isNoncomputable : Bool
  isUnsafe        : Bool
  isPartial       : Bool
  isPrivate       : Bool
  isInternal      : Bool
  isAuto          : Bool

/-- A JSON object with its fields in the order given, each value already
rendered; `Json.mkObj` would sort the fields by key. -/
def renderObject (fields : List (String × String)) : String :=
  "{" ++ ",".intercalate (fields.map fun (k, v) => (Json.str k).compress ++ ":" ++ v) ++ "}"

/-- A name as a JSON string, escaped as Lean prints it (`«...»` around a
component that is not an identifier), so that Lean can read it back. -/
def renderName (n : Name) : String := (Json.str (toString n)).compress

/-- Names as a JSON array. -/
def renderNames (ns : Array Name) : String := "[" ++ ",".intercalate (ns.map renderName).toList ++ "]"

/-- A string, a number or a Boolean as JSON. -/
def renderStr (s : String) : String := (Json.str s).compress
def renderNat (n : Nat) : String := toString n
def renderBool (b : Bool) : String := toString b

/-- The record's line in the NDJSON file. -/
def Record.render (r : Record) : String :=
  renderObject [
    ("name", renderName r.name),
    ("module", renderName r.module),
    ("kind", renderStr r.kind),
    ("axioms", renderNames r.axioms),
    ("tier", renderStr (tierOf r.axioms).label),
    ("lean_omits", renderNames r.leanOmits),
    ("noncomputable", renderBool r.isNoncomputable),
    ("unsafe", renderBool r.isUnsafe),
    ("partial", renderBool r.isPartial),
    ("private", renderBool r.isPrivate),
    ("internal", renderBool r.isInternal),
    ("auto", renderBool r.isAuto)
  ]

/-- Where the records came from: the pinned versions and what was
imported.  It is the file's first line. -/
structure Header where
  leanVersion  : String
  leanCommit   : String
  mathlibTag   : String
  mathlibRev   : String
  imports      : Array Name
  constants    : Nat

/-- The header's line. -/
def Header.render (h : Header) : String :=
  renderObject [("atlas", renderObject [
    ("version", renderNat formatVersion),
    ("lean", renderStr h.leanVersion),
    ("lean_commit", renderStr h.leanCommit),
    ("mathlib", renderStr h.mathlibTag),
    ("mathlib_commit", renderStr h.mathlibRev),
    ("imports", renderNames h.imports),
    ("constants", renderNat h.constants)
  ])]

/-- The file's last line: the number of records, and the two numbers of
Mendoza-Smith's method, which need the whole graph rather than one
record.  A file without it was cut short, and the report refuses it. -/
def endLine (records : Nat) (count : ValueGraphCount) : String :=
  renderObject [("end", renderObject [
    ("records", renderNat records),
    ("value_graph", renderObject [
      ("population", renderNat count.population),
      ("classical", renderNat count.classical)])
  ])]

end Atlas
