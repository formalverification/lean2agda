/-
File: atlas/probes/ValueGraph.lean

Mendoza-Smith's count of classical declarations, and what each of its
three restrictions costs, for the Mathlib of any checkout.  Run it from
a Mathlib checkout (or a Lake package that requires Mathlib) whose
`.olean` files are in place, with the Lean that checkout pins:

    lake env lean /path/to/atlas/probes/ValueGraph.lean

It imports only Mathlib and Lean's core, so it runs at revisions where
the atlas program (`translator/Atlas/`) does not build, and it counts
only the constants the imports declare, never the file's own.

The method (the paper's repository, `scripts/build_decl_graph.py` and
`src/lean/kernel_graph.py`): every constant whose name is not internal
is a node; a definition or theorem has an edge to each non-internal
constant its value uses; a node is classical when `Classical.choice` is
reachable from it.  Each further line lifts one or more of the three
restrictions (an edge from a definition's or theorem's type, the edges
`Lean.collectAxioms` follows out of every other kind of constant, and
paths through internal names); with all three lifted the count is the
atlas's exact one.  Every line counts non-internal constants only.
-/
import Mathlib

open Lean Elab Command

/-- The edges out of a constant: always a definition's or theorem's
value; with `types`, its type; with `kinds`, what `Lean.collectAxioms`
follows out of an axiom, an opaque constant, an inductive type, a
constructor and a recursor. -/
def valueGraphEdges (types kinds : Bool) : ConstantInfo → Array Name
  | .defnInfo v   => (if types then v.type.getUsedConstants else #[]) ++ v.value.getUsedConstants
  | .thmInfo v    => (if types then v.type.getUsedConstants else #[]) ++ v.value.getUsedConstants
  | .axiomInfo v  => if kinds then v.type.getUsedConstants else #[]
  | .opaqueInfo v => if kinds then v.type.getUsedConstants ++ v.value.getUsedConstants else #[]
  | .quotInfo _   => #[]
  | .ctorInfo v   => if kinds then v.type.getUsedConstants else #[]
  | .recInfo v    => if kinds then v.type.getUsedConstants else #[]
  | .inductInfo v => if kinds then v.type.getUsedConstants ++ v.ctors.toArray else #[]

/-- How many non-internal constants reach `Classical.choice` (the axiom
itself included) in the graph `valueGraphEdges types kinds` gives,
through internal names too when `internal`. -/
def valueGraphClassical (consts : Array (Name × ConstantInfo)) (index : Std.HashMap Name Nat)
    (types kinds internal : Bool) : Nat := Id.run do
  let keep (n : Name) := internal || !n.isInternal
  let mut usedBy : Array (Array Nat) := Array.replicate consts.size #[]
  for h : i in [0:consts.size] do
    let (n, ci) := consts[i]
    unless keep n do continue
    for d in valueGraphEdges types kinds ci do
      if keep d then
        if let some j := index[d]? then
          if j != i then usedBy := usedBy.modify j (·.push i)
  let some c := index[``Classical.choice]? | return 0
  let mut seen : Array Bool := (Array.replicate consts.size false).set! c true
  let mut queue : Array Nat := #[c]
  let mut next : Nat := 0
  while h : next < queue.size do
    let node := queue[next]
    next := next + 1
    for user in usedBy[node]! do
      unless seen[user]! do
        seen := seen.set! user true
        queue := queue.push user
  return queue.foldl (fun k i => if consts[i]!.1.isInternal then k else k + 1) 0

elab "#value_graph" : command => do
  let env ← getEnv
  let consts := env.constants.toList.toArray.filter fun (n, _) => (env.getModuleIdxFor? n).isSome
  let mut index : Std.HashMap Name Nat := {}
  for h : i in [0:consts.size] do
    index := index.insert consts[i].1 i
  -- The annotations matter: with Mathlib imported, an unannotated 0 that
  -- reaches `m!` below is elaborated as a `MessageData` at some versions.
  let population : Nat := consts.foldl (fun (k : Nat) (n, _) => if n.isInternal then k else k + 1) 0
  logInfo m!"imported constants {consts.size}; population (not internal) {population}"
  let lines : List (String × Bool × Bool × Bool) := [
    ("their method", false, false, false),
    ("with types", true, false, false),
    ("with other kinds", false, true, false),
    ("with internal names", false, false, true),
    ("with types and other kinds", true, true, false),
    ("with types and internal names", true, false, true),
    ("with other kinds and internal names", false, true, true),
    ("with all three (exact)", true, true, true)]
  for (label, types, kinds, internal) in lines do
    logInfo m!"classical, {label}: {valueGraphClassical consts index types kinds internal}"

#value_graph
