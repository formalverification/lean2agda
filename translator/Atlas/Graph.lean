/-
File: translator/Atlas/Graph.lean
-/
import Lean.Declaration
import Lean.Util.FoldConsts
import Std.Data.HashMap

/-!
# Atlas.Graph

The dependency graph of an environment's constants, and the two answers
the atlas computes from it: the exact axiom set of every constant, and
the count of Mendoza-Smith's method (a graph of definition and theorem
values alone).  Everything here is pure; the constants are an array,
and a constant is named by its index in it.

Why not `Lean.collectAxioms` alone.  At Lean v4.33.1 it caches the
result of a constant reached while one of its own dependencies is still
being visited, with that dependency counted as having no axioms.  The
cycles where that happens are an inductive type and its constructors
(each constructor's type mentions the type, and the type depends on its
constructors) and mutually recursive `unsafe` definitions; the per-module
table each `.olean` carries keeps the incomplete answer (Lean issue
15226).  Reachability over the same edges has no such order dependence:
a constant depends on an axiom exactly when the axiom is reachable from
it.  `Atlas.Main` checks that Lean never reports an axiom the graph does
not reach, and the records name what Lean omits.
-/

namespace Atlas

open Lean

/-- The constants `Lean.collectAxioms` follows from a constant: the
constants its type uses, those its value uses (definitions, theorems,
opaque constants), and an inductive type's constructors. -/
def directDeps : ConstantInfo → Array Name
  | .axiomInfo v  => v.type.getUsedConstants
  | .defnInfo v   => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v    => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _   => #[]
  | .ctorInfo v   => v.type.getUsedConstants
  | .recInfo v    => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

/-- The edges of Mendoza-Smith's dependency graph: a definition's or a
theorem's value, without its type, and no edge out of any other kind of
constant.  Internal names are left out, as nodes and as targets. -/
def valueDeps (n : Name) : ConstantInfo → Array Name
  | .defnInfo v => if n.isInternal then #[] else v.value.getUsedConstants.filter (!·.isInternal)
  | .thmInfo v  => if n.isInternal then #[] else v.value.getUsedConstants.filter (!·.isInternal)
  | _           => #[]

/-- Each constant's index in the array. -/
def indexOf (constants : Array (Name × ConstantInfo)) : Std.HashMap Name Nat :=
  constants.size.fold (fun i _ acc => acc.insert constants[i].1 i) {}

/-- The graph reversed: for each constant, the constants whose `deps`
name it.  A name `deps` gives that is not a constant is dropped, as
`collectAxioms` drops it, and so is an edge from a constant to itself. -/
def usedBy (constants : Array (Name × ConstantInfo)) (index : Std.HashMap Name Nat)
    (deps : Name → ConstantInfo → Array Name) : Array (Array Nat) :=
  constants.size.fold (init := Array.replicate constants.size #[]) fun i _ acc =>
    (deps constants[i].1 constants[i].2).foldl (init := acc) fun acc d =>
      match index[d]? with
      | some j => if j == i then acc else acc.modify j (·.push i)
      | none   => acc

/-- The constants from which `start` is reachable, `start` included:
breadth first along the reversed edges. -/
def reaching (usedBy : Array (Array Nat)) (start : Nat) : Array Nat := Id.run do
  let mut seen : Array Bool := (Array.replicate usedBy.size false).set! start true
  let mut queue : Array Nat := #[start]
  let mut next : Nat := 0
  while h : next < queue.size do
    let node := queue[next]
    next := next + 1
    for user in usedBy[node]! do
      unless seen[user]! do
        seen := seen.set! user true
        queue := queue.push user
  return queue

/-- The exact axiom set of every constant, aligned with the array: the
axioms reachable from it along `directDeps`, in the order the axioms
appear in the array. -/
def axiomSets (constants : Array (Name × ConstantInfo)) : Array (Array Name) :=
  let index := indexOf constants
  let graph := usedBy constants index fun _ ci => directDeps ci
  let axioms := (Array.range constants.size).filter fun i => constants[i]!.2 matches .axiomInfo _
  axioms.foldl (init := Array.replicate constants.size #[]) fun acc a =>
    (reaching graph a).foldl (init := acc) fun acc i => acc.modify i (·.push constants[a]!.1)

/-- Mendoza-Smith's two numbers for an environment: the constants whose
names are not internal, and how many of them reach `Classical.choice`
along `valueDeps` (the axiom itself included). -/
structure ValueGraphCount where
  population : Nat
  classical  : Nat

/-- Count by Mendoza-Smith's method (the repository of the paper,
`scripts/build_decl_graph.py` and `src/lean/kernel_graph.py`): every
constant whose name is not internal is a node, a definition or theorem
has an edge to each non-internal constant its value uses, and a node is
classical when `Classical.choice` is reachable from it. -/
def valueGraphCount (constants : Array (Name × ConstantInfo)) : ValueGraphCount :=
  let index := indexOf constants
  let population := constants.foldl (fun k (n, _) => if n.isInternal then k else k + 1) 0
  match index[``Classical.choice]? with
  | none   => { population, classical := 0 }
  | some c => { population, classical := (reaching (usedBy constants index valueDeps) c).size }

end Atlas
