/-
File: translator/Lean2Agda/Core/Modules.lean
-/
import Lean2Agda.Core.Scaffold

/-!
# One Agda module per Lean module

The profile U scaffold of a closure as a tree of Agda modules (issue
M2-8): one module per Lean source module of the closure, at the path its
names sidecar has (`agdaModule root source`), holding the items of the
declarations that module owns, an auxiliary definition with its owner.
Inside a module the printer names a constant by its identifier; a
constant another module owns it names by that module's path and the
identifier (`Naming.qualified`), and the module imports, plainly, exactly
the modules whose constants its items name, so that what the printer
wrote is what Agda reads.  Lean's import graph is acyclic and a
declaration refers only to its own module and the ones that module
imports, so the emitted import graph is acyclic too.

A module whose items pass `split` bytes of text is cut, in item order,
into parts `M.~p1`, `M.~p2`, …, each part opening the earlier parts it
needs, since inside one Lean module every identifier is unqualified; the
module itself becomes a header that re-exports its parts, so that the
qualified names other modules print still resolve.  An item is never
cut, and a `mutual` block is one item.  No Lean module component encodes
to `~p` followed by a digit (`naming.md`), so a part's path is never a
module's.

`docs/translator/modules.md` gives the rule and its measurements, the
library files, and the driver that checks the tree.
-/

namespace Lean2Agda

open Lean

/-- The default `--split`: bytes of printed Agda per module. -/
def defaultSplitThreshold : Nat := 1000000

/-- One emitted Agda module: the Lean module it comes from, its path,
which part of that module it is (`k` of `n`) when the module is split,
the modules it imports plainly, the earlier parts of its own module it
opens, the parts it re-exports (only the header of a split module has
those), its items, and how many of its Lean module's declarations the
scaffold refused (counted in the module, or in the header of a split
one). -/
structure AgdaModule where
  source : ModuleName
  path : List String
  part : Option (Nat × Nat) := none
  imports : Array (List String) := #[]
  opens : Array (List String) := #[]
  reexports : Array (List String) := #[]
  items : Array ScaffoldItem := #[]
  refused : Nat := 0
  deriving Inhabited

def dotted (path : List String) : String := ".".intercalate path

def AgdaModule.name (m : AgdaModule) : String := dotted m.path

def AgdaModule.filePath (m : AgdaModule) (dir : System.FilePath) : System.FilePath :=
  m.path.foldl (· / ·) dir |>.addExtension "agda"

/-- The module's text: the profile's options, the comment, the Lean module
it comes from, a count of the refused declarations when there are any,
the header with the imports, opens and re-exports, then the items,
separated by blank lines. -/
def AgdaModule.render (m : AgdaModule) (comment : String) : String :=
  let origin := match m.part with
    | some (k, n) => s!"-- Lean module {m.source}, part {k} of {n}\n"
    | none => if m.reexports.isEmpty then s!"-- Lean module {m.source}\n"
      else s!"-- Lean module {m.source}, in {m.reexports.size} parts\n"
  let refused := if m.refused == 0 then "" else
    s!"-- refused {m.refused} declarations; refusals.txt names each with its reason\n"
  let lines := m.imports.map (s!"import {dotted ·}") ++ m.opens.map (s!"open import {dotted ·}")
    ++ m.reexports.map (s!"open import {dotted ·} public")
  let header := lines.foldl (fun out l => out ++ l ++ "\n")
    s!"{profileUOptions}\n-- {comment}\n{origin}{refused}module {m.name} where\n"
  m.items.foldl (fun out item => out ++ "\n" ++ item.text) header

/-- The scaffold of a closure as a tree: its root, its modules sorted by
path, what printing counted, and the refused declarations in the
closure's order, auxiliary definitions left out. -/
structure ScaffoldTree where
  root : Root
  modules : Array AgdaModule
  counts : PrintCounts
  refused : Array Refusal := #[]
  deriving Inhabited

/-- Every item of the tree, module by module. -/
def ScaffoldTree.items (t : ScaffoldTree) : Array ScaffoldItem :=
  t.modules.foldl (fun acc m => acc ++ m.items) #[]

/-- The module, or the header of the split module, of a Lean module. -/
def ScaffoldTree.module? (t : ScaffoldTree) (source : ModuleName) : Option AgdaModule :=
  t.modules.find? fun m => m.source == source && m.part.isNone

/-- One tab-separated line per refused declaration: kind, name, reason. -/
def ScaffoldTree.renderRefusals (t : ScaffoldTree) : String :=
  t.refused.foldl (fun out r => out ++ s!"{r.kind.label}\t{r.name}\t{r.reason}\n") ""

/-! ## The library files -/

/-- The library's name, which a consumer's `depend:` line gives: the
root's encoded components joined by dots, or `lean2agda` for no root. -/
def libraryName (root : Root) : String :=
  if root == .anonymous then "lean2agda" else dotted (agdaComponents root)

/-- The `.agda-lib` file at the output root: the library's name and its
include path, the root itself.  It names no library to depend on, since
the profile U scaffold imports nothing outside the tree, and no flags,
since every module states its own in its options pragma. -/
def ScaffoldTree.renderLibrary (t : ScaffoldTree) (comment : String) : String :=
  s!"-- {comment}\nname: {libraryName t.root}\ninclude: .\n"

def ScaffoldTree.libraryFile (t : ScaffoldTree) : String := libraryName t.root ++ ".agda-lib"

/-- The path of the module importing every module of the tree. -/
def ScaffoldTree.everythingPath (t : ScaffoldTree) : List String :=
  agdaComponents t.root ++ ["Everything"]

/-- The module importing every module of the tree, the single Agda process
that checks it all. -/
def ScaffoldTree.renderEverything (t : ScaffoldTree) (comment : String) : String :=
  t.modules.foldl (fun out m => out ++ s!"import {m.name}\n")
    s!"{profileUOptions}\n-- {comment}\n-- every module of the tree\nmodule {dotted t.everythingPath} where\n"

/-! ## Splitting -/

/-- The items in order, cut into parts of at most `threshold` bytes of
text each, counting the blank line before each item; an item larger than
the threshold is a part of its own.  Zero never cuts. -/
def splitItems (threshold : Nat) (items : Array ScaffoldItem) : Array (Array ScaffoldItem) := Id.run do
  if threshold == 0 then return #[items]
  let mut parts := #[]
  let mut current := #[]
  let mut size := 0
  for item in items do
    let n := item.text.utf8ByteSize + 1
    if !current.isEmpty && size + n > threshold then
      parts := parts.push current
      current := #[]
      size := 0
    current := current.push item
    size := size + n
  return parts.push current

/-! ## The tree -/

/-- The qualified name another module prints for constant `n` of module
`owner`. -/
def qualifiedName (root : Root) (owner : ModuleName) (ident : String) : String :=
  dotted (agdaModule root owner) ++ "." ++ ident

/-- The distinct entries of `xs`, sorted by their dotted names. -/
def sortedPaths (xs : Array (List String)) : Array (List String) :=
  (xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]).qsort (dotted · < dotted ·)

/-- The Lean modules, other than its own, whose constants the items name:
an error for a reference that names neither one of the items' own module
nor a constant another module owns. -/
def foreignModules (own : Std.HashSet String) (qualifiedOwner : Std.HashMap String ModuleName)
    (source : ModuleName) (items : Array ScaffoldItem) : Except String (Array ModuleName) := do
  let mut found := #[]
  for item in items do
    for r in item.references do
      unless own.contains r do
        let some o := qualifiedOwner[r]?
          | throw s!"the module of {source} refers to {r}, which nothing declares"
        unless found.contains o do found := found.push o
  return found

/-- The emitted modules of one Lean module: itself, or, when its items
pass the threshold, a header re-exporting its parts and the parts.  Each
imports the Lean modules its items name and opens the earlier parts they
name. -/
def moduleParts (root : Root) (qualifiedOwner : Std.HashMap String ModuleName) (split : Nat)
    (source : ModuleName) (items : Array ScaffoldItem) (refused : Nat) : Except String (Array AgdaModule) := do
  let path := agdaModule root source
  let own : Std.HashSet String := items.foldl (fun s i => i.provides.foldl (·.insert ·) s) {}
  let importsOf (xs : Array ScaffoldItem) : Except String (Array (List String)) := do
    return sortedPaths ((← foreignModules own qualifiedOwner source xs).map (agdaModule root))
  let parts := splitItems split items
  if parts.size ≤ 1 then
    return #[{ source, path, imports := ← importsOf items, items, refused }]
  let partPath (k : Nat) : List String := path ++ [s!"~p{k + 1}"]
  let partOf : Std.HashMap String Nat := (List.range parts.size).foldl (fun m k =>
    parts[k]!.foldl (fun m i => i.provides.foldl (·.insert · k) m) m) {}
  let mut out := #[{ source, path, reexports := (List.range parts.size).toArray.map partPath, refused }]
  for k in [:parts.size] do
    let xs := parts[k]!
    let opened := xs.foldl (fun acc i => i.references.foldl (fun acc r => match partOf[r]? with
      | some j => if j != k && !acc.contains j then acc.push j else acc
      | none => acc) acc) #[]
    out := out.push { source, path := partPath k, part := some (k + 1, parts.size),
                      imports := ← importsOf xs, opens := (opened.qsort (· < ·)).map partPath, items := xs }
  return out

/-- The scaffold tree of a closure that the sharing pass has already
rewritten.  Each declaration belongs to its source module, an auxiliary
definition to its owner's; an auxiliary appears when something the
scaffold prints uses it, and a refused declaration does not appear, nor
do its auxiliaries.  The computation rules of `Quot.lift` and `Quot.ind`
join their postulates' module, which `orderItems` keeps after `Quot.mk`
and `Eq` too.  Within a module the items are ordered as the single
scaffold ordered them; a module none of whose declarations is emitted is
not written. -/
def scaffoldTree (env : Environment) (root : Root) (closure : Closure)
    (split : Nat := defaultSplitThreshold) : Except String ScaffoldTree := do
  let env ← addAuxiliaries env closure
  let decls := closure.declarations
  let byName : Std.HashMap Name Declaration := decls.foldl (fun m d => m.insert d.name d) {}
  let refused := refuseDeclarations decls
  let kept := decls.filter fun d => !refused.contains d.name
  let auxiliaries : Std.HashMap Name Declaration :=
    kept.foldl (fun m d => if d.auxiliary then m.insert d.name d else m) {}
  let needed := reachableAuxiliaries auxiliaries <| kept.foldl (fun acc d =>
    if d.auxiliary then acc else acc ++ constantExprs d.info) #[]
  let recursors := recursorBlocks kept
  let mut owner : Std.HashMap Name ModuleName := {}
  for d in decls do
    let some m := d.sourceModule | throw s!"no source module assigned to {d.name}"
    owner := owner.insert d.name m
  let mut order : Array ModuleName := #[]
  let mut groups : Std.HashMap ModuleName (Array Declaration) := {}
  for decl in kept do
    unless decl.auxiliary && !needed.contains decl.name do
      let m := owner[decl.name]!
      unless groups.contains m do order := order.push m
      groups := groups.insert m ((groups.getD m #[]).push decl)
  let qualifiedOwner : Std.HashMap String ModuleName :=
    owner.fold (fun acc n m => acc.insert (qualifiedName root m (agdaIdent n)) m) {}
  let refusedIn : Std.HashMap ModuleName Nat := refused.fold (fun acc n _ =>
    if byName[n]!.auxiliary then acc else
    let m := owner[n]!
    acc.insert m (acc.getD m 0 + 1)) {}
  let mut counts : PrintCounts := {}
  let mut modules := #[]
  let mut provided : Std.HashSet String := {}
  for m in order do
    let p : Printer := { env, naming := Naming.qualified root fun n => (owner[n]?).filter (· != m) }
    let mut items := #[]
    for decl in groups[m]! do
      if let some (item, c) ← scaffoldItem p byName recursors decl then
        items := items.push item
        counts := counts.add c
      if let some (name, type) := quotRule? decl.name then
        let (item, c) ← ruleItem p name type
        items := items.push item
        counts := counts.add c
    let ordered ← orderItems (breakCycles items)
    provided := ordered.foldl (fun s i => i.provides.foldl (fun s x => s.insert (qualifiedName root m x)) s) provided
    modules := modules ++ (← moduleParts root qualifiedOwner split m ordered (refusedIn.getD m 0))
  -- A reference to another module must name something that module's
  -- items declare, not merely a constant it owns.
  for mod in modules do
    for item in mod.items do
      for r in item.references do
        if qualifiedOwner.contains r && !provided.contains r then
          throw s!"{mod.name} refers to {r}, which no module declares"
  let sorted := modules.qsort (·.name < ·.name)
  let refusals := decls.filterMap fun d => if d.auxiliary then none else refused[d.name]?
  let tree : ScaffoldTree := { root := root, modules := sorted, counts := counts, refused := refusals }
  if sorted.any (·.path == tree.everythingPath) then
    throw s!"the closure has a module at {dotted tree.everythingPath}, the path of the module importing all"
  return tree

end Lean2Agda
