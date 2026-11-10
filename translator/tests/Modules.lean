/-
File: translator/tests/Modules.lean
-/
import Lean2Agda.Main
import TranslatorTests

/-!
The tree of modules (issue M2-8), on the two-module fixture
`TranslatorTests.Input.Base` and `Consumer`: each declaration in its
source module's Agda module, an auxiliary definition with its owner;
references to another module qualified and references inside one bare;
each module importing exactly the modules its items name; and the split
rule, with a threshold that falls inside the fixture's `mutual` block,
which must stay whole.  `tests/run.sh` checks the trees of the golden
closures and checks one of them with `agda_check.py`.
-/

open Lean Lean2Agda

namespace ModulesTests

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def treeOf (env : Environment) (roots : Array Name) (split : Nat := defaultSplitThreshold)
    (share : Nat := defaultShareThreshold) : IO ScaffoldTree := do
  let closure ← IO.ofExcept (dependencyClosure env roots)
  IO.ofExcept (scaffoldTree env `U (← IO.ofExcept (shareClosure env share closure)) split)

def moduleOf (t : ScaffoldTree) (source : Name) : IO AgdaModule := do
  let some m := t.module? source | throw (IO.userError s!"no module for {source}")
  return m

def providers (m : AgdaModule) : Array String := m.items.foldl (· ++ ·.provides) #[]

def base : Name := `TranslatorTests.Input.Base
def consumer : Name := `TranslatorTests.Input.Consumer

def checkOwnersAndImports (env : Environment) : IO Unit := do
  let t ← treeOf env #[``Fixtures.selected, ``Fixtures.mixed, ``Fixtures.projection]
  -- One module per source module, sorted by path, at the sidecar's path.
  require (t.modules.map (·.name) == #["U.Init.Prelude", "U.TranslatorTests.Input.Base",
    "U.TranslatorTests.Input.Consumer"]) s!"modules: {t.modules.map (·.name)}"
  let prelude ← moduleOf t `Init.Prelude
  let b ← moduleOf t base
  let c ← moduleOf t consumer
  -- Owners: each constant in its source module.
  require ((providers c).contains "Fixtures:selected" && (providers b).contains "Fixtures:token"
    && (providers prelude).contains "Nat" && !(providers c).contains "Nat") "owners"
  -- A reference to another module is qualified by that module's path; a
  -- reference inside the owner is bare.
  let some selected := c.items.find? (·.provides.contains "Fixtures:selected") | throw (IO.userError "selected")
  require (selected.text.startsWith "Fixtures:selected : U.Init.Prelude.Nat\n") s!"selected: {selected.text}"
  let some token := b.items.find? (·.provides.contains "Fixtures:token") | throw (IO.userError "token")
  require (token.text.startsWith "Fixtures:token : U.Init.Prelude.Nat\nFixtures:token = U.Init.Prelude.OfNat:ofNat")
    s!"token: {token.text}"
  let some projection := c.items.find? (·.provides.contains "Fixtures:projection") | throw (IO.userError "projection")
  -- A projection from another module's record goes through its
  -- projection function, which sits beside the record.
  require (projection.text.endsWith "= U.TranslatorTests.Input.Base.Fixtures:Box:element b₀\n")
    s!"a projection from another module's record: {projection.text}"
  require (prelude.items.all fun i => (i.text.splitOn "U.").length == 1) "Init.Prelude names another module"
  -- Imports: exactly the modules whose constants the items name, plainly.
  require (prelude.imports.isEmpty && b.imports == #[["U", "Init", "Prelude"]]
    && c.imports == #[["U", "Init", "Prelude"], ["U", "TranslatorTests", "Input", "Base"]])
    s!"imports: {prelude.imports} {b.imports} {c.imports}"
  let text := c.render "c"
  require (text.startsWith s!"{profileUOptions}\n-- c\n-- Lean module TranslatorTests.Input.Consumer\nmodule U.TranslatorTests.Input.Consumer where\nimport U.Init.Prelude\nimport U.TranslatorTests.Input.Base\n\n")
    s!"header: {text.take 300}"
  -- A module that names only Init.Prelude imports only it: Base's
  -- items never name Consumer's.
  let onlyBase ← treeOf env #[``Fixtures.token]
  require (onlyBase.modules.map (·.name) == #["U.Init.Prelude", "U.TranslatorTests.Input.Base"])
    s!"a closure inside Base: {onlyBase.modules.map (·.name)}"
  -- An auxiliary definition belongs to its owner's module.  At threshold
  -- 2 the sharing pass makes some; each sits beside its owner.
  let shared ← treeOf env #[``Fixtures.mixed] (share := 2)
  for m in shared.modules do
    for item in m.items do
      for p in item.provides do
        let parts := p.splitOn ":~ushare:"
        if parts.length == 2 then
          require (m.items.any (·.provides.contains parts[0]!)) s!"{p} is not beside its owner in {m.name}"
  require (shared.items.any fun i => i.provides.any (·.endsWith ":~n1"))
    "the sharing pass made no auxiliary definition"
  -- The library files and the module importing everything.
  require (t.renderLibrary "c" == "-- c\nname: U\ninclude: .\n" && t.libraryFile == "U.agda-lib") "library"
  require (t.renderEverything "c" == s!"{profileUOptions}\n-- c\n-- every module of the tree\nmodule U.Everything where\n"
    ++ "import U.Init.Prelude\nimport U.TranslatorTests.Input.Base\nimport U.TranslatorTests.Input.Consumer\n")
    s!"Everything: {t.renderEverything "c"}"

def checkSplit (env : Environment) : IO Unit := do
  -- splitItems: cut in order, at most `threshold` bytes each, an item
  -- larger than the threshold alone, zero never cutting.
  let item (n : Nat) : ScaffoldItem := { provides := #[s!"x{n}"], references := #[], text := String.ofList (List.replicate n 'a') }
  let sizes (parts : Array (Array ScaffoldItem)) := parts.map (·.map (·.text.length))
  require (sizes (splitItems 10 #[item 3, item 4, item 2, item 20, item 1]) == #[#[3, 4], #[2], #[20], #[1]])
    s!"splitItems: {sizes (splitItems 10 #[item 3, item 4, item 2, item 20, item 1])}"
  require (sizes (splitItems 0 #[item 3, item 40]) == #[#[3, 40]]) "zero split"
  -- A threshold that falls inside Base's mutual block of Tree and Forest.
  let roots := #[``Fixtures.Tree, ``Fixtures.Box, ``Fixtures.Envelope, ``Fixtures.token]
  let whole ← moduleOf (← treeOf env roots) base
  let some at_ := whole.items.findIdx? (·.text.startsWith "mutual") | throw (IO.userError "no mutual block")
  let before := (whole.items.extract 0 at_).foldl (fun n i => n + i.text.utf8ByteSize + 1) 0
  let threshold := before + whole.items[at_]!.text.utf8ByteSize / 2
  let t ← treeOf env roots (split := threshold)
  let header ← moduleOf t base
  let parts := t.modules.filter fun m => m.source == base && m.part.isSome
  require (parts.size ≥ 2 && header.items.isEmpty && header.refused == 0
    && header.reexports == parts.map (·.path)) s!"parts: {t.modules.map (·.name)}"
  require (parts.map (·.name) == (List.range parts.size).toArray.map
    (s!"U.TranslatorTests.Input.Base.~p{· + 1}")) s!"part names: {parts.map (·.name)}"
  -- The mutual block is whole, the first item of the part after the cut.
  let mutualIn := parts.filter fun p => p.items.any (·.text.startsWith "mutual")
  require (mutualIn.size == 1 && mutualIn[0]!.items[0]!.text == whole.items[at_]!.text)
    "the mutual block was cut or moved"
  -- Together the parts hold the module's items, in order.
  require ((parts.foldl (· ++ ·.items) #[]).map (·.text) == whole.items.map (·.text)) "the parts lose items"
  -- Each part opens only earlier parts it names and imports Init.Prelude.
  for p in parts do
    let some (k, _) := p.part | throw (IO.userError "not a part")
    require (p.opens.all fun o => match o.getLast? with
      | some last => last.startsWith "~p" && (last.drop 2).toNat! < k
      | none => false) s!"{p.name} opens {p.opens}"
    require (p.imports.all (· == ["U", "Init", "Prelude"])) s!"{p.name} imports {p.imports}"
  require (parts.any fun p => !p.opens.isEmpty) "no part opens an earlier one"
  let text := header.render "c"
  require (text.endsWith "module U.TranslatorTests.Input.Base where\nopen import U.TranslatorTests.Input.Base.~p1 public\nopen import U.TranslatorTests.Input.Base.~p2 public\n"
    || parts.size > 2) s!"the header: {text}"
  -- Another module still names the constants by the module's own path.
  let t' ← treeOf env #[``Fixtures.selected] (split := 600)
  let c ← moduleOf t' consumer
  require (c.imports.contains ["U", "TranslatorTests", "Input", "Base"]) "Consumer imports a part"

def run : IO Unit := do
  let env ← importEnvironment #[`Init, `TranslatorTests.Input.Consumer]
  checkOwnersAndImports env
  checkSplit env
  IO.println "module checks: owners, qualified references, imports, auxiliaries, library files, and the split passed"

end ModulesTests
