/-
File: translator/Lean2Agda/Core/Specialize.lean
-/
import Lean2Agda.Core.Closure
import Lean2Agda.Core.InductiveShape
import Lean2Agda.Core.Levels
import Lean2Agda.Core.Naming

/-!
# Prop-instantiation specialization

Lean's `Sort u` is `Prop` when `u` is zero, and `imax u v` is zero when
`v` is, so a universe-polymorphic constant is a different Agda
declaration at each pattern of zero and nonzero level parameters.  This
pass (issue M3-3) makes those declarations, the constant's **instances**,
in three steps:

+  the **split analysis** (`splitAnalysis`) finds, for each constant, the
   level parameters an instance must fix: those that a `Sort`'s level, an
   `imax`'s second argument, or a level passed to a split parameter of
   another constant depends on;
+  the **instance closure** (`instanceTable`) starts from every pattern of
   each root and follows the uses inside each instance, so that only the
   instances something uses are made;
+  `specializeClosure` writes each instance out as a declaration: the
   constant's own expressions with zero for each parameter fixed at zero
   and `u + 1` for each fixed as nonzero, every level in normal form
   (`Levels.lean`), so that none holds an `imax`.

An instance is not a constant of Lean's environment.  Its expressions
still name Lean's constants, with level arguments, and the kernel accepts
them as it accepts any instantiation; the printer names the instance a
reference selects from the levels it passes (`Splits.resolve`), and the
closure holds the instance under a key (`instanceKey`).
`docs/translator/levels.md` gives the rules and the counts.
-/

namespace Lean2Agda

open Lean

/-! ## The levels of a constant -/

/-- The expressions of a constant that hold levels: its type, its value,
and a recursor's rules. -/
def levelExprs (info : ConstantInfo) : Array Expr :=
  let own := match info.value? (allowOpaque := true) with
    | some v => #[info.type, v]
    | none => #[info.type]
  match info with
  | .recInfo r => own ++ r.rules.toArray.map (·.rhs)
  | _ => own

/-- Where a constant's expressions hold levels: the distinct levels of its
sorts, and the distinct constants with the level arguments they are
given, each in order of first occurrence.  A projection `Expr.proj S i t`
carries no levels, but it uses `S` at the levels of the type of `t`,
which `projectionTypes` reads; those uses are among `uses`, and
`projected` lists them again, since the printer writes a projection from
a type that is not an Agda record through the type's recursor.  The
kernel types no term of an `unsafe` declaration, which the scaffold
refuses anyway; the types such a declaration projects from are `unread`,
and its instances use every pattern of them. -/
structure LevelSites where
  sorts : Array Level := #[]
  uses : Array (Name × List Level) := #[]
  projected : Array (Name × List Level) := #[]
  unread : Array Name := #[]
  deriving Inhabited

/-- Whether a subterm holds a projection from a type with level
parameters, remembered per distinct subterm. -/
partial def holdsProjection (polymorphic : Name → Bool) (e : Expr) :
    StateM (Std.HashMap ExprStructEq Bool) Bool := do
  if let some known := (← get)[(e : ExprStructEq)]? then return known
  let found ← match e with
    | .proj s _ t => if polymorphic s then pure true else holdsProjection polymorphic t
    | .app f a => return (← holdsProjection polymorphic f) || (← holdsProjection polymorphic a)
    | .lam _ t b _ | .forallE _ t b _ =>
      return (← holdsProjection polymorphic t) || (← holdsProjection polymorphic b)
    | .letE _ t v b _ =>
      return (← holdsProjection polymorphic t) || (← holdsProjection polymorphic v) ||
        (← holdsProjection polymorphic b)
    | .mdata _ b => holdsProjection polymorphic b
    | _ => pure false
  modify (·.insert e found)
  return found

/-- The types projected from in an expression, each with the level
arguments of the type of the term projected from, as the kernel infers
it: `Expr.proj S i t` uses `S.{us}` when `t : S.{us} …`.  The walk enters
each binder with a free variable, as the printer does, and only the
subterms that hold a projection from a type with level parameters. -/
partial def projectionTypes (env : Environment) (polymorphic : Name → Bool) (root : Expr) :
    Except String (Array (Name × List Level)) := do
  let rec walk (lctx : LocalContext) (depth : Nat) (shape e : Expr)
      (state : Std.HashMap ExprStructEq Bool × Array (Name × List Level)) :
      Except String (Std.HashMap ExprStructEq Bool × Array (Name × List Level)) := do
    let (holds, marks) := (holdsProjection polymorphic shape).run state.1
    let mut state := (marks, state.2)
    unless holds do return state
    match shape, e with
    | .proj s _ st, .proj _ _ t =>
      if polymorphic s then
        let type ← match Kernel.check env lctx t with
          | .ok type => pure type
          | .error _ => throw s!"the kernel could not infer the type of a term projected from {s}"
        let type ← match Kernel.whnf env lctx type with
          | .ok type => pure type
          | .error _ => throw s!"the kernel could not reduce the type of a term projected from {s}"
        let .const head us := type.getAppFn | throw s!"a projection from {s} of a term of another type"
        unless head == s do throw s!"a projection from {s} of a term of type {head}"
        unless state.2.contains (s, us) do state := (state.1, state.2.push (s, us))
      walk lctx depth st t state
    | .app sf sa, .app f a => walk lctx depth sa a (← walk lctx depth sf f state)
    | .lam _ st sb _, .lam n t b bi | .forallE _ st sb _, .forallE n t b bi =>
      state ← walk lctx depth st t state
      let id : FVarId := ⟨.num `_lean2agda.sites depth⟩
      walk (lctx.mkLocalDecl id n t bi) (depth + 1) sb (b.instantiate1 (.fvar id)) state
    | .letE _ st sv sb _, .letE n t v b _ =>
      state ← walk lctx depth st t state
      state ← walk lctx depth sv v state
      let id : FVarId := ⟨.num `_lean2agda.sites depth⟩
      walk (lctx.mkLetDecl id n t v) (depth + 1) sb (b.instantiate1 (.fvar id)) state
    | .mdata _ sb, .mdata _ b => walk lctx depth sb b state
    | _, _ => return state
  return (← walk {} 0 root root ({}, #[])).2

/-- A constant's `LevelSites`: one pass over its expressions for the
sorts, the constants and the types projected from, then, when one of
those types has level parameters, the kernel's reading of the levels it
is projected from at. -/
def levelSites (env : Environment) (info : ConstantInfo) : Except String LevelSites := do
  let (sorts, uses, structures) := runST fun s => do
    let sorts : ST.Ref s (Array Level × Std.HashSet Level) ← ST.mkRef (#[], {})
    let uses : ST.Ref s (Array (Name × List Level) × Std.HashSet (Name × List Level)) ← ST.mkRef (#[], {})
    let structures : ST.Ref s (Array Name) ← ST.mkRef #[]
    for e in levelExprs info do
      e.forEach (ω := s) (m := ST s) fun sub => do
        match sub with
        | .sort l => sorts.modify fun (order, seen) =>
            if seen.contains l then (order, seen) else (order.push l, seen.insert l)
        | .const n us => uses.modify fun (order, seen) =>
            if seen.contains (n, us) then (order, seen) else (order.push (n, us), seen.insert (n, us))
        | .proj n _ _ => structures.modify fun order => if order.contains n then order else order.push n
        | _ => pure ()
    return ((← sorts.get).1, (← uses.get).1, ← structures.get)
  if structures.isEmpty then return { sorts, uses }
  let polymorphic (n : Name) : Bool := match env.find? n with
    | some c => !c.levelParams.isEmpty
    | none => false
  -- A type without level parameters is projected from at no levels, and
  -- needs no inference.
  let mut projected : Array (Name × List Level) :=
    (structures.filter (!polymorphic ·)).map fun n => (n, [])
  if info.isUnsafe then
    return { sorts, projected, unread := structures.filter polymorphic,
             uses := projected.foldl (fun acc x => if acc.contains x then acc else acc.push x) uses }
  if structures.any polymorphic then
    for e in levelExprs info do
      for site in ← projectionTypes env polymorphic e do
        unless projected.contains site do projected := projected.push site
  return { sorts, projected, uses := projected.foldl (fun acc x => if acc.contains x then acc else acc.push x) uses }

/-! ## Patterns -/

/-- Which rule decides the parameters to split.  Under `zeroness` a
parameter is split when whether a level is zero depends on it; under
`predecessor` also when it stands under no successor in a level that is
never zero, so that every sort of an instance is `Prop` or `Type ℓ` for a
level `ℓ` the instance can write, and every level it passes to a
parameter fixed as nonzero is some `ℓ + 1`. -/
inductive SplitRule where
  | zeroness
  | predecessor
  deriving BEq, Repr, Inhabited

def SplitRule.label : SplitRule → String
  | .zeroness => "zeroness"
  | .predecessor => "predecessor"

def SplitRule.other : SplitRule → SplitRule
  | .zeroness => .predecessor
  | .predecessor => .zeroness

/-- The rule the translator emits instances by. -/
def defaultSplitRule : SplitRule := .predecessor

/-- One entry per level parameter of a constant: whether it is split. -/
abbrev Mask := Array Bool

/-- The split parameters of each constant that has level parameters. -/
structure Splits where
  rule : SplitRule := .predecessor
  masks : Std.HashMap Name Mask := {}
  deriving Inhabited

def Splits.mask (s : Splits) (n : Name) : Mask := s.masks.getD n #[]

def Mask.splitCount (m : Mask) : Nat := m.foldl (fun n b => if b then n + 1 else n) 0

/-- Every array of `k` Booleans, the all-false one first. -/
def allPatterns : Nat → Array (Array Bool)
  | 0 => #[#[]]
  | k + 1 => (allPatterns k).foldl (fun acc p => acc.push (p.push false) |>.push (p.push true)) #[]

/-- A pattern's letters, one per split parameter in the constant's order:
`z` for zero and `n` for nonzero. -/
def patternLetters (zeros : Array Bool) : String :=
  String.ofList (zeros.toList.map fun z => if z then 'z' else 'n')

def lettersPattern (letters : String) : Array Bool := letters.toList.toArray.map (· == 'z')

/-- What each level parameter of a constant stands for in the instance
whose split parameters are zero as `zeros` says: zero, the successor of a
parameter of the same name, or, for a parameter that is not split,
itself. -/
def assignment (params : List Name) (mask : Mask) (zeros : Array Bool) : Name → NormalLevel :=
  let (table, _) := params.foldl (init := (({} : Std.HashMap Name NormalLevel), (0, 0))) fun (table, i, j) p =>
    if mask.getD i false then
      (table.insert p (if zeros.getD j false then .zero else (NormalLevel.param p).succ), i + 1, j + 1)
    else (table, i + 1, j)
  fun p => table.getD p (.param p)

/-- The parameters an instance keeps: all but those fixed at zero. -/
def keptParams (params : List Name) (mask : Mask) (zeros : Array Bool) : List Name :=
  (params.foldl (init := ((#[] : Array Name), (0, 0))) fun (kept, i, j) p =>
    if mask.getD i false then (if zeros.getD j false then kept else kept.push p, i + 1, j + 1)
    else (kept.push p, i + 1, j)).1.toList

/-! ## The split analysis -/

/-- The parameters a level asks to be split, under one assignment: those
of an `imax` it cannot yet decide; and, when `decide` (the level is a
sort's, or is passed to a split parameter), those that leave it neither
zero nor never zero, or under `predecessor` every bare one. -/
def blockers (rule : SplitRule) (assign : Name → NormalLevel) (l : Level) (decide : Bool) : Array Name :=
  match normalLevelWith assign l with
  | .error (.undecided ps) => ps
  | .error .metavariable => #[]
  | .ok n =>
    if !decide || n.isZero then #[]
    else match rule with
      | .zeroness => if n.neverZero then #[] else n.bare
      | .predecessor => n.bare

/-- The parameters of a constant to split beyond `mask`, given the masks
of the constants it uses: the blockers of its levels under every pattern
of `mask`. -/
def wantedSplits (rule : SplitRule) (maskOf : Name → Mask) (params : List Name) (mask : Mask)
    (sites : LevelSites) : Array Name := Id.run do
  let mut wanted : Array Name := #[]
  for zeros in allPatterns mask.splitCount do
    let assign := assignment params mask zeros
    for l in sites.sorts do
      for p in blockers rule assign l true do
        unless wanted.contains p do wanted := wanted.push p
    for (c, us) in sites.uses do
      let cm := maskOf c
      let mut i := 0
      for l in us do
        for p in blockers rule assign l (cm.getD i false) do
          unless wanted.contains p do wanted := wanted.push p
        i := i + 1
  return wanted

/-- The declarations of a closure that must share a mask with `d`: the
types and constructors of an inductive block, which one Agda declaration
holds, and the recursors of a block, which one `mutual` definition
holds. -/
def blockTag (byName : Std.HashMap Name Declaration) (d : Declaration) : Option (Bool × Name) :=
  match d.info with
  | .inductInfo v => v.all.head?.map (false, ·)
  | .ctorInfo c => match (byName[c.induct]?).map (·.info) with
    | some (ConstantInfo.inductInfo v) => v.all.head?.map (false, ·)
    | _ => some (false, c.induct)
  | .recInfo r => r.all.head?.map (true, ·)
  | _ => none

/-- The split parameters of every constant of a closure: the least masks
closed under `wantedSplits`, with one mask per block.  The closure orders
its groups with dependencies first, so each group is settled before the
groups that use it, and a group's own constants, which may use each
other, are revisited until nothing changes.  Every round that changes a
mask splits a parameter more, so a group of `n` parameters settles within
`n + 1` rounds; one that does not is an error of the analysis, not a
loop. -/
def splitAnalysis (rule : SplitRule) (closure : Closure) (sites : Std.HashMap Name LevelSites) :
    Except String Splits := do
  let byName : Std.HashMap Name Declaration := closure.declarations.foldl (fun m d => m.insert d.name d) {}
  let mut masks : Std.HashMap Name Mask := {}
  for group in closure.groups do
    for d in group do
      unless d.info.levelParams.isEmpty do
        masks := masks.insert d.name (.replicate d.info.levelParams.length false)
    let polymorphic := group.filter (!·.info.levelParams.isEmpty)
    let bound : Nat := polymorphic.foldl (fun n d => n + d.info.levelParams.length) 1
    let mut changed := !polymorphic.isEmpty
    let mut rounds : Nat := 0
    while changed do
      if rounds > bound then
        throw s!"the split analysis did not settle the group of {polymorphic.map (·.name)}"
      rounds := rounds + 1
      changed := false
      for d in polymorphic do
        let params := d.info.levelParams
        let mask := masks.getD d.name #[]
        let wanted := wantedSplits rule (masks.getD · #[]) params mask (sites.getD d.name {})
        let grown := (params.toArray.zip mask).map fun (p, b) => b || wanted.contains p
        if grown != mask then
          masks := masks.insert d.name grown
          changed := true
      -- One mask per block: the union of its members'.
      for d in polymorphic do
        if let some tag := blockTag byName d then
          let members := polymorphic.filter fun m => blockTag byName m == some tag
          let union := members.foldl (init := masks.getD d.name #[]) fun acc m =>
            let other := masks.getD m.name #[]
            if other.size == acc.size then (acc.zip other).map fun (a, b) => a || b else acc
          for m in members do
            if (masks.getD m.name #[]).size == union.size && masks.getD m.name #[] != union then
              masks := masks.insert m.name union
              changed := true
  return { rule, masks }

/-! ## Instances -/


/-- The letters of the instance of a constant with mask `mask` that the
level arguments `us` select under `assign`: `z` where a split parameter's
argument is zero and `n` where it is never zero.  The analysis leaves no
other case, so one is an error. -/
def useLetters (assign : Name → NormalLevel) (c : Name) (mask : Mask) (us : List Level) : Except String String := do
  let mut letters := ""
  let mut i := 0
  for l in us do
    if mask.getD i false then
      match normalLevelWith assign l with
      | .ok n =>
        if n.isZero then letters := letters.push 'z'
        else if n.neverZero then letters := letters.push 'n'
        else throw s!"the level {l} passed to {c} is zero for some of its parameters only"
      | .error _ => throw s!"the level {l} passed to {c} has an imax that its parameters do not decide"
    i := i + 1
  return letters

/-- The key of the instance that a reference `c.{us}` selects, for the
printer; a constant without split parameters, and a name the analysis
never saw (an auxiliary definition of the sharing pass), is its own. -/
def Splits.resolve (s : Splits) (c : Name) (us : List Level) : Except String Name := do
  let mask := s.mask c
  if mask.splitCount == 0 then return c
  return instanceKey c (← useLetters .param c mask us)

/-- One instance: the constant, its pattern, its key, and the keys of the
instances it uses. -/
structure InstanceRecord where
  name : Name
  zeros : Array Bool
  key : Name
  uses : Array Name
  deriving Inhabited

/-- The instances a given one uses, as constants with letters:

+  each constant its expressions name, and each type they project from,
   at the pattern its level arguments select;
+  for a projection from a type that is not an Agda record, that type's
   recursor, through which the printer writes the projection, at the same
   pattern and both patterns of its motive's level, which is the level of
   the field's type and is not read here; and for an `unsafe`
   declaration, every pattern of the types it projects from;
+  the companions its declaration is printed with, at its own pattern: an
   inductive type's block and constructors (a constructor names its type,
   and a recursor its types and their constructors, in its own type);
   `Quot.mk` for `Quot.lift`, whose computation rule names it; and for
   `Quot.ind` the instance of `Eq` at zero, the relation of its rule;
+  `Nat` and `String`, for a literal. -/
def instanceUses (env : Environment) (splits : Splits) (sites : LevelSites) (d : Declaration)
    (zeros : Array Bool) : Except String (Array (Name × String)) := do
  let params := d.info.levelParams
  let assign := assignment params (splits.mask d.name) zeros
  let mut out : Array (Name × String) := #[]
  let add (out : Array (Name × String)) (x : Name × String) := if out.contains x then out else out.push x
  for (c, us) in sites.uses do
    out := add out (c, ← useLetters assign c (splits.mask c) us)
  for (s, us) in sites.projected do
    if !isAgdaRecordName env s then
      if let some (.recInfo r) := env.find? (mkRecName s) then
        let motives := if r.levelParams.length == us.length + 1 then [[Level.zero], [Level.succ .zero]] else [[]]
        for motive in motives do
          out := add out (r.name, ← useLetters assign r.name (splits.mask r.name) (motive ++ us))
  -- An `unsafe` declaration's projections, whose levels were not read.
  for s in sites.unread do
    for c in if isAgdaRecordName env s || !env.contains (mkRecName s) then [s] else [s, mkRecName s] do
      for p in allPatterns (splits.mask c).splitCount do out := add out (c, patternLetters p)
  -- A companion takes the parameters of this constant that have its
  -- parameters' names.
  let companion (out : Array (Name × String)) (c : Name) : Except String (Array (Name × String)) := do
    let some info := env.find? c | throw s!"missing companion {c} of {d.name}"
    return add out (c, ← useLetters assign c (splits.mask c) (info.levelParams.map Level.param))
  match d.info with
  | .inductInfo v =>
    for t in v.all do
      out ← companion out t
      if let some (.inductInfo tv) := env.find? t then
        for c in tv.ctors do out ← companion out c
  | .quotInfo q =>
    if q.name == ``Quot.lift then out ← companion out ``Quot.mk
    if q.name == ``Quot.ind then out := add out (``Eq, ← useLetters assign ``Eq (splits.mask ``Eq) [.zero])
  | _ => pure ()
  for literal in [``Nat, ``String] do
    if d.dependencies.contains literal then out := add out (literal, "")
  return out

/-- The instances of a closure: every pattern of each root, and the
instances those use, each made once, in the order they are reached. -/
def instanceTable (env : Environment) (splits : Splits) (sites : Std.HashMap Name LevelSites)
    (closure : Closure) : Except String (Array InstanceRecord) := do
  let byName : Std.HashMap Name Declaration := closure.declarations.foldl (fun m d => m.insert d.name d) {}
  let mut queue : Array (Name × Array Bool) := #[]
  let mut seen : Std.HashSet Name := {}
  for r in closure.roots do
    for p in allPatterns (splits.mask r).splitCount do
      let key := instanceKey r (patternLetters p)
      unless seen.contains key do
        seen := seen.insert key
        queue := queue.push (r, p)
  let mut records : Array InstanceRecord := #[]
  let mut next := 0
  while h : next < queue.size do
    let (name, zeros) := queue[next]
    next := next + 1
    let some d := byName[name]? | throw s!"an instance of {name}, which the closure does not hold"
    let uses ← instanceUses env splits (sites.getD name {}) d zeros
    let mut keys := #[]
    for (c, letters) in uses do
      let key := instanceKey c letters
      keys := keys.push key
      unless seen.contains key do
        seen := seen.insert key
        queue := queue.push (c, lettersPattern letters)
    records := records.push { name, zeros, key := instanceKey name (patternLetters zeros), uses := keys }
  return records

/-! ## Instances as declarations -/

/-- A constant's information with other level parameters and every
expression mapped. -/
def mapConstantInfo (info : ConstantInfo) (levelParams : List Name) (f : Expr → Expr) : ConstantInfo :=
  match info with
  | .axiomInfo v => .axiomInfo { v with levelParams, type := f v.type }
  | .defnInfo v => .defnInfo { v with levelParams, type := f v.type, value := f v.value }
  | .thmInfo v => .thmInfo { v with levelParams, type := f v.type, value := f v.value }
  | .opaqueInfo v => .opaqueInfo { v with levelParams, type := f v.type, value := f v.value }
  | .quotInfo v => .quotInfo { v with levelParams, type := f v.type }
  | .inductInfo v => .inductInfo { v with levelParams, type := f v.type }
  | .ctorInfo v => .ctorInfo { v with levelParams, type := f v.type }
  | .recInfo v =>
    let rules := v.rules.map fun r => { r with rhs := f r.rhs }
    .recInfo { v with levelParams, type := f v.type, rules }

/-- An expression with every level in the normal form it has under
`assign`; a level without one is left as it is, for `instanceInfo` to
refuse. -/
def normalizeLevels (assign : Name → NormalLevel) (e : Expr) : Expr :=
  let normal (l : Level) : Level := match normalLevelWith assign l with
    | .ok n => n.toLevel
    | .error _ => l
  e.replace fun sub => match sub with
    | .sort l => some (.sort (normal l))
    | .const n us => some (.const n (us.map normal))
    | _ => none

def exprHasIMax (e : Expr) : Bool :=
  (e.find? fun sub => match sub with
    | .sort l => hasIMax l
    | .const _ us => us.any hasIMax
    | _ => false).isSome

/-- The declaration of one instance: the constant's information at the
instance's levels, with the parameters it keeps, and every level in
normal form, also in a constant without split parameters, whose one
instance is the constant itself.  The names inside stay Lean's.  An
instance in which an `imax` survives is an error of the analysis. -/
def instanceInfo (info : ConstantInfo) (mask : Mask) (zeros : Array Bool) : Except String ConstantInfo := do
  let params := info.levelParams
  let made := mapConstantInfo info (keptParams params mask zeros) (normalizeLevels (assignment params mask zeros))
  if (levelExprs made).any exprHasIMax then
    throw s!"the instance {instanceKey info.name (patternLetters zeros)} holds an imax that its pattern does not decide"
  return made

/-- What the specialization counted, for `--stats`: the closure's
constants, those with level parameters and their parameters, the
parameters split and the constants with one, the instances made, and the
instances there could be, counted three ways: one per pattern of each
constant's split parameters; one per pattern of all its parameters; and
that last sum as rocq-lean-import takes it, over entries, where an
inductive type with its constructors and recursors is one entry and the
quotient's four constants are one entry of two instances. -/
structure SpecializationStats where
  rule : SplitRule := .predecessor
  constants : Nat := 0
  polymorphic : Nat := 0
  parameters : Nat := 0
  split : Nat := 0
  splitConstants : Nat := 0
  instances : Nat := 0
  possibleBySplit : Nat := 0
  possibleByParameters : Nat := 0
  entries : Nat := 0
  possibleByEntries : Nat := 0
  deriving BEq, Repr, Inhabited

def specializationStats (splits : Splits) (closure : Closure) (instances : Nat) : SpecializationStats :=
  let s := closure.declarations.foldl (init := { rule := splits.rule, instances }) fun s d =>
    let n := d.info.levelParams.length
    let k := (splits.mask d.name).splitCount
    let entry := match d.info with
      | .ctorInfo _ | .recInfo _ | .quotInfo _ => false
      | _ => true
    { s with constants := s.constants + 1, polymorphic := s.polymorphic + (if n > 0 then 1 else 0),
             parameters := s.parameters + n, split := s.split + k,
             splitConstants := s.splitConstants + (if k > 0 then 1 else 0),
             possibleBySplit := s.possibleBySplit + 2 ^ k,
             possibleByParameters := s.possibleByParameters + 2 ^ n,
             entries := s.entries + (if entry then 1 else 0),
             possibleByEntries := s.possibleByEntries + (if entry then 2 ^ n else 0) }
  if closure.declarations.any (·.info matches .quotInfo _) then
    { s with entries := s.entries + 1, possibleByEntries := s.possibleByEntries + 2 }
  else s

def SpecializationStats.render (s : SpecializationStats) : String :=
  s!"# specialization, rule {s.rule.label}\n" ++ "\n".intercalate [
    s!"constants\t{s.constants}", s!"with level parameters\t{s.polymorphic}",
    s!"level parameters\t{s.parameters}", s!"split parameters\t{s.split}",
    s!"constants with a split parameter\t{s.splitConstants}",
    s!"instances\t{s.instances}", s!"possible instances, split parameters\t{s.possibleBySplit}",
    s!"possible instances, all parameters\t{s.possibleByParameters}",
    s!"entries\t{s.entries}", s!"possible instances, entries\t{s.possibleByEntries}"] ++ "\n"

/-- The sites of every constant of a closure. -/
def closureSites (env : Environment) (closure : Closure) : Except String (Std.HashMap Name LevelSites) :=
  closure.declarations.foldlM (init := {}) fun m d => do
    match levelSites env d.info with
    | .ok sites => return m.insert d.name sites
    | .error e => throw s!"{d.name}: {e}"

/-- A closure's split parameters, its instances, and the counts, without
the instances' expressions, from the closure's sites (`closureSites`,
which two rules can share): what `--stats` needs.  A closure holding a
Lean constant whose name has a pattern's component is refused, so that an
instance's key is never a constant's name. -/
def specializationWith (env : Environment) (rule : SplitRule) (closure : Closure)
    (sites : Std.HashMap Name LevelSites) : Except String (Splits × Array InstanceRecord × SpecializationStats) := do
  for d in closure.declarations do
    if hasPatternComponent d.name then
      throw s!"{d.name} has a component an instance's key is made with"
  let splits ← splitAnalysis rule closure sites
  let instances ← instanceTable env splits sites closure
  return (splits, instances, specializationStats splits closure instances.size)

def specializationOf (env : Environment) (rule : SplitRule) (closure : Closure) :
    Except String (Splits × Array InstanceRecord × SpecializationStats) := do
  specializationWith env rule closure (← closureSites env closure)

/-- The closure of instances: one declaration per instance, under its
key, depending on the instances it uses, ordered again by strongly
connected groups; its roots are every pattern of the closure's roots. -/
def specializeClosure (env : Environment) (rule : SplitRule) (closure : Closure) :
    Except String (Closure × Splits × SpecializationStats) := do
  let (splits, instances, stats) ← specializationOf env rule closure
  let byName : Std.HashMap Name Declaration := closure.declarations.foldl (fun m d => m.insert d.name d) {}
  let mut made : Std.HashMap Name Declaration := {}
  for r in instances do
    let d := byName[r.name]!
    let info ← instanceInfo d.info (splits.mask r.name) r.zeros
    made := made.insert r.key { name := r.key, info, sourceModule := d.sourceModule,
                                dependencies := uniqueNames r.uses, pattern := patternLetters r.zeros }
  let names := sortNames (instances.map (·.key))
  let groups := SCC.scc names.toList fun n => (made[n]!.dependencies.filter made.contains).toList
  let roots := closure.roots.foldl (init := #[]) fun acc r =>
    (allPatterns (splits.mask r).splitCount).foldl (fun acc p => acc.push (instanceKey r (patternLetters p))) acc
  return ({ roots := sortNames roots, groups := groups.toArray.map fun group =>
    (sortNames group.toArray).map (made[·]!) }, splits, stats)

end Lean2Agda
