/-
File: translator/Lean2Agda/Core/Recursor.lean
-/
import Lean2Agda.Core.Inductive

/-!
# Recursors by pattern matching

Lean's kernel gives each inductive type a recursor and one computation
rule per constructor; Agda has no recursors, so each one becomes a
function defined by pattern matching whose clauses are the kernel's
rules.  A rule's right-hand side is a lambda over the recursor's
parameters, motives and minor premises and the constructor's fields, and
its clause is as follows:

+  the parameters, motives and minor premises are variable patterns, with
   the visibilities of the recursor's Lean type, which every printed
   application of the recursor passes;
+  each index is `_`, which Agda's unifier fills in from the constructor's
   target;
+  the major premise is the constructor applied to `_` for each parameter
   that Lean promoted from an index and Agda keeps as one (`Eq.refl`'s
   `a`, bound by the recursor's own pattern for that parameter), then to
   one variable per field, with the field's Lean visibility;
+  the right-hand side is the rule's, applied to those variables and
   printed in their scope, so that a recursive field comes out as a call
   of the recursor on that field, which Agda's termination checker sees
   as structural.

A type without constructors gets one clause with the absurd pattern.  The
recursors of one block (the types of a mutual declaration, and a nested
type's `rec_N` on the kernel's auxiliary types) are one `mutual`
definition, since their rules call each other.  `docs/translator/inductives.md`
gives the rules and the probes behind them.
-/

namespace Lean2Agda

open Lean

/-- The recursor's binders after its parameters, motives and minor
premises, `indices → (t : I …) → motive …`, instantiated at the given
indices and major premise. -/
def instantiateRecursorTail (s : Scope) (tail : Expr) (args : Array Expr) : PrintM Expr :=
  args.foldlM (init := tail) fun t a => do
    let some (.forallE _ _ b _) ← asPi s t | throw "a recursor with fewer binders than its rule"
    return b.instantiate1 a

/-- Enter a recursor's indices, whose patterns are `_`, so that the major
premise's type can be read: the scope after them, the patterns, and the
major premise's binder. -/
def enterIndices (r : RecursorVal) (s : Scope) (tail : Expr) :
    PrintM (Scope × Array (Visibility × Pattern) × Expr × BinderInfo) := do
  let mut scope := s
  let mut rest := tail
  let mut patterns : Array (Visibility × Pattern) := #[]
  for _ in [:r.numIndices] do
    let some (.forallE n t b bi) ← asPi scope rest | throw s!"{r.name} has too few indices"
    let (scope', _, fv) := scope.enter n t bi
    patterns := patterns.push (Visibility.ofBinderInfo bi, .wild)
    scope := scope'
    rest := b.instantiate1 fv
  let some (.forallE _ majorType _ majorInfo) ← asPi scope rest | throw s!"{r.name} has no major premise"
  return (scope, patterns, majorType, majorInfo)

/-- The variable patterns of a recursor's parameters, motives and minor
premises. -/
def variablePatterns (binders : Array (Visibility × String × AgdaTerm)) : Array (Visibility × Pattern) :=
  binders.map fun (v, x, _) => (v, .var x)

/-- The clause of one rule of a recursor whose first binders, its
parameters, motives and minor premises, were entered as `binders` in the
scope `s`, with `tail` the rest of its type in that scope. -/
def recursorClause (r : RecursorVal) (binders : Array (Visibility × String × AgdaTerm)) (s : Scope)
    (tail : Expr) (rule : RecursorRule) : PrintM PatternClause := do
  let env := (← read).env
  let (scope, indexPatterns, majorType, majorInfo) ← enterIndices r s tail
  let mut scope := scope
  let majorType ← if majorType.consumeMData.getAppFn.isConst then pure majorType.consumeMData
    else kernelWhnf scope majorType
  let .const induct us := majorType.getAppFn | throw s!"the major premise of {r.name} is not inductive"
  let some (.inductInfo ind) := env.find? induct | throw s!"no inductive type {induct}"
  let some (.ctorInfo c) := env.find? rule.ctor | throw s!"no constructor {rule.ctor}"
  let ctorParams := majorType.getAppArgs.extract 0 ind.numParams
  -- The constructor's fields, in the scope after the indices.
  let mut ctorType ← instantiateParams scope ((ConstantInfo.ctorInfo c).instantiateTypeLevelParams us) ctorParams
  let mut fieldPatterns : Array (Visibility × Pattern) := #[]
  let mut fields : Array Expr := #[]
  for _ in [:rule.nfields] do
    let some (.forallE n t b bi) ← asPi scope ctorType | throw s!"{rule.ctor} has too few fields"
    let (scope', x, fv) := scope.enter n t bi
    fieldPatterns := fieldPatterns.push (Visibility.ofBinderInfo bi, .var x)
    fields := fields.push fv
    scope := scope'
    ctorType := b.instantiate1 fv
  let target ← if ctorType.consumeMData.getAppFn.isConst then pure ctorType.consumeMData
    else kernelWhnf scope ctorType
  let indices := target.getAppArgs.extract ind.numParams (ind.numParams + ind.numIndices)
  -- Lean's parameters that Agda keeps as indices, which the constructor
  -- binds with its own visibilities.
  let promoted := (leadingBinderInfos c.type ind.numParams).drop (agdaParamCount env ind)
  let ctorPattern := Pattern.ctor ((← read).naming.constant rule.ctor)
    (promoted.toArray.map (fun bi => (Visibility.ofBinderInfo bi, Pattern.wild)) ++ fieldPatterns)
  let major := mkAppN (.const rule.ctor us) (ctorParams ++ fields)
  let expected ← instantiateRecursorTail scope tail (indices.push major)
  let leading := r.numParams + r.numMotives + r.numMinors
  unless rule.rhs.getNumHeadLambdas ≥ leading + rule.nfields do
    throw s!"the rule of {r.name} for {rule.ctor} has too few lambdas"
  let body := rule.rhs.beta (parameterVariables leading ++ fields)
  let patterns := (variablePatterns binders ++ indexPatterns).push (Visibility.ofBinderInfo majorInfo, ctorPattern)
  return { patterns, body := some (← printAgainst scope body expected false) }

/-- The absurd clause of a recursor of a type without constructors. -/
def absurdClause (r : RecursorVal) (binders : Array (Visibility × String × AgdaTerm)) (s : Scope)
    (tail : Expr) : PrintM PatternClause := do
  let (_, indexPatterns, _, majorInfo) ← enterIndices r s tail
  return { patterns := (variablePatterns binders ++ indexPatterns).push (Visibility.ofBinderInfo majorInfo, .absurd),
           body := none }

/-- A recursor's printed type and clauses, one per rule. -/
def recursorClauses (r : RecursorVal) : PrintM (AgdaTerm × Array PatternClause) := do
  let type ← printExpr {} r.type
  let leading := r.numParams + r.numMotives + r.numMinors
  let (binders, scope, tail) ← enterTelescope {} r.type leading
  let clauses ← if r.rules.isEmpty then pure #[← absurdClause r binders scope tail]
    else r.rules.toArray.mapM (recursorClause r binders scope tail)
  return (type, clauses)

/-- The order of a block's recursors: each type's `rec` in the order of
`all`, then the nested types' `rec_N` by `N`. -/
def recursorRank (all : List Name) (n : Name) : Nat :=
  match all.idxOf? (n.getPrefix) with
  | some i => if n == mkRecName (all[i]!) then i else all.length + suffix
  | none => all.length + suffix
where
  suffix : Nat := match n with
    | .str _ s => ((s.drop 4).toString.toNat?).getD 0
    | _ => 0

/-- A recursor block's declaration: its lines, the identifiers it
declares, those its text refers to (the constructors it matches among
them), and the postulates of its members' types, which stand for it when
Agda refuses it.  A lone recursor is its signature and clauses; several
are one `mutual` block, the signatures first. -/
structure RecursorDecl where
  lines : Array String
  provides : Array String
  references : Array String
  postulates : Array String
  typeReferences : Array String
  counts : PrintCounts
  deriving Inhabited

def recursorDecl (p : Printer) (members : Array RecursorVal) : Except String RecursorDecl := do
  let (printed, counts) ← runPrint p (members.mapM recursorClauses)
  let names := members.map (agdaIdent ·.name)
  let signatures := (names.zip printed).map fun (n, (t, _)) => s!"{n} : {t.render}"
  let clauses := (names.zip printed).foldl (fun acc (n, (_, cs)) => acc ++ cs.map (·.render n)) #[]
  let lines := if members.size == 1 then signatures ++ clauses
    else #["mutual"] ++ (signatures ++ clauses).map ("  " ++ ·)
  let ctors := members.foldl (fun acc r => acc ++ r.rules.toArray.map (agdaIdent ·.ctor)) #[]
  let terms := printed.foldl (fun acc (t, cs) => (acc.push t) ++ cs.filterMap (·.body)) #[]
  let distinct (ns : Array String) : Array String := ns.foldl (fun acc n =>
    if acc.contains n || names.contains n then acc else acc.push n) #[]
  return { lines, provides := names, counts,
           references := distinct (terms.foldl (fun acc t => acc ++ t.constants) ctors),
           postulates := signatures.map ("postulate " ++ ·),
           typeReferences := distinct (printed.foldl (fun acc (t, _) => acc ++ t.constants) #[]) }

end Lean2Agda
