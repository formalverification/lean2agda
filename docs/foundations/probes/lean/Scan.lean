-- File: docs/foundations/probes/lean/Scan.lean
-- Scan of every constant in the environment of import Mathlib: axioms, hatches, K recursors, large elimination, nested and mutual inductives.  Needs Mathlib's cache; about 7 GB and 2.5 minutes.
-- Run from translator/ as: lake env lean ../docs/foundations/probes/lean/Scan.lean
import Mathlib
open Lean

def modNameOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => Name.anonymous

def isStdAxiom (a : Name) : Bool := a == ``propext || a == ``Quot.sound || a == ``Classical.choice

partial def resultSortIsProp (e : Expr) : Bool :=
  match e with
  | .forallE _ _ b _ => resultSortIsProp b
  | .sort u => u.isZero
  | _ => false

#eval show CoreM Unit from do
  let env ← getEnv
  let t0 ← IO.monoMsNow
  let mut total : Nat := 0
  let mut axioms : Array String := #[]
  let mut nUnsafe : Nat := 0
  let mut nOpaque : Nat := 0
  let mut nPartial : Nat := 0
  let mut nImpl : Nat := 0
  let mut nNoncomp : Nat := 0
  let mut nRec : Nat := 0
  let mut kRecs : Array String := #[]
  let mut nInd : Nat := 0
  let mut nPropInd : Nat := 0
  let mut nLargeProp : Nat := 0
  let mut largePropInit : Array String := #[]
  let mut largePropMathlib : Array String := #[]
  let mut nestedMutual : Array String := #[]
  let mut nonStd : Std.HashMap Name (Nat × Array Name) := {}
  let mut nT3 : Nat := 0
  let mut nSorry : Nat := 0
  for (n, ci) in env.constants.toList do
    total := total + 1
    let m := modNameOf env n
    if ci.isUnsafe then nUnsafe := nUnsafe + 1
    if isNoncomputable env n then nNoncomp := nNoncomp + 1
    if (Compiler.getImplementedBy? env n).isSome then nImpl := nImpl + 1
    match ci with
    | .axiomInfo v => axioms := axioms.push s!"{n} unsafe={v.isUnsafe} module={m}"
    | .opaqueInfo _ =>
      nOpaque := nOpaque + 1
      if env.contains (n ++ `_unsafe_rec) then nPartial := nPartial + 1
    | .recInfo v =>
      nRec := nRec + 1
      if v.k then kRecs := kRecs.push s!"{n} module={m}"
    | .inductInfo v =>
      nInd := nInd + 1
      if v.numNested > 0 || v.all.length > 1 then
        nestedMutual := nestedMutual.push s!"{m} {n} nested={v.numNested} mutual={v.all.length}"
      if resultSortIsProp v.type then
        nPropInd := nPropInd + 1
        if let some (.recInfo r) := env.find? (n ++ `rec) then
          if r.levelParams.length > v.levelParams.length then
            nLargeProp := nLargeProp + 1
            if (`Init).isPrefixOf m then largePropInit := largePropInit.push s!"{n} ({m})"
            else if (`Mathlib).isPrefixOf m then largePropMathlib := largePropMathlib.push s!"{n} ({m})"
    | _ => pure ()
    let axs ← collectAxioms n
    let mut t3 := false
    for a in axs do
      if a == ``sorryAx then nSorry := nSorry + 1
      unless isStdAxiom a do
        t3 := true
        let (c, ex) := nonStd.getD a (0, #[])
        nonStd := nonStd.insert a (c + 1, if ex.size < 8 then ex.push n else ex)
    if t3 then nT3 := nT3 + 1
  let t1 ← IO.monoMsNow
  IO.println s!"constants: {total}; inductives: {nInd}; recursors: {nRec}; opaque: {nOpaque}"
  IO.println s!"unsafe: {nUnsafe}; partial (opaque with _unsafe_rec): {nPartial}; implemented_by: {nImpl}; noncomputable: {nNoncomp}"
  IO.println s!"constants depending on an axiom outside propext/Quot.sound/Classical.choice: {nT3}; on sorryAx: {nSorry}"
  IO.println s!"Prop inductives: {nPropInd}; with large elimination: {nLargeProp}"
  IO.println "--- axioms in the environment ---"
  for s in axioms.qsort (· < ·) do IO.println s
  IO.println "--- dependents per non-standard axiom (count, up to 8 examples) ---"
  for (a, (c, ex)) in nonStd.toList do IO.println s!"{a}: {c} {ex}"
  IO.println "--- recursors with k = true ---"
  for s in kRecs.qsort (· < ·) do IO.println s
  IO.println "--- Prop inductives with large elimination, Init ---"
  for s in largePropInit.qsort (· < ·) do IO.println s
  IO.println s!"--- Prop inductives with large elimination, Mathlib ({largePropMathlib.size}) ---"
  for s in largePropMathlib.qsort (· < ·) do IO.println s
  IO.println "--- nested or mutual inductives ---"
  for s in nestedMutual.qsort (· < ·) do IO.println s
  IO.println s!"elapsed ms: {t1 - t0}"

/- Output on 2026-10-07 (Lean v4.33.1, Mathlib v4.33.1):
constants: 771136; inductives: 6790; recursors: 6913; opaque: 3062
unsafe: 714; partial (opaque with _unsafe_rec): 1509; implemented_by: 341; noncomputable: 16021
constants depending on an axiom outside propext/Quot.sound/Classical.choice: 255; on sorryAx: 1
Prop inductives: 2253; with large elimination: 1980
--- axioms in the environment ---
Classical.choice unsafe=false module=Init.Prelude
Lean.ofReduceBool unsafe=false module=Init.Core
Lean.ofReduceNat unsafe=false module=Init.Core
Lean.trustCompiler unsafe=false module=Init.Core
Quot.lcInv unsafe=true module=Init.Prelude
Quot.sound unsafe=false module=Init.Core
isScalarObj unsafe=true module=Init.Prelude
lcAny unsafe=true module=Init.Prelude
lcCast unsafe=true module=Init.Prelude
lcErased unsafe=true module=Init.Prelude
lcProof unsafe=true module=Init.Prelude
lcUnreachable unsafe=true module=Init.Prelude
lcVoid unsafe=true module=Init.Prelude
propext unsafe=false module=Init.Core
sorryAx unsafe=false module=Init.Prelude
--- dependents per non-standard axiom (count, up to 8 examples) ---
sorryAx: 1 #[sorryAx]
lcProof: 242 #[Lean.Elab.Term.FixedTermElab.toFixedTermElabRefImpl, FP.Float.instSub, _private.Lean.LibrarySuggestions.SymbolFrequency.0.Lean.Environment.unsafeRunMetaM, Lean.Elab.Do.DoOpsRef.toDoOpsImpl, Lean.Language.instImpl._@.Lean.Language.Basic.3470488393._hygCtx._hyg.29, Lean.Level.param._override, Std.Tactic.BVDecide.BVExpr.casesOn._override, instReprNNReal]
Quot.lcInv: 1 #[Quot.lcInv]
lcVoid: 1 #[lcVoid]
isScalarObj: 1 #[isScalarObj]
Lean.ofReduceBool: 1 #[Lean.ofReduceBool]
lcErased: 1 #[lcErased]
Lean.ofReduceNat: 1 #[Lean.ofReduceNat]
lcAny: 1 #[lcAny]
lcUnreachable: 1 #[lcUnreachable]
Lean.trustCompiler: 5 #[Lean.ofReduceNat, Lean.reduceNat, Lean.ofReduceBool, Lean.reduceBool, Lean.trustCompiler]
lcCast: 1 #[lcCast]
--- recursors with k = true ---
AddCircle.EndpointIdent.rec module=Mathlib.Topology.Instances.AddCircle.Defs
CategoryTheory.Cat.FreeReflRel.rec module=Mathlib.CategoryTheory.Category.ReflQuiv
CategoryTheory.Presieve.singleton.rec module=Mathlib.CategoryTheory.Sites.Sieves
CategoryTheory.Subgroupoid.Discrete.Arrows.rec module=Mathlib.CategoryTheory.Groupoid.Subgroupoid
Eq.rec module=Init.Prelude
HEq.rec module=Init.Prelude
Lean.Meta.CheckTactic.CheckGoalType.rec module=Init.Meta.Defs
Qq.QuotedDefEq.rec module=Qq.Typ
Qq.QuotedLevelDefEq.rec module=Qq.Typ
SimpleGraph.Walk.Nil.rec module=Mathlib.Combinatorics.SimpleGraph.Walk.Basic
Std.LeftIdentity.rec module=Init.Core
Std.RightIdentity.rec module=Init.Core
String.Legacy.Iterator.ValidFor.rec module=Batteries.Data.String.Lemmas
Substring.Raw.ValidFor.rec module=Batteries.Data.String.Lemmas
True.rec module=Init.Prelude
--- Prop inductives with large elimination, Init ---
Acc (Init.WF)
Acc.below (Init.WF)
And (Init.Prelude)
Array.Mem (Init.Data.Array.Basic)
Array.Perm (Init.Data.Array.Perm)
BitVec.DivModState.Lawful (Init.Data.BitVec.Bitblast)
BitVec.DivModState.Poised (Init.Data.BitVec.Bitblast)
Eq (Init.Prelude)
EquivBEq (Init.Data.BEq)
Equivalence (Init.Core)
False (Init.Prelude)
Float.Model.Format.Valid (Init.Data.Float.Model.Format.Valid)
HEq (Init.Prelude)
Iff (Init.Core)
LawfulApplicative (Init.Control.Lawful.Basic)
LawfulBEq (Init.Core)
LawfulFunctor (Init.Control.Lawful.Basic)
LawfulGetElem (Init.GetElem)
LawfulHashable (Init.Data.LawfulHashable)
LawfulMonad (Init.Control.Lawful.Basic)
LawfulMonadAttach (Init.Control.MonadAttach)
LawfulMonadLift (Init.Control.Lawful.MonadLift.Basic)
LawfulMonadLiftT (Init.Control.Lawful.MonadLift.Basic)
LawfulSingleton (Init.Core)
Lean.Grind.AddRightCancel (Init.Grind.Module.Basic)
Lean.Grind.ExistsAddOfLT (Init.Grind.Ordered.Module)
Lean.Grind.IsCharP (Init.Grind.Ring.Basic)
Lean.Grind.LawfulOfScientific (Init.Grind.Ring.OfScientific)
Lean.Grind.NoNatZeroDivisors (Init.Grind.Module.Basic)
Lean.Grind.OrderedAdd (Init.Grind.Ordered.Module)
Lean.Grind.OrderedRing (Init.Grind.Ordered.Ring)
Lean.Grind.PowIdentity (Init.Grind.Ring.Basic)
Lean.Grind.ToInt.Add (Init.Grind.ToInt)
Lean.Grind.ToInt.Div (Init.Grind.ToInt)
Lean.Grind.ToInt.LE (Init.Grind.ToInt)
Lean.Grind.ToInt.LT (Init.Grind.ToInt)
Lean.Grind.ToInt.Mod (Init.Grind.ToInt)
Lean.Grind.ToInt.Mul (Init.Grind.ToInt)
Lean.Grind.ToInt.Neg (Init.Grind.ToInt)
Lean.Grind.ToInt.OfNat (Init.Grind.ToInt)
Lean.Grind.ToInt.Pow (Init.Grind.ToInt)
Lean.Grind.ToInt.Sub (Init.Grind.ToInt)
Lean.Grind.ToInt.Zero (Init.Grind.ToInt)
Lean.Meta.CheckTactic.CheckGoalType (Init.Meta.Defs)
Lean.Order.MonoBind (Init.Internal.Order.Basic)
NeZero (Init.Data.NeZero)
PartialEquivBEq (Init.Data.BEq)
ReflBEq (Init.Core)
Std.Antisymm (Init.Core)
Std.Associative (Init.Core)
Std.Asymm (Init.Core)
Std.Commutative (Init.Core)
Std.IdempotentOp (Init.Core)
Std.Identity (Init.Core)
Std.Internal.LawfulMonadLiftBindFunction (Init.Data.Iterators.Internal.LawfulMonadLiftFunction)
Std.Internal.LawfulMonadLiftFunction (Init.Data.Iterators.Internal.LawfulMonadLiftFunction)
Std.Irrefl (Init.Core)
Std.IsLinearOrder (Init.Data.Order.Classes)
Std.IsLinearPreorder (Init.Data.Order.Classes)
Std.IsPartialOrder (Init.Data.Order.Classes)
Std.IsPreorder (Init.Data.Order.Classes)
Std.Iterators.Finite (Init.Data.Iterators.Basic)
Std.Iterators.Productive (Init.Data.Iterators.Basic)
Std.LawfulBEqCmp (Init.Data.Order.Ord)
Std.LawfulCommIdentity (Init.Core)
Std.LawfulDeterministicIterator (Init.Data.Iterators.Basic)
Std.LawfulEqCmp (Init.Data.Order.Ord)
Std.LawfulIdentity (Init.Core)
Std.LawfulIteratorLoop (Init.Data.Iterators.Consumers.Monadic.Loop)
Std.LawfulLeftIdentity (Init.Core)
Std.LawfulOrderBEq (Init.Data.Order.Classes)
Std.LawfulOrderInf (Init.Data.Order.Classes)
Std.LawfulOrderLT (Init.Data.Order.Classes)
Std.LawfulOrderLeftLeaningMax (Init.Data.Order.Classes)
Std.LawfulOrderLeftLeaningMin (Init.Data.Order.Classes)
Std.LawfulOrderMax (Init.Data.Order.Classes)
Std.LawfulOrderMin (Init.Data.Order.Classes)
Std.LawfulOrderOrd (Init.Data.Order.ClassesExtra)
Std.LawfulOrderSup (Init.Data.Order.Classes)
Std.LawfulRightIdentity (Init.Core)
Std.LeftIdentity (Init.Core)
Std.MaxEqOr (Init.Data.Order.Classes)
Std.MinEqOr (Init.Data.Order.Classes)
Std.OrientedCmp (Init.Data.Order.Ord)
Std.PRange.InfinitelyUpwardEnumerable (Init.Data.Range.Polymorphic.UpwardEnumerable)
Std.PRange.LawfulUpwardEnumerable (Init.Data.Range.Polymorphic.UpwardEnumerable)
Std.PRange.LawfulUpwardEnumerableLE (Init.Data.Range.Polymorphic.UpwardEnumerable)
Std.PRange.LawfulUpwardEnumerableLT (Init.Data.Range.Polymorphic.UpwardEnumerable)
Std.PRange.LawfulUpwardEnumerableLeast? (Init.Data.Range.Polymorphic.UpwardEnumerable)
Std.PRange.LinearlyUpwardEnumerable (Init.Data.Range.Polymorphic.UpwardEnumerable)
Std.PRange.UpwardEnumerable.Map.PreservesLE (Init.Data.Range.Polymorphic.Map)
Std.PRange.UpwardEnumerable.Map.PreservesLT (Init.Data.Range.Polymorphic.Map)
Std.PRange.UpwardEnumerable.Map.PreservesLeast? (Init.Data.Range.Polymorphic.Map)
Std.PRange.UpwardEnumerable.Map.PreservesRxcSize (Init.Data.Range.Polymorphic.Map)
Std.PRange.UpwardEnumerable.Map.PreservesRxiSize (Init.Data.Range.Polymorphic.Map)
Std.PRange.UpwardEnumerable.Map.PreservesRxoSize (Init.Data.Range.Polymorphic.Map)
Std.Rcc.LawfulRcoIntersection (Init.Data.Range.Polymorphic.PRange)
Std.Rci.LawfulRcoIntersection (Init.Data.Range.Polymorphic.PRange)
Std.Rco.LawfulRcoIntersection (Init.Data.Range.Polymorphic.PRange)
Std.Refl (Init.Core)
Std.ReflCmp (Init.Data.Order.Ord)
Std.Ric.LawfulRcoIntersection (Init.Data.Range.Polymorphic.PRange)
Std.RightIdentity (Init.Core)
Std.Rio.LawfulRcoIntersection (Init.Data.Range.Polymorphic.PRange)
Std.Roc.LawfulRcoIntersection (Init.Data.Range.Polymorphic.PRange)
Std.Roi.LawfulRcoIntersection (Init.Data.Range.Polymorphic.PRange)
Std.Roo.LawfulRcoIntersection (Init.Data.Range.Polymorphic.PRange)
Std.Rxc.IsAlwaysFinite (Init.Data.Range.Polymorphic.PRange)
Std.Rxc.LawfulHasSize (Init.Data.Range.Polymorphic.Basic)
Std.Rxi.IsAlwaysFinite (Init.Data.Range.Polymorphic.PRange)
Std.Rxi.LawfulHasSize (Init.Data.Range.Polymorphic.Basic)
Std.Rxo.IsAlwaysFinite (Init.Data.Range.Polymorphic.PRange)
Std.Rxo.LawfulHasSize (Init.Data.Range.Polymorphic.Basic)
Std.Slice.LawfulSliceSize (Init.Data.Slice.Operations)
Std.Slice.Self (Init.Data.Slice.Basic)
Std.Symm (Init.Core)
Std.Total (Init.Core)
Std.TransCmp (Init.Data.Order.Ord)
Std.Trichotomous (Init.Core)
String.Pos.Raw.IsValid (Init.Data.String.Defs)
String.Pos.Raw.IsValidForSlice (Init.Data.String.Defs)
String.Pos.Splits (Init.Data.String.Lemmas.Splits)
String.Slice.Pattern.LawfulBackwardPattern (Init.Data.String.Pattern.Basic)
String.Slice.Pattern.LawfulForwardPattern (Init.Data.String.Pattern.Basic)
String.Slice.Pattern.Model.IsLongestMatch (Init.Data.String.Lemmas.Pattern.Basic)
String.Slice.Pattern.Model.IsLongestMatchAt (Init.Data.String.Lemmas.Pattern.Basic)
String.Slice.Pattern.Model.IsLongestRevMatch (Init.Data.String.Lemmas.Pattern.Basic)
String.Slice.Pattern.Model.IsLongestRevMatchAt (Init.Data.String.Lemmas.Pattern.Basic)
String.Slice.Pattern.Model.IsMatch (Init.Data.String.Lemmas.Pattern.Basic)
String.Slice.Pattern.Model.IsRevMatch (Init.Data.String.Lemmas.Pattern.Basic)
String.Slice.Pattern.Model.LawfulBackwardPatternModel (Init.Data.String.Lemmas.Pattern.Basic)
String.Slice.Pattern.Model.LawfulForwardPatternModel (Init.Data.String.Lemmas.Pattern.Basic)
String.Slice.Pattern.Model.LawfulToBackwardSearcherModel (Init.Data.String.Lemmas.Pattern.Basic)
String.Slice.Pattern.Model.LawfulToForwardSearcherModel (Init.Data.String.Lemmas.Pattern.Basic)
String.Slice.Pattern.Model.MatchesAt (Init.Data.String.Lemmas.Pattern.Basic)
String.Slice.Pattern.Model.NoPrefixPatternModel (Init.Data.String.Lemmas.Pattern.Basic)
String.Slice.Pattern.Model.NoSuffixPatternModel (Init.Data.String.Lemmas.Pattern.Basic)
String.Slice.Pattern.Model.RevMatchesAt (Init.Data.String.Lemmas.Pattern.Basic)
String.Slice.Pattern.Model.StrictPatternModel (Init.Data.String.Lemmas.Pattern.Basic)
String.Slice.Pattern.StrictBackwardPattern (Init.Data.String.Pattern.Basic)
String.Slice.Pattern.StrictForwardPattern (Init.Data.String.Pattern.Basic)
String.Slice.Pos.Splits (Init.Data.String.Lemmas.Splits)
Subsingleton (Init.Core)
True (Init.Prelude)
Vector.Mem (Init.Data.Vector.Basic)
Vector.Perm (Init.Data.Vector.Perm)
WeaklyLawfulMonadAttach (Init.Control.MonadAttach)
WellFounded (Init.WF)
_private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants (Init.Data.String.Lemmas.Pattern.String.ForwardSearcher)
_private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable (Init.Data.String.Lemmas.Pattern.String.ForwardSearcher)
_private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch (Init.Data.String.Lemmas.Pattern.String.ForwardSearcher)
--- Prop inductives with large elimination, Mathlib (1765) --- [list of 1,765 names omitted here]
--- nested or mutual inductives ---
Aesop.Frontend.RuleExpr Aesop.Frontend.RuleExpr nested=2 mutual=1
Aesop.Index.Basic Aesop.IndexingMode nested=2 mutual=1
Aesop.Script.UScriptToSScript Aesop.Script.StepTree nested=2 mutual=1
Aesop.Tree.Data Aesop.GoalUnsafe nested=10 mutual=3
Aesop.Tree.Data Aesop.MVarClusterUnsafe nested=10 mutual=3
Aesop.Tree.Data Aesop.RappUnsafe nested=10 mutual=3
Batteries.Data.MLList.Basic _private.Batteries.Data.MLList.Basic.0.MLList.MLListImpl nested=1 mutual=1
Init.Prelude Lean.Syntax nested=2 mutual=1
Lean.Compiler.IR.Basic Lean.IR.Alt nested=2 mutual=2
Lean.Compiler.IR.Basic Lean.IR.FnBody nested=2 mutual=2
Lean.Compiler.IR.Basic Lean.IR.IRType nested=2 mutual=1
Lean.Compiler.LCNF.Basic Lean.Compiler.LCNF.Alt nested=2 mutual=4
Lean.Compiler.LCNF.Basic Lean.Compiler.LCNF.Cases nested=2 mutual=4
Lean.Compiler.LCNF.Basic Lean.Compiler.LCNF.Code nested=2 mutual=4
Lean.Compiler.LCNF.Basic Lean.Compiler.LCNF.FunDecl nested=2 mutual=4
Lean.Data.Json.Basic Lean.Json nested=5 mutual=1
Lean.Data.Lsp.Ipc Lean.Lsp.Ipc.CallHierarchy nested=2 mutual=1
Lean.Data.Lsp.Ipc Lean.Lsp.Ipc.ModuleHierarchy nested=2 mutual=1
Lean.Data.Lsp.LanguageFeatures Lean.Lsp.DocumentSymbol nested=4 mutual=1
Lean.Data.PersistentArray Lean.PersistentArrayNode nested=2 mutual=1
Lean.Data.PersistentHashMap Lean.PersistentHashMap.Node nested=3 mutual=1
Lean.Data.PrefixTree Lean.PrefixTreeNode nested=3 mutual=1
Lean.Data.Trie Lean.Data.Trie nested=2 mutual=1
Lean.DocString.Types Lean.Doc.Block nested=8 mutual=1
Lean.DocString.Types Lean.Doc.Inline nested=2 mutual=1
Lean.DocString.Types Lean.Doc.Part nested=2 mutual=1
Lean.Elab.ConfigEval.DeriveEvalConfigItem _private.Lean.Elab.ConfigEval.DeriveEvalConfigItem.0.Lean.Elab.ConfigEval.HandlerTrie nested=3 mutual=1
Lean.Elab.Do.Legacy Lean.Elab.Term.Do.Code nested=6 mutual=1
Lean.Elab.InfoTree.Types Lean.Elab.InfoTree nested=6 mutual=1
Lean.Elab.Tactic.RCases Lean.Elab.Tactic.RCases.RCasesPatt nested=1 mutual=1
Lean.Elab.Term.TermElabM Lean.Elab.Tactic.TacticParsedSnapshot nested=7 mutual=1
Lean.Language.Basic Lean.Language.SnapshotTree nested=4 mutual=1
Lean.Language.Lean.Types Lean.Language.Lean.CommandParsedSnapshot nested=3 mutual=1
Lean.Level Lean.Level.PP.Result nested=1 mutual=1
Lean.Message Lean.MessageData nested=2 mutual=1
Lean.Meta.DiscrTree.Types Lean.Meta.DiscrTree.Trie nested=3 mutual=1
Lean.Meta.Match.Basic Lean.Meta.Match.Example nested=1 mutual=1
Lean.Meta.Match.Basic Lean.Meta.Match.Pattern nested=1 mutual=1
Lean.Meta.Tactic.Grind.AC.Types Lean.Meta.Grind.AC.DiseqCnstr nested=0 mutual=2
Lean.Meta.Tactic.Grind.AC.Types Lean.Meta.Grind.AC.DiseqCnstrProof nested=0 mutual=2
Lean.Meta.Tactic.Grind.AC.Types Lean.Meta.Grind.AC.EqCnstr nested=0 mutual=2
Lean.Meta.Tactic.Grind.AC.Types Lean.Meta.Grind.AC.EqCnstrProof nested=0 mutual=2
Lean.Meta.Tactic.Grind.Arith.CommRing.Types Lean.Meta.Grind.Arith.CommRing.EqCnstr nested=0 mutual=2
Lean.Meta.Tactic.Grind.Arith.CommRing.Types Lean.Meta.Grind.Arith.CommRing.EqCnstrProof nested=0 mutual=2
Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Grind.Arith.Cutsat.CooperSplit nested=9 mutual=12
Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Grind.Arith.Cutsat.CooperSplitPred nested=9 mutual=12
Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Grind.Arith.Cutsat.CooperSplitProof nested=9 mutual=12
Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Grind.Arith.Cutsat.DiseqCnstr nested=9 mutual=12
Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Grind.Arith.Cutsat.DiseqCnstrProof nested=9 mutual=12
Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Grind.Arith.Cutsat.DvdCnstr nested=9 mutual=12
Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Grind.Arith.Cutsat.DvdCnstrProof nested=9 mutual=12
Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Grind.Arith.Cutsat.EqCnstr nested=9 mutual=12
Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Grind.Arith.Cutsat.EqCnstrProof nested=9 mutual=12
Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Grind.Arith.Cutsat.LeCnstr nested=9 mutual=12
Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Grind.Arith.Cutsat.LeCnstrProof nested=9 mutual=12
Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Grind.Arith.Cutsat.UnsatProof nested=9 mutual=12
Lean.Meta.Tactic.Grind.Arith.Linear.Types Lean.Meta.Grind.Arith.Linear.DiseqCnstr nested=0 mutual=7
Lean.Meta.Tactic.Grind.Arith.Linear.Types Lean.Meta.Grind.Arith.Linear.DiseqCnstrProof nested=0 mutual=7
Lean.Meta.Tactic.Grind.Arith.Linear.Types Lean.Meta.Grind.Arith.Linear.EqCnstr nested=0 mutual=7
Lean.Meta.Tactic.Grind.Arith.Linear.Types Lean.Meta.Grind.Arith.Linear.EqCnstrProof nested=0 mutual=7
Lean.Meta.Tactic.Grind.Arith.Linear.Types Lean.Meta.Grind.Arith.Linear.IneqCnstr nested=0 mutual=7
Lean.Meta.Tactic.Grind.Arith.Linear.Types Lean.Meta.Grind.Arith.Linear.IneqCnstrProof nested=0 mutual=7
Lean.Meta.Tactic.Grind.Arith.Linear.Types Lean.Meta.Grind.Arith.Linear.RingDiseqCnstr nested=0 mutual=2
Lean.Meta.Tactic.Grind.Arith.Linear.Types Lean.Meta.Grind.Arith.Linear.RingDiseqCnstrProof nested=0 mutual=2
Lean.Meta.Tactic.Grind.Arith.Linear.Types Lean.Meta.Grind.Arith.Linear.RingEqCnstr nested=0 mutual=2
Lean.Meta.Tactic.Grind.Arith.Linear.Types Lean.Meta.Grind.Arith.Linear.RingEqCnstrProof nested=0 mutual=2
Lean.Meta.Tactic.Grind.Arith.Linear.Types Lean.Meta.Grind.Arith.Linear.RingIneqCnstr nested=0 mutual=2
Lean.Meta.Tactic.Grind.Arith.Linear.Types Lean.Meta.Grind.Arith.Linear.RingIneqCnstrProof nested=0 mutual=2
Lean.Meta.Tactic.Grind.Arith.Linear.Types Lean.Meta.Grind.Arith.Linear.UnsatProof nested=0 mutual=7
Lean.Server.AsyncList Lean.AsyncList nested=3 mutual=1
Lean.Widget.InteractiveDiagnostic Lean.Widget.MsgEmbed nested=4 mutual=1
Lean.Widget.TaggedText Lean.Widget.TaggedText nested=2 mutual=1
Mathlib.SetTheory.Lists Lists'.Subset nested=0 mutual=2
Mathlib.SetTheory.Lists Lists'.Subset.below nested=0 mutual=2
Mathlib.SetTheory.Lists Lists.Equiv nested=0 mutual=2
Mathlib.SetTheory.Lists Lists.Equiv.below nested=0 mutual=2
Mathlib.Tactic.Ring.Common Mathlib.Tactic.Ring.Common.ExBase nested=0 mutual=3
Mathlib.Tactic.Ring.Common Mathlib.Tactic.Ring.Common.ExBaseNat nested=0 mutual=3
Mathlib.Tactic.Ring.Common Mathlib.Tactic.Ring.Common.ExProd nested=0 mutual=3
Mathlib.Tactic.Ring.Common Mathlib.Tactic.Ring.Common.ExProdNat nested=0 mutual=3
Mathlib.Tactic.Ring.Common Mathlib.Tactic.Ring.Common.ExSum nested=0 mutual=3
Mathlib.Tactic.Ring.Common Mathlib.Tactic.Ring.Common.ExSumNat nested=0 mutual=3
Mathlib.Tactic.Translate.Reorder Mathlib.Tactic.Translate.ArgReorder nested=3 mutual=1
ProofWidgets.Data.Html ProofWidgets.Html nested=2 mutual=1
Std.Tactic.Do.Syntax Lean.Parser.Tactic.MCasesPat nested=1 mutual=1
Std.Tactic.Do.Syntax Lean.Parser.Tactic.MRefinePat nested=1 mutual=1
elapsed ms: 145760
-/
