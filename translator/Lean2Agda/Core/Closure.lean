/-
File: translator/Lean2Agda/Core/Closure.lean
-/
import Lean2Agda.Core.Types
import Lean.Util.ForEachExpr
import Lean.Util.SCC

namespace Lean2Agda

open Lean

/-- Stable order independent of environment and hash-table iteration. -/
def sortNames (names : Array Name) : Array Name :=
  (names.map fun n => (toString n, n)).qsort (·.1 < ·.1) |>.map (·.2)

def uniqueNames (names : Array Name) : Array Name :=
  sortNames (names.foldl (fun (s : Std.HashSet Name) n => s.insert n) {} |>.toArray)

def moduleOf (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  env.header.moduleNames[idx.toNat]?

/-- Visit shared subexpressions once.  Projections carry a structure
name outside `.const`; literals carry an implicit primitive type. -/
def expressionDependencies (expr : Expr) : Array Name := runST fun s => do
  let names : ST.Ref s (Std.HashSet Name) ← ST.mkRef {}
  expr.forEach (ω := s) (m := ST s) fun e => do
    match e with
    | .const n _ | .proj n _ _ => names.modify (·.insert n)
    | .lit (.natVal _) => names.modify (·.insert ``Nat)
    | .lit (.strVal _) => names.modify (·.insert ``String)
    | _ => pure ()
  return sortNames (← names.get).toArray

/-- Index primitive recursors by their inductive types once, including
auxiliary recursors generated for nested and mutual inductives.
lean4export at the pinned revision uses the same index. -/
def recursorIndex (env : Environment) : Std.HashMap Name (Array Name) :=
  env.constants.fold (init := {}) fun index _ info =>
    match info with
    | .recInfo r => r.all.foldl (fun index n =>
        index.insert n ((index[n]?.getD #[]).push r.name)) index
    | _ => index

/-- Expression dependencies plus the companions needed to emit a
complete inductive, mutual definition, or primitive quotient package.
Recursor reduction rules are kernel expressions too. -/
def directDependencies (recursors : Std.HashMap Name (Array Name))
    (info : ConstantInfo) : Array Name := Id.run do
  let mut deps := expressionDependencies info.type
  if let some value := info.value? (allowOpaque := true) then
    deps := deps ++ expressionDependencies value
  deps := deps ++ match info with
    | .inductInfo v => v.all.toArray ++ v.ctors.toArray ++ (recursors[v.name]?.getD #[])
    | .ctorInfo v => #[v.induct]
    | .recInfo v => v.rules.foldl (fun ns r =>
        ns ++ #[r.ctor] ++ expressionDependencies r.rhs) v.all.toArray
    | .defnInfo v => v.all.toArray
    | .thmInfo v => v.all.toArray
    | .opaqueInfo v => v.all.toArray
    | .quotInfo _ => #[`Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]
    | _ => #[]
  return uniqueNames deps

/-- Explicit declarations are roots.  Otherwise select every declaration
owned by the named modules, including private and generated declarations;
imports contribute only the dependencies of those roots. -/
def selectRoots (env : Environment) (modules requested : Array Name) : Except String (Array Name) := do
  if !requested.isEmpty then
    for name in requested do
      unless env.contains name do
        throw s!"unknown declaration {name}"
    return uniqueNames requested
  return sortNames <| env.constants.fold (init := #[]) fun names name _ =>
    if (moduleOf env name).any modules.contains then names.push name else names

/-- Compute reachability before ordering the graph, so cycles cannot
truncate the closure.  Tarjan's algorithm orders strongly connected
groups with dependencies first; names inside a group are sorted. -/
def dependencyClosure (env : Environment) (roots : Array Name) : Except String Closure := do
  let roots := uniqueNames roots
  let recursors := recursorIndex env
  let mut queue := roots
  let mut seen := roots.foldl (fun (s : Std.HashSet Name) n => s.insert n) {}
  let mut declarations : Std.HashMap Name Declaration := {}
  let mut next := 0
  while h : next < queue.size do
    let name := queue[next]
    next := next + 1
    let some info := env.find? name | throw s!"missing dependency {name}"
    let dependencies := directDependencies recursors info
    declarations := declarations.insert name { name, info, sourceModule := moduleOf env name, dependencies }
    for dep in dependencies do
      unless seen.contains dep do
        seen := seen.insert dep
        queue := queue.push dep
  let names := sortNames queue
  let groups := SCC.scc names.toList (fun n => (declarations[n]!.dependencies).toList)
  return { roots, groups := groups.toArray.map fun group =>
    (sortNames group.toArray).map (declarations[·]!) }

end Lean2Agda
