/-
File: translator/scripts/FlattenBenchmark.lean
-/
import Lean2Agda.Core.Types

open Lean2Agda

@[noinline] def singletonClosure (count : Nat) : Closure :=
  { roots := #[], groups := (Array.range count).map fun i =>
      #[{ name := .num `bench i, info := default, sourceModule := none, dependencies := #[] }] }

@[noinline] def explicitPush (closure : Closure) : Array Declaration := Id.run do
  let mut result := #[]
  for group in closure.groups do
    for declaration in group do
      result := result.push declaration
  return result

/-- Retaining every prefix forces copy-on-write on the next append. -/
@[noinline] def retainPrefixes (closure : Closure) : Array Declaration × Array (Array Declaration) :=
  closure.groups.foldl (fun (result, prefixes) group =>
    let prefixes := prefixes.push result
    (result ++ group, prefixes)) (#[], #[])

def timeRepeated (repetitions : Nat) (compute : Unit → Nat) : IO Nat := do
  let start ← IO.monoNanosNow
  let mut checksum := 0
  for _ in [:repetitions] do
    checksum := checksum + (← IO.lazyPure compute)
  if checksum == 0 then throw (IO.userError "empty benchmark result")
  return (← IO.monoNanosNow) - start

def main : IO Unit := do
  IO.println s!"Lean {Lean.versionString}"
  IO.println "singleton_groups\tclosure_ns\tpush_ns\trepetitions"
  for count in [25000, 50000, 100000, 200000, 400000] do
    let closure ← IO.lazyPure fun _ => singletonClosure count
    let actual ← IO.lazyPure fun _ => closure.declarations
    let alternative ← IO.lazyPure fun _ => explicitPush closure
    unless actual.map (·.name) == alternative.map (·.name) do
      throw (IO.userError "flattening changed contents or order")
    let elapsed ← timeRepeated 32 fun _ => (closure.declarations).size
    let pushElapsed ← timeRepeated 32 fun _ => (explicitPush closure).size
    IO.println s!"{count}\t{elapsed}\t{pushElapsed}\t32"
  IO.println "copy_control_groups\tretaining_prefixes_ns\trepetitions"
  for count in [2000, 4000, 8000] do
    let closure ← IO.lazyPure fun _ => singletonClosure count
    let elapsed ← timeRepeated 1 fun _ =>
      let (result, prefixes) := retainPrefixes closure
      result.size + prefixes.size
    IO.println s!"{count}\t{elapsed}\t1"
