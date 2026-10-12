/-
File: translator/scripts/PrintingBlowup.lean

Measure how large the printer's output is for the three core-Lean corpus
entries, with and without the sharing pass, against the entries'
committed lean4export exports.  Run from translator/ inside the Nix shell:

    lake env lean scripts/PrintingBlowup.lean

It prints Markdown tables: for each entry and threshold, the bytes of
every type and value of the closure printed, the auxiliary definitions
made, the printed nodes against the distinct subterms of each
declaration, and the binder repairs.  `docs/reports/` holds a dated run.
-/
import Lean2Agda.Main

open Lean Lean2Agda

/-- The export's bytes and its expression records, one per distinct
subterm as lean4export keys them (`docs/lean-findings.md`, LF-11). -/
def exportSize (entry : String) : IO (Nat × Nat) := do
  let text ← IO.FS.readFile s!"../corpus/{entry}/lean/term.ndjson"
  let records := text.splitOn "\n" |>.filter (fun line => (line.splitOn "\"ie\":").length > 1)
  return (text.utf8ByteSize, records.length)

structure Row where
  threshold : Nat
  bytes : Nat
  auxiliaries : Nat
  printedNodes : Nat
  worstNodes : Float
  worstAt : Name
  counts : PrintCounts

def measureAt (env : Environment) (closure : Closure) (threshold : Nat) : IO Row := do
  let shared ← IO.ofExcept (shareClosure env threshold closure)
  let p : Printer := { env := ← IO.ofExcept (addAuxiliaries env shared) }
  let mut bytes := 0
  let mut counts : PrintCounts := {}
  for d in shared.declarations do
    let (t, c₁) ← IO.ofExcept (p.type d.info.type)
    counts := counts.add c₁
    bytes := bytes + s!"{agdaIdent d.name} : {t.render}\n".utf8ByteSize
    if let some v := d.info.value? (allowOpaque := true) then
      let (c, c₂) ← IO.ofExcept (p.clause d.info.type v)
      counts := counts.add c₂
      bytes := bytes + (c.render (agdaIdent d.name) ++ "\n").utf8ByteSize
  let mut printedNodes := 0
  let mut worstNodes : Float := 0
  let mut worstAt := Name.anonymous
  for d in closure.declarations do
    let (roots, g) := ShareGraph.build ((constantExprs d.info).map stripMData)
    let chosen := if threshold == 0 then .replicate g.nodes.size false else g.choose roots threshold
    let n := g.printedSize roots chosen
    printedNodes := printedNodes + n
    let ratio := n.toFloat / g.nodes.size.toFloat
    if ratio > worstNodes then worstNodes := ratio; worstAt := d.name
  return { threshold, bytes, auxiliaries := shared.size - closure.size, printedNodes, worstNodes,
           worstAt, counts }

/-- A nonnegative float to `digits` decimal places. -/
def fixed (x : Float) (digits : Nat := 2) : String :=
  let scale := 10 ^ digits
  let n := (x * scale.toFloat).round.toUInt64.toNat
  let fraction := toString (n % scale)
  s!"{n / scale}." ++ String.ofList (List.replicate (digits - fraction.length) '0') ++ fraction

def entry (name : String) (module root : Name) : IO Unit := do
  let env ← importEnvironment #[module]
  let closure ← IO.ofExcept (dependencyClosure env #[root])
  let (exportBytes, records) ← exportSize name
  let distinct := closure.declarations.foldl (fun n d =>
    n + (ShareGraph.build ((constantExprs d.info).map stripMData)).2.nodes.size) 0
  IO.println s!"\n### {name}\n"
  IO.println s!"{closure.size} constants; the export has {records} expression records in {exportBytes} bytes; the declarations have {distinct} distinct subterms, counted per declaration.\n"
  IO.println "| Threshold | Bytes | Bytes per record | Bytes over export bytes | Auxiliaries | Printed nodes | Worst nodes per distinct subterm | Repairs, top and deeper |"
  IO.println "| --- | --- | --- | --- | --- | --- | --- | --- |"
  for t in [0, 64, 32, 16, 8, 4, 2] do
    let r ← measureAt env closure t
    let label := if t == 0 then "off" else toString t
    IO.println s!"| {label} | {r.bytes} | {fixed (r.bytes.toFloat / records.toFloat) 1} | {fixed (r.bytes.toFloat / exportBytes.toFloat)} | {r.auxiliaries} | {r.printedNodes} | {fixed r.worstNodes 1} (`{r.worstAt}`) | {r.counts.topRepairs}, {r.counts.deepRepairs} |"

#eval show IO Unit from do
  entry "list-reverse-reverse" `Init.Data.List.Lemmas ``List.reverse_reverse
  entry "nat-gcd-succ" `Init.Data.Nat.Gcd ``Nat.gcd_succ
  entry "nat-gcd-self" `Init.Data.Nat.Gcd ``Nat.gcd_self
