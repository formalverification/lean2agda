<!-- File: corpus/subtype-coe-eta/notes.md -->

# Subtype.coe_eta

The entry for structure eta, translated by issue M1-9 ([#9]).  Mathlib
declares `Subtype.coe_eta` in `Mathlib.Data.Subtype`; its proof cites
`Subtype.ext`, from Lean's `Init.Core`.  Two Agda files translate it, one
for each encoding of Lean's `Prop` that issue M3-2 ([#27]) is to decide
between: `agda/SubtypeCoeEta.agda` under encoding A (propositions are
types of `Set` with a proof of irrelevance), with profile CC
(`--safe --cubical-compatible`); and `agda/SubtypeCoeEtaProp.agda` under
encoding B (propositions live in Agda's `Prop`), with profile CC and the
flag `--prop` (`--safe --cubical-compatible --prop`).

## Statement

Lean's statement, as `#check` prints it:

    @Subtype.coe_eta : ∀ {α : Sort u_1} {p : α → Prop} (a : { a // p a }) (h : p ↑a), ⟨↑a, h⟩ = a

The Agda statements, with `a` and `p` generalized level variables, are
as follows:

    -- SubtypeCoeEta.agda, encoding A
    coe-eta : {P : A → Ω p} (x : Subtype P) (h : proj₁ (P (val x))) → mk (val x) h ≡ x
    -- SubtypeCoeEtaProp.agda, encoding B
    coe-eta   : {A : Set a} {P : A → Prop p} (x : Subtype P) (h : P (val x)) → mk (val x) h ≡ x
    coe-eta-P : {A : Prop a} {P : A → Prop p} (x : SubtypeP P) (h : P (valP x)) → mkP (valP x) h ≡ x

They match up to notation.  Lean's structure `Subtype` becomes a record
with constructor `mk` and fields `val` and `property`; `↑a` is
`Subtype.val a`, since Mathlib declares the projection a coercion
(`attribute [coe] Subtype.val`), and `⟨↑a, h⟩` is `Subtype.mk`.  The
binder `a` becomes `x`, because the files use `a` for a level.  Under
encoding A the predicate takes values in `Ω p = Σ (Set p) Irrelevant`,
the `Ω` of `multiset-map-map` and `set-ext`; under encoding B, in
`Prop p`.

Lean's `α : Sort u_1` ranges over types and over propositions, so the
one declaration covers both.  Under encoding A a proposition is the
carrier of an `Ω`, a type of `Set`, so `A : Set a` covers both cases too
and the file has one statement.  Under encoding B a proposition is an
element of `Prop a`, a sort different from `Set a`, so the case
`u_1 = 0` needs its own record, `SubtypeP` over `A : Prop a`, and its
own theorem, `coe-eta-P`: the specialization by zero level parameters
of issue M3-3 ([#28]).  Lean's `Subtype` at `u_1 = 0` lives in
`Sort (max 1 0)`, which is `Type`, so `SubtypeP` lives in `Set` as
well, with both its fields in `Prop`.

## Tier

`#print axioms` prints that `Subtype.coe_eta` depends on no axioms, and
so does `Subtype.ext`, so the entry is T0.  Neither Agda file takes a
parameter or uses an axiom.  Nothing is classical, so the statement and
both proofs survive de-classicalization unchanged.

## What the kernel term needed

The export holds 14 declarations: the inductive types `Subtype`, `Eq`
and `HEq`; the definitions `Subtype.val`, `Subtype.casesOn`,
`Eq.casesOn`, `Eq.ndrec`, `rfl`, `cast` and the private matcher
`Subtype.ext.match_1_1`; and the theorems `Eq.symm`, `eq_of_heq`,
`Subtype.ext` and `Subtype.coe_eta`.

`coe_eta`'s term is `Subtype.ext ⟨↑a, h⟩ a rfl`, where `rfl` proves
`↑⟨↑a, h⟩ = ↑a`, which the kernel accepts by reducing the projection.
The work is in `Subtype.ext`.  Its pattern match compiles to the matcher,
which takes both subtypes apart with `Subtype.casesOn`, takes the
equation of their values apart with `Eq.casesOn` after generalizing it
through `HEq`, and recovers it with `eq_of_heq`; the match's one case,
`fun val property property_1 => rfl`, must have the type
`⟨val, property⟩ = ⟨val, property_1⟩`.

What the kernel's check relied on was measured: all 11 theorems and
definitions of the closure were re-checked in Lean's kernel with its
diagnostics on, and in the elaborator with structure eta switched off
(the probe under Remarks).  By feature, as follows:

+  `proof-irrelevance`: the case of `Subtype.ext`'s match.  The `rfl`
   there proves `⟨val, property⟩ = ⟨val, property⟩`, and the kernel
   accepts it at `⟨val, property⟩ = ⟨val, property_1⟩` only by
   identifying the two proofs of `p val`.  The kernel's diagnostics do
   not count this conversion, but the term leaves no other way for the
   case to have its type.  Under encoding A the Agda `ext` makes the
   step explicit, `cong (mk v) (proj₂ (P v) h₁ h₂)`, with the proof that
   `Ω` carries; under encoding B it is `refl`, by the definitional
   irrelevance of `Prop`.
+  `structure-eta`: not used.  The statement is eta's content, but none
   of the 11 declarations needs structure eta: each passes the
   elaborator's re-check with eta off (controls: `x = ⟨x.1, x.2⟩ := rfl`
   on a sigma type was flagged, and `⟨n, i⟩ = ⟨n, i⟩ := rfl` was not).
   Lean's kernel would accept the statement by `rfl`, through eta and
   proof irrelevance together (measured: `Subtype.mk a.val h = a := rfl`
   was accepted, for `α` a type and for `α` a proposition), but
   Mathlib's proof goes through `Subtype.ext`, whose match eliminates
   both sides instead.  Lean's own `Subtype.eta` (`Init.Core`, line
   1371), the same statement proved by `cases a; exact rfl`, needs no
   eta either.  The manifest listed this feature; it is removed.  The
   corpus still covers it through `lists-subset-refl`, whose
   `Lists'.to_ofList` needs eta for `Sigma`.  The direct Agda proofs,
   `coe-eta-direct`, do use record eta: `mk (val x) (property x)` is `x`
   by definition.
+  `k-and-uip`: `eq_of_heq`, the one declaration whose check reduced a
   recursor that admits K-like reduction (`Eq.rec`, twice).  Its proof
   is K-like reduction on a universe, `cast h a = a` for `h : α = α`
   ([`../multiset-map-map/notes.md`](../multiset-map-map/notes.md) reads
   it).  The matcher uses it at level 0, `eq_of_heq.{0}`, on two proofs
   of an equation; there `α` is a proposition, and `cast h a = a` holds
   by proof irrelevance, so a translation that specializes `eq_of_heq`
   at level 0 ([#28]) needs no K.  Neither Agda file uses K.
+  `large-elimination`: `cast`, which eliminates `Eq` into `Sort u`,
   inside `eq_of_heq`.  The matcher uses both at level 0, where the
   elimination is into `Prop`; the large elimination is in the generic
   declarations the export carries, not in the use.  The other
   eliminations are into `Prop` (`Eq.casesOn.{0,u_1}`,
   `Eq.ndrec.{0,u_1}`) or of `Subtype`, which is not a proposition.
+  `universe-levels`: one level parameter, `u_1`, with `α : Sort u_1`,
   so that `α` may be a proposition (the Statement section); the
   equation lives in `Sort (max 1 u_1)` (`Eq.{max((0+1),u_1)}` in the
   export).  No `imax` occurs.
+  `projections-and-let`: `Subtype.val` is a projection function, whose
   value is the export's one projection expression; the kernel reduces
   `Subtype.val ⟨↑a, h⟩` to `↑a` when it checks the `rfl` above, and
   Agda's `val` computes on `mk` the same way.  One `let`, `this` in
   `eq_of_heq`, goes with that proof.

The term has no axioms, quotients, literals, `Decidable` instances or
nested inductive types.

## Instance arguments

No instance arguments, in the statement or in the proof.

## The Agda version

**`agda/SubtypeCoeEta.agda`**, encoding A, profile CC, has no
parameters.  `Subtype` is a record over `P : A → Ω p`.  `ext` is
Lean's `Subtype.ext`, by matching both records and the equation of
their values, `ext {a₁ = mk v h₁} {a₂ = mk .v h₂} refl`, and closes with
the irrelevance proof of `P v` where Lean's kernel identifies the proofs
by definition.  `coe-eta` is Lean's term, `ext refl`.  `coe-eta-direct`
proves the statement in one step, `cong (mk (val x)) (proj₂ (P (val x))
h (property x))`, by record eta and the same irrelevance proof.  A
control file showed that `refl` does not prove the statement under this
encoding: Agda answered `h != x .property of type proj₁ (P (val x))`
(`UnequalTerms`).  The match draws no warning, because it unifies
variables only.

**`agda/SubtypeCoeEtaProp.agda`**, encoding B, profile CC with
`--prop`, has no parameters.  `Subtype` is a record over
`P : A → Prop p`, and `coe-eta-direct` is `refl`: record eta makes `x`
equal to `mk (val x) (property x)`, and `Prop`'s irrelevance makes `h`
equal to `property x`.  That is the conversion Lean's kernel would
accept for `rfl`.  `coe-eta` is Lean's term, `ext refl`.  `ext` itself
is not Lean's match but a substitution along the equation, because the
match, `ext {a₁ = mk v h₁} {a₂ = mk .v h₂} refl = refl`, is accepted
under `--cubical-compatible --prop` only with the warning
`UnsupportedIndexedMatch`: "It relies on substitution in Setω, which is
not yet supported", so that the function "will not compute when applied
to transports".  Control files showed the warning with every level
fixed at 0, and no warning under `--prop` alone, that is, profile K.
This refines the gap catalog's probe `P25bPropEqCC`, in which matching
on a `Prop`-valued indexed family under `--cubical-compatible --prop` is
an error: matching an equation in `Set` with a `Prop` field in scope is
accepted, with the warning.  The file ends with `SubtypeP` and
`coe-eta-P` for `α` a proposition, also by `refl`.

Which encoding to emit is [#27]'s decision, on measurements across the
corpus and `Init`.  For this entry I would emit encoding B: it is the
one of the two that reproduces the term's single nontrivial conversion,
proof irrelevance in `Subtype.ext`, without a cast, and its costs here
are small, a second record for `α` a proposition and a substitution in
place of Lean's match.  Encoding A's cost is one use of the irrelevance
witness for each pair of proofs Lean identifies: here one, in `ext`,
which is the cast Lean4Less ([#26]) would insert.  What weighs against B
across the corpus is visible here in small: every constant with a
universe parameter that may be `Prop` needs a copy per instantiation,
and under `--cubical-compatible` a match that would transport a `Prop`
is refused or, as here, warned about.

## Sizes

| Measure | Value |
| --- | --- |
| Export, bytes | 46,536 |
| Export, records | 963 |
| Export, expression records | 797 |
| Export, declarations | 14: 3 inductive, 7 def, 4 thm |
| Agda, lines per file | `SubtypeCoeEta.agda` 76, of which 25 are code; `SubtypeCoeEtaProp.agda` 77, of which 31 are code |
| Agda, check time | 0.4 seconds for the two files (Agda 2.8.0, no `.agdai` files of the corpus) |

## Remarks

The export was made on 2026-10-11 with lean4export v4.33.0 (format
3.1.0) under Lean v4.33.1 (commit `819816b`), the pins of
[`docs/pinning.md`](../../docs/pinning.md).  Two runs gave the same
bytes (SHA-256 `0bd0b788...06a25dda`).

The reduction counts come from the probe printed in
[`../multiset-map-map/notes.md`](../multiset-map-map/notes.md), Remarks,
which re-checks every theorem and definition of a closure in the kernel
with its diagnostics on and lists the reductions of `k = true`
recursors and of `Quot.lift`.  For `Subtype.coe_eta` it printed one
line, `eq_of_heq: [(Eq.rec, 2)]`, and no `Quot.lift`.  The test for
structure eta re-checks each stored value in the elaborator, with and
without eta, and lists the declarations accepted only with it; the eta
statement itself was tested in the kernel with proof `Eq.refl`.  Both
ran from `translator/` as `lake env lean` on a scratch file on
2026-10-11:

```lean
import Mathlib.Data.Subtype
open Lean Elab Command Meta

/-- The closure lean4export exports: types, values, constructors, recursors. -/
partial def closure (env : Environment) (n : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := [n]
  while !todo.isEmpty do
    let c := todo.head!
    todo := todo.tail!
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    let mut deps := ci.type.getUsedConstants.toList
    if let some v := ci.value? (allowOpaque := true) then
      deps := deps ++ v.getUsedConstants.toList
    match ci with
    | .inductInfo v => deps := deps ++ v.ctors ++ v.all
    | .ctorInfo v => deps := deps ++ [v.induct]
    | .recInfo v => deps := deps ++ v.all
    | _ => pure ()
    todo := deps ++ todo
  return seen

/-- Whether the elaborator accepts a declaration's stored value under `cfg`. -/
def accepts (ci : ConstantInfo) (cfg : Meta.Config → Meta.Config) : CoreM Bool := do
  let some v := ci.value? (allowOpaque := true) | return true
  let act : MetaM Bool := withConfig cfg <| withTransparency .all do
    try
      Meta.check v
      isDefEq (← inferType v) ci.type
    catch _ => return false
  act.run'

elab "#eta_needed " nm:ident : command => do
  let env ← getEnv
  let mut hits : Array String := #[]
  let mut n : Nat := 0
  for c in (closure env nm.getId).toList do
    let some ci := env.find? c | continue
    unless ci matches .thmInfo _ || ci matches .defnInfo _ do continue
    n := n + 1
    let on ← liftCoreM <| accepts ci (fun c => c)
    let off ← liftCoreM <| accepts ci (fun c => { c with etaStruct := .none })
    if on && !off then hits := hits.push s!"{c}"
    if !on then hits := hits.push s!"{c}: not accepted even with eta on"
  logInfo m!"{nm.getId}: {n} checked; needing structure eta: {hits.toList}"

elab "#kernel_rfl " name:ident " : " stmt:term : command => do
  let (ty, val) ← liftTermElabM do
    let t ← instantiateMVars (← Term.elabTerm stmt (some (mkSort .zero)))
    let v ← forallTelescope t fun xs body => do
      let some (_, _, r) := body.eq? | throwError "not an equation"
      mkLambdaFVars xs (← mkEqRefl r)
    pure (t, v)
  let decl := Declaration.thmDecl
    { name := name.getId, levelParams := [], type := ty, value := val }
  match ((← getEnv).toKernelEnv.enableDiag true).addDecl {} decl with
  | .error _ => logInfo m!"{name.getId}: rejected"
  | .ok _ => logInfo m!"{name.getId}: accepted"

#eta_needed Subtype.coe_eta
#eta_needed Subtype.eta
#kernel_rfl coeEtaRfl : ∀ (p : Nat → Prop) (a : Subtype p) (h : p a.val), Subtype.mk a.val h = a
#kernel_rfl coeEtaRflProp : ∀ (q : Prop) (p : q → Prop) (a : Subtype p) (h : p a.val), Subtype.mk a.val h = a

-- Controls for #eta_needed.
theorem etaCtl (x : Σ n : Nat, Fin n) : x = ⟨x.1, x.2⟩ := rfl
theorem noEtaCtl (n : Nat) (i : Fin n) : (⟨n, i⟩ : Σ n : Nat, Fin n) = ⟨n, i⟩ := rfl
#eta_needed etaCtl
#eta_needed noEtaCtl
```

It printed the following:

```text
Subtype.coe_eta: 11 checked; needing structure eta: []
Subtype.eta: 6 checked; needing structure eta: []
coeEtaRfl: accepted
coeEtaRflProp: accepted
etaCtl: 7 checked; needing structure eta: [etaCtl]
noEtaCtl: 5 checked; needing structure eta: []
```

The elaborator's check stands in for the kernel's, which has no switch
for eta; the controls show that it tells the two cases apart.

[#9]: https://github.com/formalverification/lean2agda/issues/9
[#26]: https://github.com/formalverification/lean2agda/issues/26
[#27]: https://github.com/formalverification/lean2agda/issues/27
[#28]: https://github.com/formalverification/lean2agda/issues/28
