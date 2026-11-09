<!-- File: docs/reports/quotient-rules-2026-11-08.md -->

# The quotient's computation rules under profile U, 2026-11-08

Where the computation rules of `Quot.lift` and `Quot.ind`, which the
profile U scaffold states as Agda rewrite rules since [#21], fire: the
measurements of that issue.  [`printing.md`][printing] (Quotients) states
the emission and the probe it rests on; the gap catalog's
[`quotients`][catalog-quot] entry states the rules and the profiles.  The
code is the translator at this report's commit, under Lean v4.33.1 and
Agda 2.8.0, on a 20-thread Intel i9-12900H with 62 GB of memory, which
other sessions shared; the load averages are given with each run.

## Terms

+  **The rules** are `Quot:lift-β`, a postulate of
   `Quot.lift f h (Quot.mk r a) = f a`, and `Quot:ind-β`, a postulate of
   `Quot.ind mk (Quot.mk r a) = mk a`, each followed by its `REWRITE`
   pragma, with `Eq` declared the rewrite relation.
+  A rule **fires for** a declaration when the declaration checks with the
   rules and is refused without them: `scaffold_check.py` checks the same
   scaffold twice, the second time with `--without-rewrite`, which removes
   the `REWRITE` pragmas and leaves the rules postulates that never fire.
   Such a declaration is one that needs a cast by the propositional rule
   in the safe profiles ([#30]).  A declaration refused both ways for
   another reason is not counted, whether or not a rule fired in it.
+  **Kernel reductions** are the reductions of `Quot.lift` and `Quot.ind`
   that Lean's kernel performs when it re-checks a declaration with its
   diagnostics on (the probe under Remarks): Lean's own record of where it
   uses the rules.
+  **Values**, **checked**, **refused**, **behind a refused type** and
   **unfolded** are as in [`opaque-theorems`][report-opaque].

## The probe

Agda 2.8.0 accepts the scaffold's `Eq`, a data type with an implicit
parameter and two indices, as the rewrite relation, and accepts both rules,
whose left-hand sides apply a postulate to a postulate, with no warning.
The probe module declares `Eq`, the four primitives and the two rules
exactly as the scaffold prints them, then four definitions by `Eq:refl`:
the lift rule itself, the ind rule itself, a lift into a function type
applied to one more argument, and a lift under a binder whose result is a
function only by eta, the shape of `funext`'s proof.  With the rules the
module checks (exit 0); without the two `REWRITE` pragmas each definition,
alone in its module, fails with `UnequalTerms` (exit 42), the first with
`f₃ a₅ != Quot:lift f₃ h₄ (Quot:mk r₁ a₅) of type β₂`.  `--safe` refuses
`--rewriting`, with or without `--confluence-check`:
`[SafeFlagPragma] The --safe mode does not allow OPTIONS pragma
--rewriting`.  The probe ran on 2026-10-13 and again on 2026-11-08 with the
same results.

## The goldens

`make test-translator` regenerates and compares these, and checks the
fixture both ways; the other goldens were checked without the rules by
hand on 2026-11-08 at load averages near 6.  The kernel column is the
probe under Remarks.

| Scaffold | Values | Checked with the rules | Checked without | Rules fire for | Kernel reductions |
| --- | --- | --- | --- | --- | --- |
| `list-reverse-reverse` | 21 | 17 | 17 | nothing | none |
| `nat-gcd-succ` | 201 | 142 | 141 | `funext` | `funext`, `Quot.lift` twice |
| `nat-gcd-self` | 266 | 183 | 182 | `funext` | `funext`, `Quot.lift` twice |
| `quotients` | 8 | 8 | 4 | the four roots | the four roots, once each |

Every other golden holds no quotient: their scaffolds change by the options
line and the `BUILTIN REWRITE` line in `Eq`'s block, and their listings not
at all.  In both gcd listings `funext`'s refusal,
`Quot:lift (λ f₈ → f₈ x₇) (λ x₈ x₉ h₁₀ → h₁₀ x₇) (Quot:mk eqv₅ f₂)`, is
the only line that goes, and the two rules are the module's two new
declarations (322 and 254 in all).  The fixture
`tests/TranslatorTests/Input/Quotients.lean` has four theorems, each true
by `rfl` because the kernel reduces a primitive on `Quot.mk`: `succ_mk`,
`over_mk` and `eta_mk` reduce `Quot.lift` once each, and `ind_mk` reduces
`Quot.ind` once, although proof irrelevance alone would have identified its
two proofs.  Without the rules Agda refuses all four, and the fallback
unfolds `congrArg` once in vain, since the message of `eta_mk`'s refusal
names it.

The checker's times with the rules, at load averages between 2 and 5:
`nat-gcd-self` 64 runs in 138.5 s, `nat-gcd-succ` 50 in 76.5 s, the fixture
one run in 0.1 s; without the rules, 65 runs in 164.3 s and 51 in 87.8 s.

## `Multiset.map_map`

The corpus entry [`multiset-map-map`][multiset] needs Mathlib's cache
(`make lean-cache`, 44 s here, then `make lean-smoke`).  Its closure under
the translator is 191 constants; the scaffold, 80 KB and 96 declarations
(11 data types and records, 66 values, 34 of them theorems), printed in
3 s and scope-checked in under a second, with nothing refused by the
translator.  Checked at load average 8:

| Run | Values checked | Refused | Unfolded | Runs, seconds |
| --- | --- | --- | --- | --- |
| with the rules | 53 | 13 | 1, in vain | 15, 5.6 |
| without the rules | 51 | 15 | 2, in vain | 18, 6.3 |

The rules fire for `Multiset.map_map`, the entry's root, and `funext`,
which are the two declarations of the closure whose kernel check reduces
`Quot.lift` (three times and twice, the entry's
[notes][multiset-notes]); without the rules Agda refuses the root at
`Quot:mk Setoid:r (List:map g₃ (List:map f₄ l₆)) != …`, after unfolding
the theorem `Multiset.map._proof_1` in vain.  With them the root checks:
the three reductions the notes list for it, each after unfolding
`Multiset.map` and `Quot.liftOn`, go through as the kernel makes them.

The 13 refusals left are none of the quotient's.  Twelve are a recursor's
iota, which [#19] supplies: `List.rec` under `List.map`, `List.filterMap`,
`List.Perm.refl` and the `brecOn` definitions, `Option.rec` under
`List.filterMap`'s equations, and the `noConfusion` definitions of
`Option`, whose types reduce only through `Option.casesOn` (one of them a
`CannotApply`, `Option.some.noConfusion`, for which the fallback unfolded
`heq_of_eq` in vain).  The thirteenth is K-like reduction in `eq_of_heq`,
which the normalizer of [#26] makes explicit.  So the entry's root checks
under profile U, which is this issue's part of its acceptance criterion;
the whole closure checks once recursors compute and K-like reduction is
explicit.

## `Init.Core`

The scaffold of every declaration of `Init.Core` (`lake exe lean2agda
--out core Init.Core`) is 1.2 MB and 1,965 declarations: 144 data types
and records, 1,660 values, 510 of them theorems, and the two rules.  It
printed in 2 s.  The two checks ran side by side, from load average 5.33
to 4.99, and took 86 minutes of wall time together:

| Run | Values checked | Refused | Behind a refused type | Unfolded | Runs, seconds |
| --- | --- | --- | --- | --- | --- |
| with the rules | 1,351 | 305 | 4 | 4, one in vain | 311, 5,016 |
| without the rules | 1,344 | 312 | 4 | 6, five in vain | 320, 5,161 |

The run without the rules reproduces the figures of
[`opaque-theorems`][report-opaque] (1,344 checked, 312 refused, 4 behind
the refused type of `apply_eqRec`).  The rules fire for seven
declarations, which are exactly the seven whose kernel check reduces
`Quot.lift` or `Quot.ind` (Remarks), as follows:

+  `funext`, `Quot.lift` under a binder twice, as in the corpus;
+  `Quot.liftBeta` and `Quot.indBeta`, Lean's statements of the two rules,
   proved by `rfl`, which without the rules Agda refuses at
   `Quot:lift f₃ c₄ (Quot:mk r₁ a₅) != f₃ a₅` and
   `Quot:ind p₃ (Quot:mk r₁ a₄) != p₃ a₄`;
+  `Quot.liftIndepPr1`, `Quotient.exact` and the private
   `Quotient.rel.refl`, each a `Quot.lift` (through `Quot.liftOn` or
   `Quotient.lift`) on `Quot.mk` whose result is the type to check
   against;
+  `Quotient.lift₂._proof_2`, which needs the rule and two theorems
   unfolded besides: with the rules the fallback unfolds `Setoid.refl` and
   `Quotient.lift₂._proof_1` for it and it checks, the only unfoldings of
   the corpus scaffolds and `Init.Core` that the rule made useful; without
   the rules the same unfoldings are in vain.

No refusal of the run with the rules names a quotient primitive.  The
305 left are the classes of [`opaque-theorems`][report-opaque]: recursors'
iota ([#19]), K-like reduction ([#26]) and the comparisons of two proofs
of one proposition ([#27]).  `Quot.pliftOn`,
`Quot.pliftOn._proof_1` and `Quotient.pliftOn` stand behind `apply_eqRec`,
whose type needs `h = Eq.refl b` for `h : b = b`, which is UIP, not a
computation rule.  The fallback's one other help, `Quotient.rec` checking
once `Quotient.sound` unfolds to `Quot.sound`, is unchanged.

## Remarks

The kernel reductions come from the following probe, run from
`translator/` as `lake env lean` on a scratch file.  It re-checks every
theorem and definition of the translator's own closure (pre-sharing) with
the kernel's diagnostics on, the method of the corpus entry's
[notes][multiset-notes], and took 11 s.  Twelve runs on 2026-11-08 gave
the same list eleven times; the first run, made while nine `lake exe`
processes and a `lake build` started in the same package, listed only
`funext` (both gcd closures) and `Quotient.rel.refl`, and nothing for the
fixture, and three runs made to reproduce that condition gave the full
list, so the counters are trusted here as the eleven agreeing runs give
them.  They name exactly the declarations the rules fire for in Agda, in
every scaffold above; [`lean-findings.md`][findings], LF-12, records that
agreement and the short run.

```lean
import Lean2Agda.Main
open Lean Lean2Agda

def quotReductions (env : Environment) (label : String) (roots : Array Name) : IO Unit := do
  let closure ← IO.ofExcept (dependencyClosure env roots)
  let mut checked := 0
  let mut hits : Array String := #[]
  for d in closure.declarations do
    let decl? := match d.info with
      | .thmInfo v => some (Declaration.thmDecl { v with name := d.name ++ `_recheck })
      | .defnInfo v => some (Declaration.defnDecl { v with name := d.name ++ `_recheck })
      | _ => none
    let some decl := decl? | continue
    checked := checked + 1
    match (env.toKernelEnv.enableDiag true).addDecl {} decl with
    | .error _ => hits := hits.push s!"  {d.name}: rejected"
    | .ok kenv =>
      let ws := kenv.diagnostics.unfoldCounter.toList.filter fun (r, _) =>
        r == ``Quot.lift || r == ``Quot.ind
      unless ws.isEmpty do hits := hits.push s!"  {d.name}: {ws}"
  IO.println s!"{label}: {closure.size} declarations, {checked} theorems and definitions re-checked"
  for h in hits do IO.println h

#eval show IO Unit from do
  let env ← importEnvironment #[`Init.Data.Nat.Gcd, `Init.Data.List.Lemmas]
  quotReductions env "Nat.gcd_self" #[``Nat.gcd_self]
  quotReductions env "Nat.gcd_succ" #[``Nat.gcd_succ]
  quotReductions env "List.reverse_reverse" #[``List.reverse_reverse]
  let core ← importEnvironment #[`Init.Core]
  quotReductions core "Init.Core" (← IO.ofExcept (selectRoots core #[`Init.Core] #[]))
  let q ← importEnvironment #[`TranslatorTests.Input.Quotients]
  quotReductions q "QuotFixtures" (← IO.ofExcept (selectRoots q #[`TranslatorTests.Input.Quotients] #[]))
```

Its output, on eleven of the twelve runs, was as follows:

```text
Nat.gcd_self: 334 declarations, 251 theorems and definitions re-checked
  funext: [(Quot.lift, 2)]
Nat.gcd_succ: 271 declarations, 192 theorems and definitions re-checked
  funext: [(Quot.lift, 2)]
List.reverse_reverse: 41 declarations, 21 theorems and definitions re-checked
Init.Core: 2128 declarations, 1632 theorems and definitions re-checked
  funext: [(Quot.lift, 2)]
  Quot.liftIndepPr1: [(Quot.lift, 2)]
  Quot.indBeta: [(Quot.ind, 1)]
  Quot.liftBeta: [(Quot.lift, 1)]
  Quotient.lift₂._proof_2: [(Quot.lift, 2)]
  _private.Init.Core.0.Quotient.rel.refl: [(Quot.lift, 2)]
  Quotient.exact: [(Quot.lift, 2)]
QuotFixtures: 18 declarations, 7 theorems and definitions re-checked
  QuotFixtures.eta_mk: [(Quot.lift, 1)]
  QuotFixtures.ind_mk: [(Quot.ind, 1)]
  QuotFixtures.over_mk: [(Quot.lift, 1)]
  QuotFixtures.succ_mk: [(Quot.lift, 1)]
```

## To rerun

Inside `nix develop`, from `translator/`:

```sh
lake exe lean2agda --out out Init.Data.Nat.Gcd -- Nat.gcd_self
python3 ../scripts/python/scaffold_check.py --messages out/U/Init/Data/Nat/Gcd.agda
python3 ../scripts/python/scaffold_check.py --messages --without-rewrite out/U/Init/Data/Nat/Gcd.agda
lake exe lean2agda --out core Init.Core
python3 ../scripts/python/scaffold_check.py --messages core/U/Init/Core.agda
python3 ../scripts/python/scaffold_check.py --messages --without-rewrite core/U/Init/Core.agda
lake exe lean2agda --out multiset Mathlib.Data.Multiset.MapFold -- Multiset.map_map
```

The last needs `make lean-cache` first.

[#19]: https://github.com/formalverification/lean2agda/issues/19
[#21]: https://github.com/formalverification/lean2agda/issues/21
[#26]: https://github.com/formalverification/lean2agda/issues/26
[#27]: https://github.com/formalverification/lean2agda/issues/27
[#30]: https://github.com/formalverification/lean2agda/issues/30
[printing]: ../translator/printing.md
[report-opaque]: opaque-theorems-2026-10-13.md
[catalog-quot]: ../foundations/gap-catalog.md#quotients
[multiset]: ../../corpus/multiset-map-map/
[multiset-notes]: ../../corpus/multiset-map-map/notes.md
[findings]: ../lean-findings.md
