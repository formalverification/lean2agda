<!-- File: docs/lean-findings.md -->

# Findings about Lean's internals

The register of everything this project finds questionable in Lean's
kernel, elaborator or tooling: a possible inconsistency, a trusted tool
that answers wrongly, an assumption a proof can make without saying so.
Every session that meets one adds an entry here with its evidence, as
`CLAUDE.md` asks, whether or not it is already known upstream; a
question asked and answered with nothing found is recorded too, so that
it is not asked again and is rerun when the pin moves.

Each entry has a number that never changes, a severity, how it was
found, the evidence and how to reproduce it, its upstream status, and
what it means for this project.  The severities are as follows:

+  **S0, kernel soundness**: the kernel accepts a proof of `False`, or a
   declaration it should reject.  Report upstream at once.
+  **S1, trust tooling**: a tool users rely on to see what a proof
   assumes (`#print axioms`, the exporter, Lake's checks) answers wrongly,
   so an assumption can go unseen.
+  **S2, surprising by design**: documented behavior that a translator or
   a reader can misread.  The trust escape hatches (`sorryAx`, the
   `native_decide` axioms, the native-reduction family, the compiler's
   `lc*` axioms, `partial`, `implemented_by`, `unsafe`) are catalogued in
   the gap catalog's entry [`trust-escape-hatches`][catalog-hatches]; an
   entry here adds only what a measurement found.
+  **Checked**: a question that was asked and answered with nothing
   wrong found.

## LF-1: `#print axioms` omits axioms behind an inductive type, `sorryAx` included

+  **Severity**.  S1.  The kernel checked every declaration involved; the
   audit of what they assume is what goes wrong.
+  **Found**.  2026-10-08, by the axiom atlas ([#11], pull request [#71]),
   at Lean v4.33.1 and Mathlib v4.33.1.
+  **What**.  `Lean.collectAxioms`, which `#print axioms` calls, caches the
   axioms of a constant it reaches while one of that constant's own
   dependencies is still being visited, counting the dependency as having
   none.  The cycles where this happens are an inductive type and its
   constructors (a constructor's type mentions its type, and the type
   depends on its constructors) and mutually recursive definitions, such as
   the `_unsafe_rec` companions of mutual `partial def`s.  Since Lean
   v4.30.0 every `.olean` stores, for its exported declarations, axioms
   computed this way, and a module that imports it trusts the table instead
   of walking the bodies, so the omission depends on hash order and
   outlives the module.  A query in the defining module is right; one from
   an importing module can be wrong.
+  **It hides `sorry`**.  The upstream report shows `Classical.choice`
   hidden.  The same two files with `sorry` in place of the choice, under
   the pinned Lean (2026-10-08), as follows:

   ```lean
   -- A.lean
   def pick : Nat := sorry

   structure S9 where
     x : Fin (pick + 1)

   #print axioms S9        -- 'S9' depends on axioms: [sorryAx]
   ```

   ```lean
   -- B.lean
   import A

   theorem usesS9 (_ : S9) : True := trivial

   #print axioms S9        -- 'S9' does not depend on any axioms
   #print axioms S9.mk     -- 'S9.mk' depends on axioms: [sorryAx]
   #print axioms usesS9    -- 'usesS9' does not depend on any axioms
   ```

   Run in the Nix shell as `lean -o A.olean A.lean`, then `LEAN_PATH=.
   lean B.lean`.  Only `A.lean` warns "declaration uses `sorry`", so a
   reader of `B` sees neither a warning nor an axiom.
+  **Could it hide a proof of `False`?**  Not that we have found.  What
   it hides is a dependence that passes through an inductive type's name,
   such as a statement about `S9`.  A proof that uses an axiom's content
   has to build or take apart a value with a constructor or a recursor,
   and in every case seen those constants' own entries were right, since
   their types mention the fields directly.  This is an argument, not a
   proof; until upstream fixes the cache, `#print axioms` on an imported
   declaration is not evidence that it is free of `sorry`.
+  **Measured at Mathlib scale**.  Over the 771,129 constants of `import
   Mathlib`, `collectAxioms` gives 1,837 an incomplete axiom set, 550 of
   them Mathlib's, and 532 Mathlib constants would get the wrong tier.  It
   never reports an axiom that is not there.  At the pin the axiom it omits
   is always `propext`, `Quot.sound` or `Classical.choice`, never `sorryAx`
   or a compiler axiom.  The 383 places where an omission starts are 267
   constructors, 107 inductive types and 9 definitions; the one definition
   examined, `Mathlib.Tactic.Ring.Common.ExBaseNat.evalPos._unsafe_rec`, is
   the companion of a `partial def` in a mutual block, and its safety is
   `partial` (LF-3).  The atlas's report,
   [`reports/atlas-mathlib-v4.33.1-0df444a.md`][report], has the numbers.
+  **Upstream**.  Lean issue [lean4#15226] (opened 2026-09-19 by someone
   outside this project, open on 2026-10-08), with the mechanism, the
   reproduction for `Classical.choice`, and the versions affected (v4.30.0
   on).  A maintainer called the inconsistency "not nice" but "arguably
   neither result is wrong".  Pull request [lean4#15385] (open) treats each
   inductive block as one unit and says that cycles of `unsafe` and
   `partial` definitions stay out of its scope, which is where the 9
   definitions above fall.  This project has filed nothing upstream; the
   `sorry` case and the Mathlib-scale counts are not in the issue.
+  **What the project does**.  The atlas computes exact axiom sets by
   reachability over the edges `collectAxioms` follows, records in
   `lean_omits` what Lean leaves out, and stops if Lean ever reports an
   axiom the graph does not reach ([`../atlas/README.md`][atlas-readme]).
   `make atlas` checks the corpus's axioms, which `#print axioms`
   printed, against the exact sets; none of the twelve entries is
   affected.  When the pin moves, compare the count of nonempty
   `lean_omits` with this one.

## LF-2: nothing safe rests on an unsafe axiom, and nothing on `sorryAx`

+  **Severity**.  Checked.
+  **Found**.  2026-10-08, from the atlas's exact axiom sets at Lean
   v4.33.1 and Mathlib v4.33.1, over all 771,129 constants of `import
   Mathlib`.
+  **What was asked**.  The compiler's axiom `lcProof : ∀ {α : Prop}, α`
   proves anything, and 242 constants depend on it.  Can a theorem, or
   any declaration the kernel treats as safe, reach it or another axiom
   outside the standard three?
+  **The answer**.  No.  Every constant that depends on one of the eight
   `unsafe` compiler axioms (`lcProof`, `lcCast`, `lcAny`, `lcErased`,
   `lcUnreachable`, `lcVoid`, `isScalarObj`, `Quot.lcInv`) is itself
   `unsafe`: 241 definitions and the axioms themselves, among them
   Mathlib's 41 (`Real.instRepr`, `Part.unwrap`, `Quot.unquot` and the
   floating-point arithmetic of `Mathlib.Data.FP.Basic`).  No theorem is
   T3.  The only safe T3 constants are `sorryAx`, `Lean.trustCompiler`,
   `Lean.ofReduceBool`, `Lean.ofReduceNat`, and the opaque
   `Lean.reduceBool` and `Lean.reduceNat`, the native-reduction family.
   `sorryAx` has no dependent but itself, and no `native_decide` axiom
   exists.
+  **To rerun**.  `make atlas`, then filter the records on `tier`,
   `unsafe` and `axioms`.

## LF-3: the kernel's safety separation holds, and `_unsafe_rec` is `partial`

+  **Severity**.  Checked, with a correction to the project's documents.
+  **Found**.  2026-10-08, by `atlas/probes/Safety.lean`
   ([`../atlas/README.md`][atlas-readme], "Probes") at Lean v4.33.1 and
   Mathlib v4.33.1, over all 771,129 constants of `import Mathlib`.
+  **What was asked**.  The kernel checks a declaration once, when it is
   added; a module that imports an `.olean` does not check its
   declarations again.  A safe declaration may use only safe ones, and a
   `partial` one no `unsafe` one, or a proof could rest on code the kernel
   never checked for termination or at all.  Does every constant of the
   environment respect that?
+  **The answer**.  Yes.  By `DefinitionVal.safety` (and
   `ConstantInfo.isUnsafe` for the other kinds), 766,708 constants are
   safe, 3,707 `partial` and 714 `unsafe`.  None of the 770,415 safe or
   `partial` ones uses, in its type, its value or its constructors, a
   constant it may not.  As a control, the same scan counts 141,293 uses
   of safe constants by `partial` ones and 15,635 by `unsafe` ones, so it
   does see edges between safeties.
+  **The correction**.  All 3,649 `_unsafe_rec` companions have safety
   `partial`, not `unsafe`, so `ConstantInfo.isUnsafe` does not flag them.
   The atlas's documents said `unsafe` and were corrected; the gap
   catalog's `trust-escape-hatches` entry on `main` still says that a
   `partial def` gets "an `unsafe` companion".  The atlas's `partial`
   field is unaffected: it flags the `opaque` constant, by its companion.

[#11]: https://github.com/formalverification/lean2agda/issues/11
[#71]: https://github.com/formalverification/lean2agda/pull/71
[lean4#15226]: https://github.com/leanprover/lean4/issues/15226
[lean4#15385]: https://github.com/leanprover/lean4/pull/15385
[catalog-hatches]: https://github.com/formalverification/lean2agda/blob/main/docs/foundations/gap-catalog.md#trust-escape-hatches
[report]: reports/atlas-mathlib-v4.33.1-0df444a.md
[atlas-readme]: ../atlas/README.md
