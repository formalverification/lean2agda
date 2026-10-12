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

The entries so far are as follows; none is S0.  A session that adds an
entry adds its row here too.

| Entry | Severity | Finding |
| --- | --- | --- |
| LF-1 | S1 | `#print axioms` omits axioms behind an inductive type, `sorryAx` included |
| LF-2 | Checked | in `import Mathlib`, nothing safe rests on an unsafe axiom, and nothing on `sorryAx` |
| LF-3 | Checked | the kernel's safety separation holds over `import Mathlib`; `_unsafe_rec` is `partial` |
| LF-4 | S2 | `proofIrrelevance := false` leaves proofs in arguments identified |
| LF-5 | S2 | injectivity of constructors of parameterized or indexed types rests, unseen, on UIP on a universe |
| LF-6 | Checked | `Nat.gcd`'s equation needs no K-like reduction at the pin |
| LF-7 | S2 | two Mathlib lemmas rely, unseen, on K-like reduction and structure eta |
| LF-8 | Checked | flattening closure groups with `Array.append` does not copy every prefix |
| LF-9 | S2 | hygienic names printed without escapes fail the name-literal decoder |
| LF-10 | S2 | `by_cases` makes a proof classical without saying so, `Finset.image` among them |

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

## LF-2: in `import Mathlib`, nothing safe rests on an unsafe axiom, and nothing on `sorryAx`

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

## LF-3: the kernel's safety separation holds over `import Mathlib`, and `_unsafe_rec` is `partial`

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
   The atlas's documents said `unsafe` and were corrected, and so was
   the gap catalog's `trust-escape-hatches` entry, which said that a
   `partial def` gets "an `unsafe` companion".  The atlas's `partial`
   field is unaffected: it flags the `opaque` constant, by its companion.

## LF-4: `proofIrrelevance := false` leaves proofs in arguments identified

+  **Severity**.  S2.  The elaborator is not trusted; the kernel has
   definitional proof irrelevance as a rule of Lean's theory and is
   unaffected.
+  **Found**.  2026-10-08, by issue [#7]'s session (pull request [#70]),
   looking for a way to make Lean say where a proof relies on
   definitional proof irrelevance; reproduced by issue [#11]'s session at
   Lean v4.33.1.
+  **What**.  `Meta.Config.proofIrrelevance`, documented as "Enables proof
   irrelevance at `isDefEq`", does not switch it off everywhere.  With it
   `false`, `isDefEq h₁ h₂` fails for two proofs of one proposition, but
   `isDefEq (h₁ = h₁) (h₁ = h₂)` still succeeds, since proofs in argument
   position are compared another way.  The file that shows it, run with
   `lake env lean` (it needs only `import Lean`), is as follows:

   ```lean
   import Lean
   open Lean Meta

   #eval show MetaM Unit from do
     withLocalDeclD `p (mkSort Level.zero) fun p => do
     withLocalDeclD `h1 p fun h1 => do
     withLocalDeclD `h2 p fun h2 => do
       let e1 ← mkEq h1 h1
       let e2 ← mkEq h1 h2
       for pi in [true, false] do
         withConfig (fun c => { c with proofIrrelevance := pi }) do
           IO.println s!"{pi}: {← isDefEq h1 h2} {← isDefEq e1 e2}"
   ```

   It printed `true: true true` and `false: false true`.
+  **What it means here**.  The elaborator cannot be made to report where
   a proof needs definitional proof irrelevance, which Agda lacks without
   `--prop`; the normalizer, Lean4Less, which makes those uses explicit
   casts, is the instrument instead (the gap catalog's
   `proof-irrelevance` entry).
+  **Upstream**.  Not reported; no Lean issue was searched for yet.

## LF-5: injectivity of constructors of parameterized or indexed types rests, unseen, on uniqueness of identity proofs on a universe

+  **Severity**.  S2.  It is Lean's design, not a defect: Lean's theory
   proves uniqueness of identity proofs for every type, by definitional
   proof irrelevance and K-like reduction (the gap catalog's
   [`k-and-uip`][catalog-k] entry).  What the measurement adds is that
   `#print axioms` cannot show it, and how far it reaches.
+  **Found**.  2026-10-08, by issue [#8]'s session (pull request [#69]);
   issue [#7]'s session met the same use in its gcd entries.  Reproduced
   by issue [#11]'s session at Lean v4.33.1 and Mathlib v4.33.1.
+  **What**.  `eq_of_heq : a ≍ a' → a = a'` is proved, with
   `pp.proofs true`, as follows:

   ```lean
   fun {α} {a a'} h =>
     have this := fun x x_1 x_2 x_3 h₁ =>
       HEq.rec (motive := fun x_4 x_5 x_6 => ∀ (h : x = x_4), cast h x_2 = x_5) (fun x_4 => rfl) h₁;
     this α α a a' h rfl
   ```

   The case `fun x_4 => rfl` has type `∀ (h : x = x), cast h x_2 = x_2`
   for `x : Sort u`, and `cast h x_2` reduces to `x_2` only by K-like
   reduction of `Eq.rec` on the variable `h`: uniqueness of identity
   proofs on a universe (Coq's `JMeq_eq`), which univalence refutes,
   since `not` gives `Bool = Bool` a second proof.  The kernel accepts
   `example (α : Sort u) (h : α = α) (a : α) : cast h a = a := rfl`, and
   its diagnostics count `[(Eq.rec, 2)]` when it re-checks `eq_of_heq`
   (the `#k_reductions` probe of the `querying-a-pinned-mathlib` skill;
   its two controls each count one `Eq.rec`, so the count alone is not
   conclusive, and the term above is the evidence).  Yet `#print axioms`
   says "does not depend on any axioms" for `eq_of_heq`,
   `Option.some.inj` and `Nat.noConfusion`.
+  **How far it reaches**.  Every `<T>.noConfusion` definition, the
   source of constructor injectivity and disjointness, was scanned for a
   use of `eq_of_heq` in its value.  Under `import Lean`, 667 of 2,610
   use it; under `import Mathlib`, 2,412 of 4,494.  In both, those are
   exactly the inductive types with parameters or indices
   (`numParams + numIndices > 0`).  So every injectivity or
   disjointness proof for a constructor of such a type goes through it.
+  **What it means here**.  A mechanical translation of such a lemma to
   profile CC or CU has no counterpart for `eq_of_heq`, which needs K;
   the hand translations avoid it by proving injectivity with Agda's own
   pattern matching ([#69]'s `corpus/multiset-map-map/notes.md` prints
   the probe).  The atlas's tiers do not see it, since it is no axiom.
+  **Upstream**.  Known design; nothing to report.

## LF-6: `Nat.gcd`'s defining equation needs no K-like reduction at the pin

+  **Severity**.  Checked, with a correction to a claim from outside the
   project that the roadmap relied on.
+  **Found**.  2026-10-08, by issue [#7]'s session (pull request [#70]), at
   Lean v4.33.1.
+  **What was asked**.  Lean4Less's README says that "for the equation
   `Nat.gcd (succ y) x = Nat.gcd (mod x (succ y)) (succ y)` to hold
   definitionally in Lean, the typechecker must use K-like reduction", and
   gives that as its reason for not treating `Nat.gcd` as a kernel primitive.
   Issue [#7] expected the corpus entry `nat-gcd-succ` to show it.
+  **The answer**.  Not at the pin.  The paragraph dates from 2025-01-12, when
   Lean's release was v4.15.0.  Since v4.27.0 a definition by well-founded
   recursion on a `Nat` measure compiles through the fuel-based
   `WellFounded.Nat.fix`, while the source of `Nat.gcd` is unchanged.  At
   v4.33.1 the kernel rejects `Eq.refl` as a proof of the equation over
   variables, so the equation is not definitional at all, and `Nat.gcd_succ` is
   a theorem through `funext`.  Re-checking the 192 theorems and definitions of
   its closure in the kernel with its diagnostics on, only `eq_of_heq` (LF-5)
   reduces a recursor that admits K-like reduction; computing `Nat.gcd._unary`
   on literals reduces only `Nat.rec`, `Bool.rec`, `Decidable.rec` and
   `PSigma.rec`.  A hand-written copy compiled the old way,
   `WellFounded.fix Nat.lt_wfRel.wf` on the same step, satisfies the equation
   by `Eq.refl` with one `Acc.rec` step and no reduction of a recursor that
   admits K.  Its two sides then differ only in their `Acc` arguments, so proof
   irrelevance identifies them, not K-like reduction.  The README's conclusion,
   that the equation fails in Lean⁻, which has neither rule, does not depend on
   which of the two Lean used.
+  **To rerun**.  The two probes printed in the Remarks of
   [`corpus/nat-gcd-succ/notes.md`][gcd-succ-notes].
+  **Upstream**.  Nothing filed.  Whether Lean4Less still refuses `Nat.gcd` at
   the pin needs a run of Lean4Less, whose own toolchain (v4.28.0-rc1) is past
   v4.27.0; that is M3-1 ([#26]).

## LF-7: two Mathlib lemmas rely, unseen, on K-like reduction and structure eta

+  **Severity**.  S2.  Both are rules of Lean's theory, not defects; LF-5 makes
   the same point for `eq_of_heq`, and this entry adds two uses written in
   Mathlib's own proofs.
+  **Found**.  2026-10-08, by issue [#7]'s session (pull request [#70]), at
   Lean v4.33.1 and Mathlib v4.33.1, in the closure of `Lists'.Subset.refl`.
+  **What**.  `#print axioms` prints `[propext]` for each of the following two
   lemmas of `Mathlib.SetTheory.Lists`, and neither rule shows:
   +  `Lists'.of_toList` generalizes the index of `Lists' α true` to
      `∀ b (h : true = b)`, because Lean's `induction` tactic needs a variable
      index, and transports along `h`.  In the cases `nil` and `cons'`,
      `h : true = true` is a bound variable, and the kernel reduces the
      transport only by K-like reduction.  Its diagnostics count ten `Eq.rec`
      reductions while re-checking the lemma; the term is the evidence, since
      the count includes ordinary reductions too.
   +  `Lists'.to_ofList` holds at `head :: tail` only because the kernel
      expands the variable `head : Lists α` into `⟨head.1, head.2⟩`, structure
      eta for `Sigma`.  The elaborator's checker rejects it with
      `etaStruct := .none`, as it rejects a control (`x = ⟨x.1, x.2⟩ := rfl` on
      a sigma type); no other theorem or definition in the closures of [#7]'s
      four corpus entries needs it.
+  **Could it prove `False`?**  No.  Uniqueness of identity proofs on `Bool` is
   harmless, since `Bool` has decidable equality and Hedberg's theorem proves
   it without K, and structure eta is consistent.  What it affects is
   translation: under `--cubical-compatible` the corpus's Agda replaces the
   K-like step by agda-stdlib's `Decidable⇒UIP` for `Bool`, and Agda's records
   have eta.
+  **To rerun**.  The notes of `lists-subset-refl`
   ([`corpus/lists-subset-refl/notes.md`][lists-notes]), which use the probes
   printed in `nat-gcd-succ`'s notes.
+  **Upstream**.  Known design; nothing to report.

## LF-8: flattening closure groups does not copy every prefix

+  **Severity**.  Checked.
+  **Found**.  2026-10-11, while evaluating Copilot's performance comment
   on pull request [#73], at Lean v4.33.1.
+  **What was asked**.  Does
   `closure.groups.foldl (· ++ ·) #[]` copy the accumulated array for
   every group, making `Closure.declarations` quadratic?
+  **The answer**.  No.  The pinned [`Array.append` implementation][array-basic]
   folds `push` over its second argument.  Lean's `Array.flatten` uses
   the same outer fold as this API.  The native code for
   `Closure.declarations` passes its accumulator to `Array.append`
   without retaining a reference to the old prefix, allowing the
   runtime to update the buffer in place.  The pinned
   [`lean_array_push` implementation][array-runtime] checks exclusive
   ownership (a single reference) and reuses the buffer when capacity
   remains.  On expansion, `lean_copy_expand_array` grows capacity to
   `(capacity + 1) * 2`.  This geometric growth gives amortized linear
   work in the group and declaration counts; the measurements below
   check the practical behavior rather than establish that bound.
+  **Evidence**.  The native [`FlattenBenchmark.lean`][flatten-benchmark]
   calls the actual API from the compiled `Core/Types` object, using
   one declaration per group and checking its names and order against
   an explicit nested `push` loop.  Thirty-two flattenings per size
   gave the following averages in milliseconds in run `flatten-r1`:

   | Groups | Current API | Explicit pushes |
   | --- | --- | --- |
   | 25,000 | 0.266 | 0.300 |
   | 50,000 | 0.714 | 0.801 |
   | 100,000 | 1.105 | 1.267 |
   | 200,000 | 2.140 | 2.972 |
   | 400,000 | 4.768 | 5.723 |

   Runs `flatten-r2` and `flatten-r3` repeated the same sizes.  Increasing
   the group count from 100,000 to 400,000 multiplied the API's time by
   4.31, 4.66, and 5.36 in the three runs.  These are scaling checks,
   rather than a performance guarantee for the whole translator.
   A positive control retains every prefix and therefore forces
   copy-on-write: at 2,000, 4,000, and 8,000 groups, run `flatten-r1`
   took 7.55, 60.32, and 1,799.15 ms.  Retaining those prefixes also
   increases memory pressure, so these timings are a copying control,
   rather than a measurement of a quadratic exponent.  Timing varies
   with machine load; the first run's one-, five-, and fifteen-minute
   system load averages were 4.02, 7.16, and 5.94.
+  **To rerun**.  From the repository root inside `nix develop`, use the
   following commands.  Compilation and execution write only to `/tmp`;
   the probe is a manual benchmark, outside the CI timing gates.

   ```sh
   make lean-build
   cd translator
   lake env lean scripts/FlattenBenchmark.lean -c /tmp/FlattenBenchmark.c
   lake env leanc -O3 -o /tmp/FlattenBenchmark /tmp/FlattenBenchmark.c \
     .lake/build/ir/Lean2Agda/Core/Types.c.o.export
   /tmp/FlattenBenchmark
   ```

+  **Upstream**.  Documented behavior; no defect to report.  The review
   comment was answered with the pinned source and measurements.
+  **What the project does**.  Keep the current flattening implementation.
   Recheck the source and scaling when the Lean pin changes.

## LF-9: hygienic printed names fail the name-literal decoder

+  **Severity**.  S2.  The printer documents that not every name round-trips.
+  **Found**.  2026-10-11, while checking the atlas population for [#16],
   at Lean v4.33.1 and Mathlib v4.33.1 (`0df444a`).
+  **What**.  `Name.toString` disables string-component escaping for names
   with macro scopes.  The atlas therefore prints names such as
   `Aesop.option._@.Aesop.Check.1191392668._hygCtx._hyg.3` without quoting
   `_@`.  `Syntax.decodeNameLit` rejects that printed form.  Even when
   decoding succeeds, arbitrary names need not retain their component
   structure: a macro-scoped string component containing a dot prints as
   multiple components.  Inaccessible names such as `x✝` can fail decoding
   as well.  These behaviors are in the pinned [name printer][name-printer].
+  **Evidence**.  The first atlas injectivity run stopped at the Aesop name
   above.  The atlas test now uses a structural fallback only for names
   satisfying `Name.hasMacroScopes`, followed by an exact printed-string
   check.  Run `naming-atlas-probe-2026-10-11` compared that decoder with
   every original structured name in `import Mathlib`: all 771,129
   imported constants round-tripped at this pin.  This is a population
   result, not a general guarantee about the printed representation.
+  **To rerun**.  After `make lean-cache`, run the following in the Nix shell:

   ```sh
   cd translator
   lake exe naming-atlas-probe
   ```

   [`NamingAtlasProbe.lean`][name-probe] loads the environment as native
   code with imported initializers enabled.  An earlier `#eval` attempt
   printed the count but then encountered an invalid-environment-extension
   panic during elaboration; that attempt is not the successful run.
+  **Upstream**.  Documented behavior; no defect is alleged or reported.
+  **What the project does**.  Encode constructors directly in the pure
   naming core and store tagged components in reverse maps.  Rerun the
   original-name probe when the atlas pin changes.

## LF-10: `by_cases` makes a proof classical without saying so

+  **Severity**.  S2.  `#print axioms` reports the dependency correctly;
   what goes unseen is where it comes from, since nothing in the source
   names classical logic.
+  **Found**.  2026-10-11, by the first part of issue [#9]'s session, at
   Lean v4.33.1 and Mathlib v4.33.1, tracing where `Classical.choice`
   enters `Finset.card_image_of_injective`
   ([`corpus/finset-card-image/notes.md`][finset-notes]).
+  **What**.  Lean core's `by_cases h : e` expands to
   `open Classical in refine if h : e then ?pos else ?neg`
   (`src/Init/ByCases.lean` at v4.33.1).  When a `Decidable e` instance
   is in scope, the `if` uses it; when none is, it takes
   `Classical.propDecidable` and the proof becomes T2.  The same two
   proofs differ only in the instance in scope, as follows:

   ```lean
   import Init.Data.List.Perm

   theorem withInstance (n m : Nat) : n = m ∨ n ≠ m := by
     by_cases h : n = m
     · exact Or.inl h
     · exact Or.inr h

   theorem withoutInstance {α : Type} (a b : α) : a = b ∨ a ≠ b := by
     by_cases h : a = b
     · exact Or.inl h
     · exact Or.inr h

   #print axioms withInstance       -- does not depend on any axioms
   #print axioms withoutInstance    -- [propext, Classical.choice, Quot.sound]
   #print axioms List.perm_iff_count
   ```

   The last prints `[propext, Classical.choice, Quot.sound]`: core's
   `List.perm_iff_count` (`Init.Data.List.Perm`), stated under
   `[BEq α] [LawfulBEq α]`, splits with `by_cases h : b = a`, and no
   `Decidable (b = a)` instance is in scope there.
+  **How far it reaches**.  `List.Perm.dedup` proves its permutation
   through `List.perm_iff_count`, and `Multiset.dedup` is a lift whose
   respect proof is `List.Perm.dedup`.  So `#print axioms Finset.image`
   prints `Classical.choice`, though the function `image` computes uses
   only its `DecidableEq` argument, and every Mathlib statement that
   mentions `Finset.image` mentions a T2 constant.  A classification of
   statements by the axioms of the constants they mention would call all
   of them classical.
+  **What it means here**.  Issue [#39]'s detection has to look for
   classical instance terms in statements, not at axiom sets, and the
   atlas could record, for a T2 definition, whether `Classical.choice`
   reaches its value only through proofs.  The corpus entry proves the
   lemmas involved constructively, splitting on the given decidable
   equality.
+  **Upstream**.  Documented behavior; nothing to report.

[#7]: https://github.com/formalverification/lean2agda/issues/7
[#8]: https://github.com/formalverification/lean2agda/issues/8
[#69]: https://github.com/formalverification/lean2agda/pull/69
[#70]: https://github.com/formalverification/lean2agda/pull/70
[#11]: https://github.com/formalverification/lean2agda/issues/11
[#26]: https://github.com/formalverification/lean2agda/issues/26
[#71]: https://github.com/formalverification/lean2agda/pull/71
[lean4#15226]: https://github.com/leanprover/lean4/issues/15226
[lean4#15385]: https://github.com/leanprover/lean4/pull/15385
[catalog-hatches]: https://github.com/formalverification/lean2agda/blob/main/docs/foundations/gap-catalog.md#trust-escape-hatches
[catalog-k]: https://github.com/formalverification/lean2agda/blob/main/docs/foundations/gap-catalog.md#k-and-uip
[report]: reports/atlas-mathlib-v4.33.1-0df444a.md
[atlas-readme]: ../atlas/README.md
[gcd-succ-notes]: ../corpus/nat-gcd-succ/notes.md
[lists-notes]: ../corpus/lists-subset-refl/notes.md
[#73]: https://github.com/formalverification/lean2agda/pull/73
[array-basic]: https://github.com/leanprover/lean4/blob/v4.33.1/src/Init/Data/Array/Basic.lean#L1475-L1490
[array-runtime]: https://github.com/leanprover/lean4/blob/v4.33.1/src/runtime/object.cpp#L2719-L2764
[flatten-benchmark]: ../translator/scripts/FlattenBenchmark.lean
[#16]: https://github.com/formalverification/lean2agda/issues/16
[name-printer]: https://github.com/leanprover/lean4/blob/v4.33.1/src/Init/Data/ToString/Name.lean
[name-probe]: ../translator/scripts/NamingAtlasProbe.lean
[#9]: https://github.com/formalverification/lean2agda/issues/9
[#39]: https://github.com/formalverification/lean2agda/issues/39
[finset-notes]: ../corpus/finset-card-image/notes.md
