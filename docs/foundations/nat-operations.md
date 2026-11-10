<!-- File: docs/foundations/nat-operations.md -->

# The operation table

Lean's kernel computes fifteen operations on natural number literals with
an arbitrary-precision library instead of unfolding their definitions
(the gap catalog's `literals` entry, [catalog-literals]).  The profile U
scaffold emitted Lean's compiled definitions of those operations, which
Agda computes in unary, and whose normal forms, stuck on a variable,
Agda's positivity check expanded until it ran out of memory: the field of
`ByteArray.IsValidUTF8` once took Agda to 23 GB, and with the checker's
heap bound the type was refused wherever it appeared, with 70 values of
`Init.Core`'s closure behind it ([`recursors.md`][recursors-positivity]).
This note maps each accelerated operation to an Agda definition, states
which of Lean's definitional equations each one keeps, gives its cost on
large numerals and what the safe profiles need of it, and records the
measurements of issue [#31] that chose the table, together with the
design for `String` and `Char` and the cost of proofs by `decide`.

Everything here was measured at the project's pins ([`../pinning.md`][pinning]):
Lean v4.33.1 and Agda 2.8.0, on 2026-11-09 and 2026-11-10.  The probes
named below are under [`probes/`][probes]; each Agda probe records its
outcome on its first line, and the Lean probe `NatOps.lean` records its
output at its end.  The translator emits the table under profile U by
default (`--arithmetic agda`); `--arithmetic lean` emits Lean's
definitions, the control of every measurement below
([`Arithmetic.lean`][arithmetic-lean]).

## Lean's side

+  **The fifteen operations**.  `reduce_nat` in the kernel's type checker
   ([kernel-type-checker], lines 702 to 733) computes `Nat.succ` and the
   fourteen binary operations `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.pow`,
   `Nat.gcd`, `Nat.mod`, `Nat.div`, `Nat.beq`, `Nat.ble`, `Nat.land`,
   `Nat.lor`, `Nat.xor`, `Nat.shiftLeft` and `Nat.shiftRight` when both
   arguments reduce to literals.  `whnf` tries it before it unfolds
   anything (line 765), while the lazy unfolding of a definitional
   equality check tries it only when neither side has a free variable
   (lines 1093 to 1099).  A result past `LEAN_NAT_MAX_SIZE` (128 MiB by
   default, line 36) is refused, and `Nat.pow` and `Nat.shiftLeft` refuse
   before computing one.  `Nat.log2`, which issue [#31] listed, is not
   among them: it is `Nat.rec` on a fuel argument (`NatOps.lean`).
+  **The definitions**.  Lean's compiled definitions take one of three
   shapes, as follows (`NatOps.lean` prints each):
   +  structural recursion through `Nat.brecOn`: `Nat.add`, `Nat.sub`,
      `Nat.mul`, `Nat.pow`, `Nat.shiftLeft` and `Nat.shiftRight` on their
      second argument, `Nat.beq` and `Nat.ble` on their first, matching
      on both;
   +  structural recursion on a fuel argument: `Nat.div` is
      `if 0 < y then Nat.div.go y _ (x + 1) x _ else 0`, and `Nat.mod`
      matches on its first argument and then calls
      `Nat.modCore`, which is `Nat.modCore.go` with fuel likewise;
   +  well-founded recursion through `WellFounded.Nat.fix`, which at the
      pin is itself recursion on fuel (`Nat.eager (n + 1)`): `Nat.gcd`,
      through `Nat.gcd._unary`, and `Nat.bitwise`, of which `Nat.land`,
      `Nat.lor` and `Nat.xor` are instances (`Nat.bitwise and` and so on).
+  **Lean's equations**.  Which equations about these operations hold by
   conversion on variables is the kernel's question, not the
   elaborator's, since `Nat.div`, `Nat.gcd` and `Nat.bitwise` are
   irreducible to the elaborator: `NatOps.lean` asks `Lean.Kernel.isDefEq`
   for each, in a local context holding the variables, 54 equations in
   all.  The ones that hold are, by operation, as follows:
   +  `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.pow`, `Nat.shiftLeft` and
      `Nat.shiftRight`: their two defining equations, at zero and at a
      successor of the second argument (`Nat.sub n (succ m) = pred
      (Nat.sub n m)`, `Nat.mul n (succ m) = Nat.add (Nat.mul n m) n`), and
      none at the first argument (`0 + n = n` fails);
   +  `Nat.beq` and `Nat.ble`: their four and three defining equations,
      and `Nat.ble 3 (m + 4) = true`, a numeral below an offset; not
      `Nat.beq n n = true`;
   +  `Nat.div`: `n / 0 = 0`, `0 / (m + 1) = 0` and `3 / (m + 4) = 0`;
      not `0 / m = 0`, `n / 1 = n`, nor `Nat.div_eq`;
   +  `Nat.mod`: `0 % m = 0`, `(n + 1) % 0 = n + 1`, `3 % (m + 4) = 3`, and
      its unfolding at a successor, `(n + 1) % m = if m ≤ n + 1 then
      Nat.modCore (n + 1) m else n + 1`; not `n % 0 = n`, `n % 1 = 0`, nor
      `Nat.mod_eq`;
   +  `Nat.gcd`: `Nat.gcd 0 n = n` only; not `Nat.gcd (m + 1) 0 = m + 1`,
      and not its defining equation at a successor, whose two sides
      unfold with different fuel (the gap catalog says why);
   +  `Nat.land`, `Nat.lor` and `Nat.xor` at a zero first argument, and
      `Nat.bitwise f 0 m = if f false true then m else 0` for every `f`;
      none at a zero second argument;
   +  `Nat.succ`: a literal is its `succ` form, `n + 1 = succ n` and
      `n + 3 = succ (succ (succ n))`.

## The rule: the recursive core, not the wrapper

The table replaces only the recursive core of each operation and keeps
Lean's non-recursive wrappers around it: `Nat.div`, `Nat.mod`,
`Nat.modCore`, `Nat.land`, `Nat.lor`, `Nat.xor` and `Nat.gcd` stay Lean's
definitions, and `Nat.div.go`, `Nat.modCore.go` and `Nat.bitwise` are
replaced, with the operations that are recursive themselves and
`Nat.pred`, which `Nat.sub`'s rewrite rules need by its clauses.  Two
things follow, as follows:

+  every one of Lean's equations about a wrapper still holds by
   conversion, since the wrapper unfolds as in Lean (`(n + 1) % m`, `3 %
   (m + 4) = 3` through `Nat.decLe` and the builtin `_<_`); and
+  a replaced core stuck on a variable is one small neutral term, a
   builtin applied to a variable, where Lean's `brecOn` unfolds into a
   recursor with its `below` table in every branch, the normal form the
   positivity check expanded.

What a replacement gives up is the replaced definition's own equations:
the unfolding of the core to Lean's compiled term (an `eq_def` lemma), and
for a core whose Agda definition is not Lean's clauses, the clauses
themselves.  The next section says which, and the section after it counts
who uses them.

## The table

Each row is settled by a probe: `P29NatOperations` defines every row's
Agda side under `--safe --cubical-compatible`, the flags of profiles K
and CC, and proves each of Lean's equations that the kernel accepts by
`refl`, then computes on numerals past 2^64; it checks in 0.19 s.  The
fixture `TranslatorTests.Input.Arithmetic` states the same equations as
Lean theorems by `rfl`, and the harness checks the translator's tree of
them under both settings (the goldens `arithmetic` and `arithmetic-lean`).
"Builtin" names the Agda definition, written as `Agda.Builtin.Nat` writes
it, that the row binds to one of Agda's `BUILTIN` pragmas; Agda computes it
on numerals with the host's integers and by its clauses otherwise.

| Operation | Lean's definition | Agda's, under profile U | Lean's equations kept by conversion | On numerals past 2^64 |
| --- | --- | --- | --- | --- |
| `Nat.succ` | a constructor | the constructor of `BUILTIN NATURAL` | all: a literal is its `succ` form | at once |
| `Nat.add n m` | `brecOn` on `m` | `m + n`, the builtin `NATPLUS` | both | at once |
| `Nat.sub n m` | `brecOn` on `m`, `pred` at a successor | `n - m`, the builtin `NATMINUS` (monus), and three rewrite rules | `sub n 0 = n` by conversion; `sub n (succ m) = pred (sub n m)` by the rules (probes `P30`, `P31`) | at once |
| `Nat.pred` | a match | Lean's two clauses, so that a rule headed by it can fire | both | at once on a numeral |
| `Nat.mul n m` | `brecOn` on `m` | `m * n`, the builtin `NATTIMES` | both | at once |
| `Nat.pow m n` | `brecOn` on `n` | Lean's two clauses over the builtin product | both | one product per unit of `n`: 64 for 2 ^ 64 |
| `Nat.beq` | `brecOn` on the first | the builtin `NATEQUALS` itself, its clauses Lean's | all four | at once |
| `Nat.ble n m` | `brecOn` on `n` | `n < m + 1`, the builtin `NATLESS` | all three, and a numeral below an offset | at once |
| `Nat.div` | `if 0 < y then Nat.div.go …` | Lean's | all of the wrapper's | at once, through the core |
| `Nat.div.go y _ fuel x _` | `brecOn` on the fuel | `div-helper 0 (y - 1) x (y - 1)`, the builtin `NATDIVSUCAUX`, the fuel and the proofs ignored | none of its own two: its equation at a successor of the fuel is lost | at once |
| `Nat.mod`, `Nat.modCore` | a match, then `if m ≤ n then Nat.modCore …`; `if 0 < y then Nat.modCore.go …` | Lean's | all of the wrappers' | at once, through the core |
| `Nat.modCore.go y _ fuel x _` | `brecOn` on the fuel | `mod-helper 0 (y - 1) x (y - 1)`, the builtin `NATMODSUCAUX` | none of its own two, as for `Nat.div.go` | at once |
| `Nat.gcd` | `Nat.gcd._unary`, through `WellFounded.Nat.fix` with fuel | Lean's | all: Lean's definition, unchanged | one step of Euclid's algorithm per remainder: `gcd 1000000007 998244353` by `decide` in 0.5 s |
| `Nat.land`, `Nat.lor`, `Nat.xor` | `Nat.bitwise and`, `or`, `bne` | Lean's | all three at a zero first argument | through `Nat.bitwise` |
| `Nat.bitwise f n m` | `Nat.bitwise._unary`, through `WellFounded.Nat.fix` | by fuel `n + 1`, each step a builtin division and remainder by 2, the recursive result used once | for a given `f`, those of `land`, `lor` and `xor`; for an unknown `f`, `bitwise f 0 m = if f false true then m else 0` is lost | one step per bit: 64 for 64-bit numbers |
| `Nat.shiftLeft n m` | `brecOn` on `m` | Lean's two clauses over the builtin product | both | one product per unit of `m` |
| `Nat.shiftRight n m` | `brecOn` on `m` | Lean's two clauses over the builtin division | both | one division per unit of `m` |

Three remarks on the rows, as follows:

+  **Arguments swapped**.  Agda's builtin `_+_` and `_*_` recur on their
   first argument and Lean's on their second, and Agda checks a `BUILTIN`
   binding by its clauses, so `Nat.add` is the builtin with its arguments
   swapped.  Lean's equations then hold by conversion (`Nat.add n (succ
   m)` is `succ m + n`, which is `succ (m + n)`), and so does the
   equation of `Nat.mul` at a successor, whose right side is a sum in
   Lean's order: `Nat.add (Nat.mul n m) n` is `n + m * n`, the builtin's
   own clause.  `Nat.pow`, `Nat.shiftLeft` and `Nat.shiftRight` keep their
   equations because their clauses call the builtins exactly as Lean's
   right sides do (`2 * n` is `n *ᴮ 2`, not `2 *ᴮ n`, which differs on a
   variable).
+  **No row is both fast and faithful for `Nat.sub`**.  A definition that
   keeps `Nat.sub n (succ m) = pred (Nat.sub n m)` by conversion recurses
   on `m`, which Agda unfolds once per unit of a numeral, and the builtin
   monus, which computes `2^128 - 2^64` at once, matches on its second
   argument and then its first, so that on a variable `n` the left side is
   stuck (probe `P30`, `UnequalTerms`).  Profile U has `--rewriting`
   (issue [#21]), and the table states the lost equation as a rewrite rule
   proved by induction.  One rule is not enough: the monus has two clauses
   of its own that Lean's `Nat.sub` lacks, `0 - succ m = 0` and `succ n -
   succ m = n - m`, which fire before the rule can, so that where a Lean
   proof expects `pred (0 - n)` Agda has `0`, and `Nat.zero_sub` was refused
   with the one rule.  Two more rules close the two critical pairs,
   `pred (0 - m) = 0` and `pred (succ n - m) = n - m`, with `Nat.pred`
   given by its clauses so that a rule headed by it can fire; Agda's
   `--local-confluence-check` accepts the three declared together and
   refuses the first alone (`RewriteNonConfluent`, the pair at `succ n -
   succ m`), probe `P31`, 0.07 s.  The equation then holds on variables,
   and numerals still compute at once, since Agda reduces a builtin on
   numerals before any rule applies.  `--safe` refuses `--rewriting`, so
   profiles K and CC cannot (below).
+  **`Nat.bitwise` by fuel**.  Lean's `Nat.bitwise` computes its
   recursive result `r` once and returns `r + r + 1` or `r + r`; printed
   in Agda, whose `let` is substitution, `r` occurs twice in each branch,
   and evaluating a builtin sum of two copies doubles the work at every
   bit, 2^64 times over for 64-bit numbers.  The table's definition
   applies `2 *ᴮ r` once, and its base cases pick `m` or `0` by a helper
   on `f false true`, which is why its equation for an unknown `f` is
   Lean's only up to that helper.

The helpers' identifiers end in `-builtin`, `-pick`, `-bit`, `-odd`,
`-go` or `-succ`, a hyphen no `agdaIdent` produces, and each lives in its
home module (`Nat`'s builtins in `Init.Prelude`, `Nat.bitwise`'s helpers
beside it in `Init.Data.Nat.Bitwise.Basic`), where it comes before its
first user; other modules name it by that module's path.  `Bool` carries
`BUILTIN BOOL`, `FALSE` and `TRUE`, which `NATEQUALS` and `NATLESS`
need.  The translator refuses to emit a row whose Lean definition no
longer has the arity its clauses bind (`tableEntry?`), since the clauses
were written against the pin's definitions.

## What the table gives up, and who uses it

(See also [#26], [#27] and [#30].)

The table gives up four definitional equations: `Nat.sub`'s at a
successor without the rules, the fuel equations of `Nat.div.go` and
`Nat.modCore.go`, and `Nat.bitwise`'s at a zero first argument for an
unknown `f`.  A Lean term that relies on one by conversion is refused by
Agda where the table is used, and in profiles K and CC each such use
becomes a propositional step, the problem issue [#30] solves for the
quotient's computation rules.  Two measurements bound how many terms
that is, as follows.

+  **Lean's kernel, over all of `Init`**.  Re-checking every theorem and
   safe definition of the modules under `Init` (63,034 of them, none
   rejected, 91 s; probe `NatOpsUses.lean`) with the kernel's diagnostics
   on, as LF-12 of
   [`lean-findings.md`][lean-findings] validated for the quotient, counts
   for each operation the constants whose check unfolded it.  `whnf`
   tries the arbitrary-precision library first, so an unfolding is a use
   on an argument that is not a numeral, or a comparison of two open
   terms; it is an upper bound on the uses of the operation's equations,
   and it does not say which equation.  Besides each operation's own
   equation lemmas, the counts are as follows:

   | Operation | Constants of `Init` whose check unfolds it | Theorems among them | Equation the table gives up |
   | --- | --- | --- | --- |
   | `Nat.sub` | 663 | 615 | at a successor, in K and CC only |
   | `Nat.div.go` | 53 | 52 | at a successor of the fuel |
   | `Nat.modCore.go` | 4 | 3 | at a successor of the fuel |
   | `Nat.bitwise` | 167 | 167 | at zero, for an unknown `f` |
   | `Nat.add` | 2,646 | 2,205 | none |
   | `Nat.ble` | 431 | 419 | none |
   | `Nat.beq` | 331 | 311 | none |
   | `Nat.pow` | 250 | 240 | none |
   | `Nat.mul` | 178 | 160 | none |
   | `Nat.shiftRight` | 97 | 93 | none |
   | `Nat.shiftLeft` | 28 | 25 | none |

   In `Init.Core`'s closure the only constants that unfold `Nat.sub` are
   `Nat.sub_le` and `Nat.succ_sub_succ_eq_sub`, exactly the two that Agda
   refuses there without the rules, and those that unfold
   `Nat.modCore.go` are `Nat.modCoreGo_lt`, which the table's
   `Nat.modCore.go` refuses, and `Nat.modCore_lt`, which it checks (it
   compares the results of `go`, and the table's ignores the proofs whose
   comparison refused it before: a refusal of [#27]'s gone).  The users
   of `Nat.div.go` beyond its own lemmas are the signed integers'
   division lemmas (`Int8.div_zero` and the other fixed widths,
   `Int.ediv_neg`), `Nat.testBit_bitwise`, `Nat.log2_def` and
   `Nat.sqrt_isSqrt`; those of `Nat.bitwise` are in `Init.Data.BitVec`,
   `Init.Data.UInt`, `Init.Data.SInt` and `Init.Data.String.Decode`.
+  **Agda, on the closures checked**.  The checker's listings name the
   values the table costs, against the same closure under
   `--arithmetic lean`: `Nat.modCoreGo_lt` in every closure that holds
   it, `Nat.modCore.go.eq_1` and `Nat.div.go.eq_1` with the private
   `fuel_congr._f` of each wherever `Init.Data.Nat.Div.Basic` is
   reached, and the fixture's `bitwise_zero_left`; nothing else.  It
   gains `Nat.modCore_lt` everywhere.

The checker's fallback met the first of these, in a way that mattered:
when Agda refuses `Nat.modCoreGo_lt`, its message names three theorems
(`Nat.le_of_ble_eq_true` and two of its kin), the fallback unfolds them
one by one, in vain, and before issue [#31] they stayed transparent.
`Nat.decLe`'s proofs then sat in the normal form of every later field
that compares numerals, and those proofs recur through `brecOn` on a
numeral while matching on a variable, the exponential shape the table
removes from the operations: `ByteArray.IsValidUTF8` exhausted the heap
again, after its operations had been replaced.  Postulating
`Nat.modCoreGo_lt` by hand made it check in 4 Agda runs, 7.8 s and 272
MiB; the checker now puts a theorem back in its opaque block once its
unfolding proves in vain (`scaffold_check.py`, `reverted`), which every
listing's "in vain" count already reported.

## `Nat.sub`: four candidates

(See also [#21] and [#30].)

Under profile U the row of `Nat.sub` has four candidates: Lean's
definition (unary on numerals, every equation kept), the builtin monus
(fast, the equation at a successor lost), the monus with the one rule for
that equation, and the monus with the three confluent rules, the table's.
Each was checked on the same closures, the trees of `Init.Core`,
`Init.Data.Nat.Gcd` and the fixture `Arithmetic`, the other variants made
from the emitted tree by changing the rules' pragma or by putting back
Lean's `Nat.sub` and `Nat.pred` and dropping the rules:

| Closure, values refused beyond the table's | No rule | One rule | Lean's `Nat.sub` | The three rules |
| --- | --- | --- | --- | --- |
| fixture `Arithmetic` | 6: the fixture's `sub_succ`, `zero_sub_succ`, `succ_sub_succ`; `Nat.sub_le`, `Nat.sub_succ`, `Nat.succ_sub_succ_eq_sub` | 2: `zero_sub_succ`, `succ_sub_succ` | none | none |
| `Init.Data.Nat.Gcd` | 5: `Nat.sub_le` and its private `_f`, `Nat.sub_succ`, `Nat.succ_sub_succ_eq_sub`, `Nat.zero_sub` | 1: `Nat.zero_sub` | none | none |
| `Init.Core` | 2: `Nat.sub_le`, `Nat.succ_sub_succ_eq_sub` | none | none | none |
| Agda's time, the three closures | 99.5 s, 290.8 s, 341.4 s | 83.6 s, 250.9 s, 338.0 s | 80.0 s, 233.9 s, 336.8 s | 81.1 s, 255.7 s, 380.9 s |

The times are each check's sum over its Agda runs (`-j 6`, the table's
`Init.Core` run `-j 8`, at load averages near 1 to 2, 2026-11-10); the
candidates differ by the passes the extra refusals cost, not by Agda's
work on `Nat.sub`.  Lean's definition refuses nothing more, but it is
unary on numerals: `2^128 - 2^64` by `rfl` exhausts the heap under it
(the section on `decide`), against 0.4 s for the monus.  One rule leaves
the two critical pairs, which `Nat.zero_sub` meets in practice.  The
three rules refuse nothing the others check and compute at once.

The three rules are the table's choice under profile U.  Profiles K and
CC take the monus without them, and each of its users pays a
propositional step there (the upper bound above, 663 constants of
`Init`), which issue [#33] needs from [#30]'s machinery.

## `Nat.gcd`

(See also [#26].)

Lean's `Nat.gcd` needs nothing of its own in the table.  It is
`Nat.gcd._unary`, well-founded recursion through `WellFounded.Nat.fix`,
which at the pin is recursion on a fuel `Nat.eager (m + 1)`: once
`Nat.modCore.go` is the builtin, each step is one builtin remainder and
one step of the fuel, which Agda takes off a numeral at once, and the
corpus's `Nat.gcd 1000000007 998244353 = 1` by `decide` checks in 0.5 s
(the fixture `Numerals`).  Lean's definition is unchanged, so every one of
its equations that the kernel accepts holds in Agda too, which is only
`Nat.gcd 0 n = n`; the equation at a successor holds in neither, since its
two sides unfold with different fuel, and `Nat.gcd_succ` is a theorem in
both.  The corpus notes' two seconds for the same `gcd` were their entry's
whole check, agda-stdlib's imports mostly; the scaffold's cost was Lean's
unary `Nat.modCore.go`, which the table removes.  Whether Lean4Less still
refuses `Nat.gcd` at the pin needs a run of Lean4Less, which is issue
[#26]'s; the finding is recorded there.

## The measurements

(See also [#19], [#22] and [#84].)

+  **`ByteArray.IsValidUTF8`**.  The type's closure alone (342
   constants), as one module before issue [#22] merged and with the
   checker that keeps in-vain unfoldings, checked by `--types-only` in one
   Agda run of 0.8 s and 137 MiB with the operations replaced by hand,
   against 77 s and 8,486 MiB, the heap bound, for the control, which
   refuses the type.  With the translator's table and the current
   checkers the full closure, as the tree of two modules, checks in 7
   Agda runs and 11.3 s, its largest Agda process at 311 MiB: 311 of 311
   declarations and 38 of 38 data types and records, refused values
   `eq_of_heq` ([#26]'s) and `Nat.modCoreGo_lt`; the control takes 96.8 s,
   8,498 MiB against the bound, and refuses the type (2026-11-10).
+  **`Init.Core`'s closure**, as the tree of modules, every value
   printed, with `-j 8` for the table and `-j 4` for the control, at load
   averages near 2 (2026-11-10):

   | `Init.Core`'s closure | Declarations | Values | Checked | Refused | Behind a refused type | Types refused | Unfolded | Agda runs | Time | Largest peak |
   | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
   | `--arithmetic lean` | 1,963 | 1,660 | 1,570 | 16 | 74 | 2 | 5, none in vain | 30 | 303.1 s (293 s wall) | 8,496 MiB, the bound |
   | the table | 1,972 | 1,660 | 1,635 | 21 | 4 | 1 | 8, three in vain | 37 | 380.9 s (369 s wall) | 2,291 MiB |

   The nine declarations more are the table's six builtin helpers and
   `Nat.sub`'s three rules.
   The 70 values behind `ByteArray.IsValidUTF8` check, but five that the
   control never reached are refused: `String.decEq`, its
   `_proof_2` and `String.ofByteArray.injEq`, which compare two proofs of
   one proposition ([#27]'s), and `String.noConfusion` and
   `String.ofByteArray.noConfusion`, which need `String.rec` to compute
   while `String` is a postulate (the section on `String`, below).  With
   `Nat.modCoreGo_lt` refused and `Nat.modCore_lt` checked, that makes the
   21; the 4 behind a refused type are `apply_eqRec` and the three behind
   it, as before.  The single-module scaffold of the code before issue
   [#22] gave the same events, declaration for declaration, in 1,326 s
   and 761 s.
+  **`Init.Data.Nat.Gcd`'s closure**: 808 constants, every declaration of
   the module a root, printed in 2 s into 9 modules of 3.3 MB, without
   `ByteArray.IsValidUTF8`.  Under the table 808 of 808 declarations and
   47 of 47 data types and records check, in 94 Agda runs over 5 passes
   and 256 s (258 s wall, `-j 6`), the largest Agda process at 618 MiB;
   under Lean's definitions 799 of 799 and 47 of 47, in 13 runs and 38 s
   (`-j 4`), at 610 MiB.  The table refuses five values that Lean's
   definitions check, the fuel cores' own lemmas (`Nat.div.go.eq_1`,
   `Nat.modCore.go.eq_1`, `Nat.modCoreGo_lt` and the two private
   `fuel_congr._f`), and checks `Nat.modCore_lt`, which they refuse;
   `dif_pos`, `dif_neg` and `eq_of_heq` are refused both ways.  The time is
   the fallback's: each of the five refusals names `Nat.decLe`'s proofs,
   and the driver tries them, in vain, over four more passes of the tree.
   With one rule for `Nat.sub` the table also refused `Nat.zero_sub`, which
   the two rules that make the set confluent restore.
+  **`Init.Data.String.Basic`'s closure**: 4,935 constants, printed in
   129 to 136 s into 281 modules of 994 MB, both settings, since the tree
   names every constant of another module by its path.  Ten modules
   exceed 10 MB, the largest 200 MB, each a single theorem whose proof
   prints that large (`Init.Data.Array.Extract` and
   `Init.Data.Array.Bootstrap`); a module is never cut inside an item, so
   no heap bound lets Agda check those values, and a full check of the
   closure is a measured ceiling, not a result; the size of such proofs is
   [#44]'s.  What the positivity check
   sees is measured by `agda_check.py --types-only`, which keeps the
   data types and records, their recursors and the definitions they
   mention, every theorem postulated (`-j 4`, 2026-11-10):

   | `Init.Data.String.Basic`, types only | Declarations checked | Data types and records | Recursors defined | Agda runs | Time | Peak |
   | --- | --- | --- | --- | --- | --- | --- |
   | `--arithmetic lean` | 442 of 471 | 109 of 116 | 111 of 118 | 283 | 283 s (231 s wall) | 8,497 MiB, the bound |
   | the table | 466 of 466 | 116 of 116 | 118 of 118 | 282 | 210 s (151 s wall) | 3,747 MiB |

   Under Lean's definitions `ByteArray.IsValidUTF8` exhausts the heap,
   and `String` with its constructor, recursor and projections, and the
   rest of 28 declarations, are dropped behind it; under the table every
   type checks, and the one value refused in both is `eq_of_heq`
   ([#26]'s).

## `decide`

The corpus has few proofs that evaluate large terms, and the two
closures have none on large numerals: the values of `Init.Core`'s closure
that decide by evaluation (`of_decide_eq_true` or `_false`) are
`instLawfulBEq`, `instLawfulBEqBool` and `of_toBoolUsing_eq_true` and
`_false`, about `Bool`, and those of `Init.Data.Nat.Gcd`'s are
`Nat.zero_sub`, `Nat.le_zero_eq`, `Nat.mod_one` and `not_true_eq_false`,
about small numerals; all of them check under the table.  The gap
catalog's examples (`probes/lean/DefEq.lean`) are in the fixture
`Numerals`, with one theorem per accelerated operation on numerals past
2^64.  Each theorem was checked alone, against its closure's other
modules already checked (the loop's final tree, its interfaces built),
under a time bound of 300 s and a heap bound of 8G, on 2026-11-10:

| Theorem of `Numerals` | Lean's proof | The table | `--arithmetic lean` |
| --- | --- | --- | --- |
| `succ_big`: `Nat.succ (2^64 - 1) = 2^64` | `rfl` | checks, 0.4 s | checks, 0.3 s |
| `add_big`: `2^64 + 1` | `rfl` | checks, 0.4 s | checks, 0.5 s |
| `sub_big`: `2^128 - 2^64` | `rfl` | checks, 0.4 s | heap exhausted after 162 s |
| `mul_big`: `1000000007 * 998244353` | `rfl` | checks, 0.4 s | no answer in 300 s |
| `pow_big`: `2 ^ 128` | `rfl` | checks, 0.4 s | no answer in 300 s |
| `pow_two`: `2 ^ 64` | `decide` | checks, 0.5 s | no answer in 300 s |
| `beq_big`, `ble_big`: at 2^64 | `rfl` | checks, 0.5 s each | no answer in 300 s |
| `div_big`, `mod_big`: by `1000000007` | `rfl` | checks, 0.5 s each | no answer in 300 s |
| `gcd_small`: `Nat.gcd 12 18 = 6` | `rfl` | checks, 0.5 s | checks, 1.1 s |
| `gcd_primes`: `Nat.gcd 1000000007 998244353 = 1` | `decide` | checks, 0.5 s | no answer in 300 s |
| `land_big`, `lor_big`, `xor_big`: 64-bit numbers | `rfl` | checks, 0.4 to 0.5 s each | no answer in 300 s |
| `shiftLeft_big`, `shiftRight_big`: by 64 and 60 | `rfl` | checks, 0.5 s each | no answer in 300 s |

Every run under the table peaked at 89 to 91 MiB, which is Agda's cost of
loading the interfaces, so the computations themselves cost nothing that
shows; the control's runs that answered peaked at 96 to 99 MiB.  Under
Lean's definitions a numeral is unary wherever the recursion meets it:
`2^64 + 1` checks, since `Nat.add` recurs on its second argument, here 1,
while `2^128 - 2^64` runs out of heap building the unary 2^64 and the
rest give no answer within the bound.  The null results are the finding:
without the table, every one of these proofs whose recursion meets a
numeral of 10^9 or more fails, by the time bound or the heap bound.

## `String` and `Char`

(See also [#17] and [#27].)

Under profile U today `String` is a postulate bound to `BUILTIN STRING`,
so that Lean's string literals print as Agda's, and its constructor
`String.ofByteArray` and recursor `String.rec` are postulates too.
Lean's kernel expands a literal on demand to `String.ofList [c₁, …,
cₙ]`, and `String.ofList` is `String.ofByteArray (List.utf8Encode l) _`,
so the round trip `"ab" = String.ofList ['a', 'b']`, which Lean accepts by
`rfl`, is refused by Agda (`UnequalTerms "ab" != String:ofList …`), as is
`"a" = String.mk ['a']`; a character literal is `Char.ofNat 97`, an
application, and `'a'.toNat = 97` checks (a scratch probe of three
theorems, 379 constants, 2026-11-10).  `String.noConfusion` and
`String.ofByteArray.noConfusion`, newly reached in `Init.Core`'s closure,
are refused for the same reason.  There are two representations, as
follows.

+  **Agda's primitive strings**.  Keep `BUILTIN STRING` and make Lean's
   operations Agda's primitives: `String.ofList` as `primStringFromList`,
   which takes Agda's builtin list of builtin characters, so Lean's
   `List` bound to `BUILTIN LIST` and Lean's `Char` to `BUILTIN CHAR`.
   Agda binds `BUILTIN CHAR` only to a postulate (probe `P32CharRecord`,
   `BuiltinMustBePostulate`), while Lean's `Char` is a structure of a
   `UInt32` and a validity proof: `Char`, `Char.mk`, `Char.val` and
   `Char.rec` become postulates, with rewrite rules for what Lean's
   kernel computes (`Char.val (Char.ofNat n)`, `String.toByteArray
   (String.ofList l)`), each an equation Agda takes on trust.  It is fast
   and it is profile U's only: `--safe` refuses the postulates and the
   rules.
+  **Lean's structures**.  Emit `String` and `Char` as the records Lean
   declares and print a literal as the kernel expands it, `String.ofList`
   applied to a list of `Char.ofNat` applications, with no `BUILTIN
   STRING`.  The round trip then holds by `refl` (both sides are one
   term), `String.rec` and `String.noConfusion` compute, nothing is
   postulated, and the representation serves every profile.  Its costs
   are text and evaluation: `Init.Core`'s closure has 742 string literals
   (85 distinct, 4,150 characters in all) and `Init.Data.String.Basic`'s
   758 (53 distinct), which the sharing pass would print once each; and a
   decision on strings evaluates `List.utf8Encode` in Agda, through the
   table's builtins.  It needs the closure to count `String.ofList`,
   `Char.ofNat`, `List.cons` and `List.nil` as dependencies of every
   constant with a string literal, the printer to expand literals, and
   `Scaffold.lean` to stop treating `String` apart; the comparisons of
   `String`'s validity proofs (`String.decEq`) stay [#27]'s.

The second representation is the recommendation, for every profile: it
is the kernel's own semantics, and profiles K and CC have no other.  It
does not fit this pull request (it changes the closure, the printer, the
scaffold and every golden that holds a literal), so issue [#31] proposes
it as a follow-up; the primitive representation could return later as a
profile U option for speed.

## Profiles K and CC

(See also [#30] and [#33].)

Profiles K and CC are `--safe` ([`../adr/0001-translation-architecture.md`][adr],
section 4), which refuses `--rewriting`, and every row of the table is
safe Agda: `P29NatOperations` checks under `--safe
--cubical-compatible`, the flags of profile CC, whose definitions hold
under profile K's `--safe` as well.  Each row's definition for K and CC
is its profile U definition, with one difference: `Nat.sub` is the
monus without the rules, so its equation at a successor is lost there
with the fuel equations of `Nat.div.go` and `Nat.modCore.go` and
`Nat.bitwise`'s for an unknown `f`.  A use of one of those becomes a
propositional step, a cast by the equation, which the normalizer of issue
[#30] inserts for the quotient's rules; the counts above bound how many
there are in `Init`.  Profile CU, with `--cubical`, uses the same
builtins through `Agda.Builtin.Nat` (`P28CubicalLiterals`).

## Probes

+  `probes/lean/NatOps.lean`: Lean's definitions of the operations and
   the kernel's verdict on 54 equations on variables; run from
   `translator/` as `lake env lean ../docs/foundations/probes/lean/NatOps.lean`.
+  `probes/lean/NatOpsUses.lean`: the kernel's counters over every theorem
   and safe definition of `Init`, one line per constant that unfolds a
   replaced operation; run likewise, 91 s.
+  `P29NatOperations`, under `--safe --cubical-compatible`: every row's
   Agda definition, each equation the kernel accepts by `refl`, and
   computations on numerals past 2^64; accepted, 0.19 s.
+  `P30NatSubMonus`, the same flags: the monus against `Nat.sub`'s
   equation at a successor; rejected, `UnequalTerms`, the intended
   rejection.
+  `P31NatSubRewrite`, under profile U's `--type-in-type --rewriting` with
   `--local-confluence-check`: the equation as a rewrite rule proved by
   induction, with the two that make the rules confluent, `Nat.pred` by
   its clauses, the critical pairs by `refl`, and numerals; accepted,
   0.07 s.
+  `P32CharRecord`, under `--safe --cubical-compatible`: Lean's `Char` as a
   record under `BUILTIN CHAR`; rejected, `BuiltinMustBePostulate`, the
   intended rejection.
+  The fixtures `TranslatorTests.Input.Arithmetic` and `Numerals`, and the
   unit check `tests/Arithmetic.lean`, in the translator's harness.

## References

+  Issues and pull requests: [#17], [#19], [#21], [#22], [#26], [#27],
   [#30], [#31], [#33], [#44], [#84].
+  Lean's kernel: [kernel-type-checker], lines 36, 571, 702 to 733, 765
   and 1093 to 1099.
+  Agda's builtins: [agda-builtins], "Natural numbers", "Booleans",
   "Characters", "Strings", "Lists".
+  Code: [`Arithmetic.lean`][arithmetic-lean] (the table),
   [`Scaffold.lean`][scaffold-lean] (`tableItem`, `helperItem`),
   [`Modules.lean`][modules-lean] (the helpers' homes),
   [`scaffold_check.py`][scaffold-check] (`reverted`).

[#17]: https://github.com/formalverification/lean2agda/issues/17
[#19]: https://github.com/formalverification/lean2agda/issues/19
[#21]: https://github.com/formalverification/lean2agda/issues/21
[#22]: https://github.com/formalverification/lean2agda/issues/22
[#26]: https://github.com/formalverification/lean2agda/issues/26
[#27]: https://github.com/formalverification/lean2agda/issues/27
[#30]: https://github.com/formalverification/lean2agda/issues/30
[#31]: https://github.com/formalverification/lean2agda/issues/31
[#33]: https://github.com/formalverification/lean2agda/issues/33
[#44]: https://github.com/formalverification/lean2agda/issues/44
[#84]: https://github.com/formalverification/lean2agda/pull/84

[catalog-literals]: gap-catalog.md#literals
[recursors-positivity]: ../translator/recursors.md#agdas-positivity-check-and-leans-arithmetic
[pinning]: ../pinning.md
[probes]: probes/
[lean-findings]: ../lean-findings.md
[adr]: ../adr/0001-translation-architecture.md
[arithmetic-lean]: ../../translator/Lean2Agda/Core/Arithmetic.lean
[scaffold-lean]: ../../translator/Lean2Agda/Core/Scaffold.lean
[modules-lean]: ../../translator/Lean2Agda/Core/Modules.lean
[scaffold-check]: ../../scripts/python/scaffold_check.py
[kernel-type-checker]: https://github.com/leanprover/lean4/blob/v4.33.1/src/kernel/type_checker.cpp
[agda-builtins]: https://agda.readthedocs.io/en/v2.8.0/language/built-ins.html
