<!-- File: docs/foundations/README.md -->

# Foundations

Notes on what Lean's type theory has that Agda's does not, and what the
translation does about each difference.  The documents, written and
planned, are as follows:

+  [`gap-catalog.md`](gap-catalog.md) (issue M1-5, written 2026-10-07):
   one entry per kernel feature, with the Lean rule, Agda's status
   under each target profile, the translation strategy, the
   predecessors' treatment, and references; the Agda and Lean probe
   files that settled its claims are under [`probes/`](probes/);
+  `gap-report-corpus.md` (issue M1-10): what the hand translations
   needed, feature by feature;
+  `faithfulness-init-std.md` (issue M3-10): what fraction of `Init` and
   `Std` translates under each profile, and why the rest does not;
+  the operation table for `Nat` and `String` literals (issue M3-6), the
   UIP-on-types study (issue M6-5), and the choice-under-univalence
   study (issue M6-3).
