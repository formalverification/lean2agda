<!-- File: corpus/README.md -->

# corpus

Mathlib declarations translated into Agda by hand, before any translator
existed, so that the project learns what translation involves and the
translator has an oracle to reproduce.  Issue M1-6 fixes the layout and
selects the first twelve entries; issues M1-7, M1-8 and M1-9 write them.

The intended layout, one directory per entry, is as follows:

+  `<id>/lean/`: the Lean statement and its elaborated kernel term as
   exported by lean4export;
+  `<id>/agda/`: the hand-written idiomatic Agda, each file declaring its
   flags in an `OPTIONS` pragma (`--safe --cubical-compatible` by
   default; `--safe --cubical --guardedness` for cubical variants, since
   the cubical library's flags make `--guardedness` infective);
+  `<id>/notes.md`: what the translation needed, cross-referenced to the
   gap catalog in `../docs/foundations/`;
+  `manifest.json`: id, Lean name, Mathlib module, axiom tier, features
   exercised, flags, status.

`make corpus-check` will type-check every entry under its declared flags.
