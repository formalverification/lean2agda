<!-- File: atlas/README.md -->

# atlas

Per-declaration records of what each constant of the pinned Mathlib
depends on: the axioms (`propext`, `Quot.sound`, `Classical.choice`,
`Lean.ofReduceBool`, `sorryAx`), computability, and, once the translator
exists, the kernel features its typing used, the universe-elaboration
result, and its acceptance under each target profile.

Issue M1-11 produces the first version (axioms only) with a Lean program
in `../translator/` and a stdlib-only Python report in
`../scripts/python/`; issue M4-1 defines the full schema in `SCHEMA.md`.
Records are NDJSON, one object per declaration, named by Mathlib
revision.  Large record files are regenerable and are not committed;
the reports derived from them are, under `../docs/reports/`.

`make atlas` will produce the records for the pinned revision.
