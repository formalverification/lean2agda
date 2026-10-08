<!-- File: docs/pinning.md -->

# Pinning

Every tool the project depends on is pinned, and every pin moves only
on purpose.  This document says what is pinned, where each pin lives,
the command that changes it, how to check the change, and what must
move with it; it ends with the upgrade procedure.  Issue M1-3 ([#3])
wrote it; issue M5-7 ([#49]) rehearses the procedure and corrects it.

## Summary

| Pin | Pinned to | Lives in | Changed by |
| --- | --- | --- | --- |
| Lean | v4.33.1 (`819816b`) | `lean-toolchain` | editing that file |
| Mathlib | tag v4.33.1 (`0df444a`) | `translator/lakefile.toml`, `translator/lake-manifest.json` | editing the tag, then `lake update --keep-toolchain` |
| lean4export | tag v4.33.0 (`15f6055`) | `translator/lakefile.toml`, `translator/lake-manifest.json` | editing the tag, then `lake update --keep-toolchain` |
| Lean4Less | not pinned (M3-1, [#26]) | | |
| Agda, agda-stdlib, cubical | 2.8.0, 2.3, 0.9 | `flake.lock` (nixpkgs `a7868a7`) | `nix flake update nixpkgs` |
| lean4-nix | `e04ca09` | `flake.lock` | `nix flake update lean4-nix` |
| github-project engine | `20a191a` | `flake.lock` | `nix flake update github-project` |

Every `lean` and `lake` command below runs inside the Nix shell: as
`nix develop --command ...`, or after `nix develop`.  The host may have
its own `elan` with other toolchains, and a version string printed
outside the shell proves nothing about the pin.

## The toolchain each Lean tool requires

Lean's `.olean` files are specific to one Lean release, so every Lean
tool the pipeline runs either uses the pinned release or runs as a
separate program at its own.  On 2026-10-05 the tools required the
following:

| Tool | Revision | Its `lean-toolchain` |
| --- | --- | --- |
| lean2agda (`translator/`) | this repository | `leanprover/lean4:v4.33.1` |
| Mathlib | tag v4.33.1, `0df444a` (2026-08-21) | `leanprover/lean4:v4.33.1` |
| lean4export | tag v4.33.0, `15f6055` (2026-08-10) | `leanprover/lean4:v4.33.0` |
| Lean4Less | `main`, `5b66bbc` (2026-02-11) | `leanprover/lean4:v4.28.0-rc1` |

Lean4Less is five minor releases behind the pin, and on a release
candidate; see its section below for what that means for M3-1.

## Lean

+  **Pinned**.  Lean v4.33.1, released 2026-08-21, commit `819816b`.
+  **Where**.  `lean-toolchain` at the repository root, one line,
   `leanprover/lean4:v4.33.1`.  Three readers take the version from it,
   as follows:
   +  the flake: `lean4-nix.readToolchainFile ./lean-toolchain` puts that
      release (the official prebuilt binaries, which lean4-nix fetches
      rather than builds; `lean --version` in the shell names commit
      `819816b`, the release tag's) into the default and `.#lean` shells;
   +  `elan`, for an editor or a terminal outside the shell, since the
      file is in elan's format;
   +  Mathlib's cache tool and Mathlib's post-update hook, through
      `translator/lean-toolchain`, a symlink to the root file.  The cache
      tool compares the text of `./lean-toolchain` with Mathlib's own and
      exits when they differ, so the Lake package needs the file beside
      it; the symlink keeps one source of truth, and `make doctor` fails
      if the two ever differ (for instance after a checkout that does not
      preserve symlinks).
+  **Change**.  Edit the root `lean-toolchain`, never the symlink, and
   only to a version for which lean4-nix carries a manifest and Mathlib a
   release tag.  lean4-nix carries one manifest per stable Lean release
   (no release candidates) and lags Lean by about one release; Mathlib
   tags `vX.Y.Z` when Lean X.Y.Z is released.
+  **Verify**.  `nix develop --command lean --version` prints the new
   version and `nix develop --command make doctor` passes.
+  **Moves with it**.  The Mathlib tag (always the same version), the
   lean4export tag, and lean4-nix first if its locked revision has no
   manifest for the new version.
+  **Never let Lake move it**.  Run every `lake update` with
   `--keep-toolchain`.  Without the flag, when a dependency's
   `lean-toolchain` names a newer Lean, Lake rewrites the root package's
   file to match, writes through the symlink, prints "no Elan detected;
   you will need to manually restart Lake" and exits with status 4
   (measured 2026-10-05 with lean4export v4.34.0 as the dependency).  If
   lean4-nix has no manifest for the version Lake wrote, every shell
   then fails to evaluate, the `.#agda` shell included, with
   `error: attribute '"v4.34.0"' missing`.

## Mathlib

+  **Pinned**.  The release tag v4.33.1, commit `0df444a`, whose own
   `lean-toolchain` names Lean v4.33.1.
+  **Where**.  `translator/lakefile.toml` names the tag (`rev =
   "v4.33.1"`); `translator/lake-manifest.json` records the commit it
   resolved to and the commits of Mathlib's own dependencies (batteries,
   Qq, aesop, proofwidgets, importGraph, LeanSearchClient, plausible,
   Cli), which Lake takes from Mathlib's manifest at that tag.  Never
   edit the manifest by hand.
+  **Change**.  Edit the tag, then run `lake update --keep-toolchain` in
   `translator/`, which rewrites the manifest.  Mathlib's `post_update`
   hook then runs `lake exe cache get` by itself (unless
   `MATHLIB_NO_CACHE_ON_UPDATE=1` is set); run `make lean-cache` anyway,
   which is quick when nothing is missing and resumes a fetch that was
   interrupted.
+  **Verify**.  `make lean-cache`, `make lean-build` and `make lean-smoke`
   in the shell.  `make lean-smoke` first runs `lake build --no-build
   Mathlib`, which compiles nothing and exits with status 3 if any module
   of Mathlib or its dependencies is out of date by Lake's traces (what
   a missing file, or a cache built by another Lean, looks like), then
   loads Mathlib and prints the axioms of one of its theorems.  The cache
   tool itself refuses to run if the manifest pins one of Mathlib's
   dependencies at a revision other than Mathlib's own, since its hashes
   would then be wrong.
+  **Moves with it**.  Lean, lean4export, and everything computed from
   Mathlib: the atlas (M1-11, [#11]), the exported terms of the corpus
   entries and the axioms and tiers `corpus/manifest.json` records for
   every entry, the translator's golden tests, and the provenance record
   of any generated library.

Mathlib's prebuilt `.olean` files come from `lake exe cache get` (or
`make lean-cache`); nothing in the project builds Mathlib from source.
The files live in two places, as follows:

+  `translator/.lake/packages/mathlib/.lake/build/` holds Mathlib's
   unpacked `.olean` files, and `translator/.lake/packages/<name>/.lake/build/`
   those of each of its dependencies; `.lake/` is gitignored;
+  `~/.cache/mathlib/` (or `$MATHLIB_CACHE_DIR`, or
   `$XDG_CACHE_HOME/mathlib`) holds the compressed downloads, shared by
   every checkout and worktree on the machine, so a second worktree
   unpacks them without downloading again.

At tag v4.33.1 the cache was 8,690 files, 440 MB compressed; unpacked,
the build directories under `translator/.lake/packages/` took 7.1 GB,
and Mathlib's git clone another 525 MB (measured 2026-10-05).  The
cache tool downloads with `curl` and unpacks with the `leantar` binary
that ships with the Lean release.  It runs `curl --version` first and
fails without curl, even when nothing is missing, so the Lean shells
carry it.

## lean4export

+  **Pinned**.  The release tag v4.33.0, commit `15f6055`; lean4export
   has no v4.33.1 tag.  Lake builds it with the pinned Lean v4.33.1,
   without a warning about its own `lean-toolchain` (which names
   v4.33.0).  The first line of every export records the exporter's
   version (3.1.0 at this tag) and the version and commit of the Lean
   that ran it.
+  **Where**.  `translator/lakefile.toml` and
   `translator/lake-manifest.json`, as for Mathlib.
+  **Change**.  Edit the tag, then `lake update --keep-toolchain` in
   `translator/`.  Choose the newest tag whose version does not exceed
   the pinned Lean's and whose minor version matches it.
+  **Verify**.  `lake build lean4export` in `translator/`, then export a
   known declaration, as follows:

   ```sh
   lake exe lean4export Mathlib.Data.Finset.Card -- Finset.card_image_of_injective > out.ndjson
   ```
+  **Moves with it**.  Lean's minor version.  The exported terms of the
   corpus entries are re-exported, and compared, whenever the tag moves:
   v4.34.0, for one, stops exporting `partial` declarations unless
   `--export-unsafe` is given.

## Lean4Less

+  **Not pinned yet**; the pin lands with M3-1 ([#26]), and this section
   will then say where it lives.
+  **Requirement**.  On 2026-10-05 the default branch, `main` (last
   commit `5b66bbc`, 2026-02-11), named `leanprover/lean4:v4.28.0-rc1`.
   The most recently pushed branch, `claude-stable` (2026-06-17), named
   v4.18.0-rc1.
+  **The skew**.  The pin is v4.33.1, five minor releases ahead.
   lean4-nix carries no release candidates, so the flake cannot fetch
   v4.28.0-rc1; its nearest manifest is v4.28.0, and Mathlib has tags
   v4.28.0 and v4.28.1.  Lean4Less has no license
   ([`licensing.md`](licensing.md)), so it is used as an external tool
   and never copied.  M3-1 decides how to bridge the skew: a Mathlib
   revision both tools support, a fork at the pinned Lean if Lean4Less's
   authors grant a license (M1-14), or the translator running inside
   Lean4Less's process.

## Agda, agda-stdlib and cubical

+  **Pinned**.  Agda 2.8.0, agda-stdlib 2.3 and the cubical library 0.9,
   all from nixpkgs `a7868a7` (2026-10-03).
+  **Where**.  `flake.lock`, root input `nixpkgs`.  `flake.nix` takes
   `pkgs.agda`, `agdaPackages.standard-library` and
   `agdaPackages.cubical` from one package set, so the three move
   together; Python 3 (3.14.7) comes from the same input.
+  **Change**.  `nix flake update nixpkgs`.
+  **Verify**.  `nix develop --command make doctor` prints the new Agda
   version, and its two probes check that both libraries resolve;
   `make corpus-check` re-checks every translated corpus entry.
+  **Moves with it**.  The version numbers written in the README,
   `CLAUDE.md`, `flake.nix`'s header comment and the roadmap's Working
   agreements, and the `OPTIONS` pragmas of the corpus if a flag changes
   meaning.  The first CI run on `main` after the move pushes the new
   closure to the Cachix cache.

## lean4-nix

+  **Pinned**.  `e04ca09` (2026-08-27), which on 2026-10-05 was also
   lean4-nix's newest commit; its newest manifest is v4.33.1.
+  **Where**.  `flake.lock`, input `lean4-nix`.
+  **Change**.  `nix flake update lean4-nix`.
+  **Verify**.  Before: the manifest list names the version you want,
   `gh api repos/lenianiva/lean4-nix/contents/manifests --jq '.[].name'`.
   After: `nix develop --command lean --version`.
+  **Moves with it**.  Nothing by itself; it moves first whenever
   `lean-toolchain` is to name a Lean newer than its locked manifests.

## The github-project engine

+  **Pinned**.  `20a191a` (2026-08-19).
+  **Where**.  `flake.lock`, input `github-project`.  CI's `checks` job
   reads the same revision from `flake.lock` to fetch its own engine
   checkout, so it follows the lock without a second edit.
+  **Change**.  `nix flake update github-project`.
+  **Verify**.  `make engine-mode` prints `path`, and `make lint` and
   `make update-check` pass.
+  **Moves with it**.  Nothing.

## Upgrade procedure

The Lean side moves as one change, in the following order; the Agda
side (`nix flake update nixpkgs`) and the engine move independently,
each in a pull request of its own.

1.  Choose the target Lean version X.Y.Z: the newest stable release for
    which lean4-nix has `manifests/vX.Y.Z.nix`, Mathlib has the tag
    `vX.Y.Z`, and lean4export has a tag of the same minor version, as
    follows:

    ```sh
    gh api repos/lenianiva/lean4-nix/contents/manifests --jq '.[].name'
    gh api 'repos/leanprover-community/mathlib4/contents/lean-toolchain?ref=vX.Y.Z' --jq .content | base64 -d
    gh api 'repos/leanprover/lean4export/tags?per_page=30' --jq '.[].name'
    gh api repos/Deducteam/Lean4Less/contents/lean-toolchain --jq .content | base64 -d
    ```

    Record what you found, and the date, in this document.
2.  If `flake.lock`'s lean4-nix predates that manifest, run
    `nix flake update lean4-nix`.
3.  Edit `lean-toolchain` to `leanprover/lean4:vX.Y.Z`, and check that
    `nix develop --command lean --version` prints X.Y.Z.
4.  Edit the `rev` of Mathlib and of lean4export in
    `translator/lakefile.toml`.
5.  In `translator/`, run `nix develop --command lake update
    --keep-toolchain`.  It rewrites `lake-manifest.json`, and Mathlib's
    hook fetches the cache.
6.  Run `nix develop --command make lean-cache`.  If the fetch was
    interrupted, run it again; it resumes.  If the cache tool reports
    that a file is missing for the tag, stop: do not let Lake build
    Mathlib.
7.  Run `make lean-build`, `make lean-smoke` and `make doctor` in the
    shell, and the lean4export check above.
8.  Check that `git diff lean-toolchain` shows only your edit, so Lake
    did not write through the symlink.  (That `lake-manifest.json` pins
    Mathlib's dependencies at the commits of Mathlib's own manifest needs
    no check of yours: the cache tool refuses to run otherwise.)
9.  Regenerate what is computed from Mathlib: the atlas, the corpus's
    exported terms, the translator's golden tests; compare the atlas with
    the previous one.
10. Update this document's pins, tables and dates, and commit
    `lean-toolchain`, `flake.lock` (if it moved), `translator/lakefile.toml`
    and `translator/lake-manifest.json` together.

[#3]: https://github.com/formalverification/lean2agda/issues/3
[#11]: https://github.com/formalverification/lean2agda/issues/11
[#26]: https://github.com/formalverification/lean2agda/issues/26
[#49]: https://github.com/formalverification/lean2agda/issues/49
