# File: flake.nix
#
# lean2agda development environment.  One `nix develop` provides everything
# the project needs; nothing is taken from the host system.
#
#   Lean      the toolchain named in ./lean-toolchain, fetched as the official
#             prebuilt release by lean4-nix (readToolchainFile; no source
#             build).  lean4-nix carries one manifest per stable Lean release
#             and lags Lean by about one release, so the pin here is the newest
#             version it knows; docs/pinning.md says how it moves with the
#             pinned Mathlib revision.  The Lean shells also carry curl,
#             which Mathlib's cache tool (`lake exe cache get`) runs to
#             download; without it the tool fails even when nothing is
#             missing.
#   Agda      Agda with agda-stdlib and the cubical library from nixpkgs
#             (2.8.0, 2.3 and 0.9 at the time of writing), registered
#             project-locally in $ROOT/.agda (gitignored) by the shellHook,
#             which points AGDA_DIR there, so the user's ~/.config/agda cannot
#             contribute, and installs an `agda` wrapper that passes the
#             project's --library-file to the shell's own Agda.  Optional
#             external libraries are registered when AGDA_UNIMATH_ROOT,
#             AGDA_TYPETOPOLOGY_ROOT or AGDA_ALGEBRAS_ROOT points at a checkout
#             containing an .agda-lib file.
#   Python    python3 from nixpkgs, standard library only (house style).
#   Engine    the github-project roadmap engine (gh-project-populate, -update,
#             -lint) as a pinned flake input; the Makefile finds it on PATH.
#
# Shells:  nix develop            everything (default)
#          nix develop .#agda     Agda and its libraries, without Lean
#          nix develop .#lean     the Lean toolchain, without Agda
#
# Every shell carries make, git and Python: the Agda shellHook finds $ROOT
# with git, the corpus checker and the planned output checker (M2-8) are
# Python scripts run through make, and Lake fetches its dependencies with git.
# Only the default shell carries the roadmap tools (gh, jq, the engine), so
# a broken or missing engine package cannot break the Agda and Lean shells.
#
# Pinning: flake.lock pins nixpkgs (Agda, Python, tools), lean4-nix (the Lean
# fetcher) and github-project (the engine).  Upgrade one input deliberately:
#   nix flake update nixpkgs        (or lean4-nix, or github-project)
{
  description = "lean2agda: a Lean 4 to Agda translator and the libraries it produces";

  # The organization's binary cache (shared with agda-native-air): prebuilt
  # Agda toolchains and library interfaces, so a fresh machine pulls instead
  # of building.  Nix asks once whether to trust the substituter.
  nixConfig = {
    extra-substituters = [ "https://formalverification.cachix.org" ];
    extra-trusted-public-keys = [ "formalverification.cachix.org-1:KG/AJuuli2F4/bA56rUYC9V8ZE/Zw6iZjxJEf40cQOo=" ];
  };

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    lean4-nix.url = "github:lenianiva/lean4-nix";
    github-project.url = "github:williamdemeo/github-project";
  };

  outputs = { self, nixpkgs, lean4-nix, github-project }:
    let
      # x86_64-darwin is absent on purpose: the pinned nixpkgs refuses to
      # evaluate for it ("Nixpkgs 26.11 has dropped support for
      # x86_64-darwin").
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ];

      # One package set per system, with the Lean overlay applied: after it,
      # pkgs.lean is the toolchain named in ./lean-toolchain.
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system:
        f {
          inherit system;
          pkgs = import nixpkgs {
            inherit system;
            overlays = [ (lean4-nix.readToolchainFile ./lean-toolchain) ];
          };
        });

      # Agda and its libraries must come from the same package set:
      # agdaPackages.* are built against pkgs.agda.
      agdaLibs = p: [ p.standard-library p.cubical ];
      mkAgdaEnv = pkgs: pkgs.agda.withPackages agdaLibs;

      # Project-local AGDA_DIR plus an `agda` wrapper.  AGDA_DIR is Agda's
      # configuration directory, so pointing it into the repository is what
      # keeps the user's ~/.config/agda out of the picture: both the
      # `libraries` file (every registered .agda-lib) and the `defaults` file
      # (the library names a file outside any .agda-lib project sees) are
      # written there on every shell entry.  The wrapper only passes
      # --library-file again on the command line (Agda's last flag wins) to
      # bypass the Nix wrapper's baked-in file, so that libraries registered
      # through the *_ROOT variables resolve too.  It deliberately does not
      # pass --library flags: those drop the current directory from the
      # include path, and a scratch file's module name then matches nothing.
      # The wrapper execs the shell's own Agda by its store path; it never
      # asks `command -v agda`.  That lookup names the wrapper itself when
      # the hook runs again in an entered shell (eval "$shellHook"), and
      # only the bare word `agda` when an agda function is defined (an
      # interactive `nix develop` sources ~/.bashrc before the hook).
      # Either way the wrapper would exec itself, and since every shell of
      # the checkout shares the file, `agda` would hang in all of them.
      # The heredoc lines sit at column 0 on purpose: Nix strips the common
      # indentation of this string, and the terminator must reach the shell
      # at column 0.
      mkAgdaShellSetup = pkgs: agdaEnv: ''
        ROOT="$PWD"
        if command -v git >/dev/null 2>&1 && git rev-parse --show-toplevel >/dev/null 2>&1; then
          ROOT="$(git rev-parse --show-toplevel)"
        fi
        export AGDA_DIR="$ROOT/.agda"
        mkdir -p "$AGDA_DIR/bin"
        {
          for f in ${pkgs.agdaPackages.standard-library}/*.agda-lib ${pkgs.agdaPackages.cubical}/*.agda-lib; do
            echo "$f"
          done
          for var in AGDA_UNIMATH_ROOT AGDA_TYPETOPOLOGY_ROOT AGDA_ALGEBRAS_ROOT; do
            root="''${!var:-}"
            if [ -n "$root" ]; then
              lib="$(ls "$root"/*.agda-lib 2>/dev/null | head -n 1)"
              if [ -n "$lib" ]; then
                echo "$lib"
              else
                echo "warning: $var=$root has no .agda-lib file; not registered" >&2
              fi
            fi
          done
        } > "$AGDA_DIR/libraries"
        : > "$AGDA_DIR/defaults"
        while IFS= read -r libfile; do
          name="$(sed -n 's/^name:[[:space:]]*//p' "$libfile" | head -n 1)"
          if [ -n "$name" ]; then
            echo "$name" >> "$AGDA_DIR/defaults"
          fi
        done < "$AGDA_DIR/libraries"
        cat > "$AGDA_DIR/bin/agda" <<EOF
#!/usr/bin/env bash
exec "${agdaEnv}/bin/agda" --library-file "$AGDA_DIR/libraries" "\$@"
EOF
        chmod +x "$AGDA_DIR/bin/agda"
        export PATH="$AGDA_DIR/bin:$PATH"
      '';

      banner = pkgs: withLean: withAgda: withRoadmap: ''
        echo ""
        echo "lean2agda dev shell"
        ${if withLean then ''echo "  Lean     : $(lean --version 2>/dev/null || echo unavailable)"'' else ""}
        ${if withAgda then ''echo "  Agda     : ${pkgs.agda.version}  (standard-library ${pkgs.agdaPackages.standard-library.version}, cubical ${pkgs.agdaPackages.cubical.version})"'' else ""}
        ${if withAgda then ''echo "  AGDA_DIR : $AGDA_DIR"'' else ""}
        echo "  Python   : ${pkgs.python3.version}"
        ${if withRoadmap then ''echo "  engine   : $(command -v gh-project-lint >/dev/null 2>&1 && echo on PATH || echo missing)"'' else ""}
        echo ""
      '';
    in
    {
      devShells = forAllSystems ({ pkgs, system }:
        let
          agdaEnv = mkAgdaEnv pkgs;
          engine = github-project.packages.${system}.gh-project-engine;
          build = [ pkgs.gnumake pkgs.git pkgs.python3 ];
          roadmap = [ pkgs.gh pkgs.jq engine ];
          # Lean and the curl that Mathlib's cache tool runs.  Only curl's
          # bin output: the default output would also put the headers of
          # curl and its libraries into the shell's environment.
          leanTools = [ pkgs.lean.lean-all pkgs.curl.bin ];
        in
        {
          default = pkgs.mkShell {
            name = "lean2agda-dev";
            packages = build ++ roadmap ++ [ agdaEnv ] ++ leanTools;
            LANG = "C.UTF-8";
            LC_ALL = "C.UTF-8";
            shellHook = mkAgdaShellSetup pkgs agdaEnv + banner pkgs true true true;
          };

          agda = pkgs.mkShell {
            name = "lean2agda-agda";
            packages = build ++ [ agdaEnv ];
            LANG = "C.UTF-8";
            LC_ALL = "C.UTF-8";
            shellHook = mkAgdaShellSetup pkgs agdaEnv + banner pkgs false true false;
          };

          lean = pkgs.mkShell {
            name = "lean2agda-lean";
            packages = build ++ leanTools;
            shellHook = banner pkgs true false false;
          };
        });

      # `nix run .#update -- docs/GITHUB_PROJECT.md` and friends, pinned by
      # this project's own flake.lock.
      apps = forAllSystems ({ system, ... }: github-project.apps.${system});

      # Handy for editors started outside the shell and for CI.
      packages = forAllSystems ({ pkgs, ... }: {
        agda = mkAgdaEnv pkgs;
        lean = pkgs.lean.lean-all;
      });

      formatter = forAllSystems ({ pkgs, ... }: pkgs.nixpkgs-fmt);
    };
}
