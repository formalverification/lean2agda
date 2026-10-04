# File: flake.nix
#
# lean2agda development environment.  One `nix develop` provides everything
# the project needs; nothing is taken from the host system.
#
#   Lean      the toolchain named in ./lean-toolchain, fetched as the official
#             prebuilt release by lean4-nix (readToolchainFile; no source
#             build).  lean4-nix carries one manifest per stable Lean release
#             and lags Lean by about one release, so the pin here is the newest
#             version it knows; docs/pinning.md (issue M1-3) aligns it with
#             the pinned Mathlib revision.
#   Agda      Agda with agda-stdlib and the cubical library from nixpkgs
#             (2.8.0, 2.3 and 0.9 at the time of writing), registered
#             project-locally in $ROOT/.agda (gitignored) by the shellHook,
#             which also installs an `agda` wrapper passing
#             --no-default-libraries and the project's --library-file, so the
#             user's ~/.config/agda cannot contribute.  Optional external
#             libraries are registered when AGDA_UNIMATH_ROOT,
#             AGDA_TYPETOPOLOGY_ROOT or AGDA_ALGEBRAS_ROOT points at a checkout
#             containing an .agda-lib file.
#   Python    python3 from nixpkgs, standard library only (house style).
#   Engine    the github-project roadmap engine (gh-project-populate, -update,
#             -lint) as a pinned flake input; the Makefile finds it on PATH.
#
# Shells:  nix develop            everything (default)
#          nix develop .#agda     Agda and its libraries only
#          nix develop .#lean     the Lean toolchain only
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
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];

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
      # The heredoc lines sit at column 0 on purpose: Nix strips the common
      # indentation of this string, and the terminator must reach the shell
      # at column 0.
      mkAgdaShellSetup = pkgs: ''
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
        NIX_AGDA="$(command -v agda)"
        cat > "$AGDA_DIR/bin/agda" <<EOF
#!/usr/bin/env bash
exec "$NIX_AGDA" --library-file "$AGDA_DIR/libraries" "\$@"
EOF
        chmod +x "$AGDA_DIR/bin/agda"
        export PATH="$AGDA_DIR/bin:$PATH"
      '';

      banner = pkgs: withLean: withAgda: ''
        echo ""
        echo "lean2agda dev shell"
        ${if withLean then ''echo "  Lean     : $(lean --version 2>/dev/null || echo unavailable)"'' else ""}
        ${if withAgda then ''echo "  Agda     : ${pkgs.agda.version}  (standard-library ${pkgs.agdaPackages.standard-library.version}, cubical ${pkgs.agdaPackages.cubical.version})"'' else ""}
        ${if withAgda then ''echo "  AGDA_DIR : $AGDA_DIR"'' else ""}
        echo "  Python   : ${pkgs.python3.version}"
        echo "  engine   : $(command -v gh-project-lint >/dev/null 2>&1 && echo on PATH || echo missing)"
        echo ""
      '';
    in
    {
      devShells = forAllSystems ({ pkgs, system }:
        let
          agdaEnv = mkAgdaEnv pkgs;
          engine = github-project.packages.${system}.gh-project-engine;
          common = [ pkgs.gnumake pkgs.git pkgs.gh pkgs.jq pkgs.python3 engine ];
        in
        {
          default = pkgs.mkShell {
            name = "lean2agda-dev";
            packages = common ++ [ agdaEnv pkgs.lean.lean-all ];
            LANG = "C.UTF-8";
            LC_ALL = "C.UTF-8";
            shellHook = mkAgdaShellSetup pkgs + banner pkgs true true;
          };

          agda = pkgs.mkShell {
            name = "lean2agda-agda";
            packages = common ++ [ agdaEnv ];
            LANG = "C.UTF-8";
            LC_ALL = "C.UTF-8";
            shellHook = mkAgdaShellSetup pkgs + banner pkgs false true;
          };

          lean = pkgs.mkShell {
            name = "lean2agda-lean";
            packages = common ++ [ pkgs.lean.lean-all ];
            shellHook = banner pkgs true false;
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
