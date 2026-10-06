# File: Makefile
#
# The project's command-line surface.  Two groups of targets:
#
#   roadmap   populate / update / lint operate on docs/GITHUB_PROJECT.md
#             through the github-project engine, which has exactly one home
#             (the williamdemeo/github-project repository) and is found here
#             through whichever channel is available, in order:
#               path      gh-project-* CLIs on PATH (the Nix dev shell)
#               checkout  GHPROJECT_DIR points at a checkout of the engine
#             (A `local` mode exists for template copies that have not run
#             `make init`; this project has.)
#   project   doctor / check / test / corpus-check / atlas are the project's
#             own targets; the ones not yet implemented say which roadmap
#             issue implements them.
#   lean      lean-cache / lean-build / lean-smoke run Lake in translator/,
#             the Lake package that carries Mathlib (docs/pinning.md).
#
# Variables:
#   PLAN           plan file            (default: docs/GITHUB_PROJECT.md)
#   REPO           owner/name override  (default: the plan file's
#                                        **Repository**: header)
#   PYTHON         interpreter          (default: python3)
#   GHPROJECT_DIR  engine checkout path (checkout channel only)
#   NO_ENV_PREFIX  set (to anything) wherever gh authenticates *through*
#                  GH_TOKEN/GITHUB_TOKEN; GitHub Actions included.

PYTHON ?= python3
PLAN   ?= docs/GITHUB_PROJECT.md
REPO   ?=
GHPROJECT_DIR ?=
AGDA   ?= agda
LEAN   ?= lean
LAKE   ?= lake

FLAGS := $(if $(REPO),--repo $(REPO)) $(if $(NO_ENV_PREFIX),--no-env-prefix)

ifneq (,$(wildcard scripts/gh_project_populate.py))
  ENGINE_MODE := local
  POPULATE := $(PYTHON) scripts/gh_project_populate.py
  UPDATE   := $(PYTHON) scripts/gh_project_update.py
  LINT     := $(PYTHON) scripts/gh_project_lint.py
else ifneq (,$(shell command -v gh-project-update 2>/dev/null))
  ENGINE_MODE := path
  POPULATE := gh-project-populate
  UPDATE   := gh-project-update
  LINT     := gh-project-lint
else ifneq (,$(wildcard $(GHPROJECT_DIR)/scripts/gh_project_populate.py))
  ENGINE_MODE := checkout
  POPULATE := $(PYTHON) $(GHPROJECT_DIR)/scripts/gh_project_populate.py
  UPDATE   := $(PYTHON) $(GHPROJECT_DIR)/scripts/gh_project_update.py
  LINT     := $(PYTHON) $(GHPROJECT_DIR)/scripts/gh_project_lint.py
else
  ENGINE_MODE := missing
endif

.PHONY: help populate-dry populate update update-check lint \
        doctor check test corpus-check atlas \
        lean-cache lean-build lean-smoke \
        guard-gh guard-engine engine-mode
.DEFAULT_GOAL := help

# In `path` mode the resolved CLI is a Nix wrapper carrying its own `gh`,
# so the ambient PATH is not probed; the CLI reports its own error if gh is
# absent.  checkout mode runs bare python3 scripts and does need ambient gh.
ifeq ($(ENGINE_MODE),path)
GH_GUARD :=
else
GH_GUARD := guard-gh
endif

help: ## Show this help
	@grep -hE '^[a-zA-Z][a-zA-Z0-9_-]*:.*## ' $(MAKEFILE_LIST) \
	  | awk 'BEGIN {FS = ":.*## "} {printf "  \033[1m%-14s\033[0m %s\n", $$1, $$2}'

# ---- roadmap -------------------------------------------------------------

populate-dry: guard-engine $(GH_GUARD) ## Preview what populate would create (no mutations)
	$(POPULATE) $(PLAN) $(FLAGS) --dry-run

populate: guard-engine $(GH_GUARD) ## Create labels, milestones, issues on GitHub from $(PLAN)
	$(POPULATE) $(PLAN) $(FLAGS)

update: guard-engine $(GH_GUARD) ## Rewrite $(PLAN)'s generated regions from live GitHub state
	$(UPDATE) $(PLAN) $(FLAGS)

update-check: guard-engine $(GH_GUARD) ## Report whether $(PLAN) is stale without writing
	$(UPDATE) $(PLAN) $(FLAGS) --check

lint: guard-engine ## Validate $(PLAN)'s structure (no network)
	$(LINT) $(PLAN)

# ---- project -------------------------------------------------------------

# $(call probe,NAME,COMMAND) is a shell fragment for doctor's first recipe
# line.  It prints NAME and the first line COMMAND writes, or MISSING when
# COMMAND fails or writes nothing; in that case it also appends NAME to
# $$missing.  The status tested is COMMAND's own: in a pipeline such as
# `gh --version | head -n 1 || echo MISSING` it is head's, so MISSING could
# never appear.  The engine has no --version, so doctor runs its lint CLI's
# --help instead: an engine that is found but cannot start fails as well.
probe = v=$$($(2) 2>/dev/null) && [ -n "$$v" ] \
  || { v=MISSING; missing="$$missing $(1)"; }; \
  printf '%-8s: %s\n' '$(1)' "$$(printf '%s\n' "$$v" | head -n 1)";

doctor: ## Print tool versions; fail, naming each missing tool or Agda library or a split Lean pin
	@missing=; \
	  $(call probe,lean,$(LEAN) --version) \
	  $(call probe,lake,$(LAKE) --version) \
	  $(call probe,agda,$(AGDA) --version) \
	  $(call probe,python,$(PYTHON) --version) \
	  $(call probe,gh,gh --version) \
	  $(call probe,jq,jq --version) \
	  if [ '$(ENGINE_MODE)' != missing ] && $(LINT) --help >/dev/null 2>&1; \
	  then e='$(ENGINE_MODE)'; else e=MISSING; missing="$$missing engine"; fi; \
	  printf '%-8s: %s\n' engine "$$e"; \
	  [ -z "$$missing" ] \
	  || { echo "error: missing:$$missing; enter the shell with: nix develop"; exit 1; }
	@cmp -s lean-toolchain translator/lean-toolchain \
	  || { echo "error: translator/lean-toolchain differs from lean-toolchain;"; \
	       echo "       it should be a symlink to it (docs/pinning.md)"; exit 1; }; \
	  echo "lean-toolchain: $$(cat lean-toolchain), also read by translator/"
	@tmp=$$(mktemp -d) || exit 1; bad=; \
	  printf '{-# OPTIONS --safe --cubical-compatible #-}\nmodule Doctor where\nopen import Data.Nat using (ℕ)\n' > "$$tmp/Doctor.agda"; \
	  printf '{-# OPTIONS --safe --cubical --guardedness #-}\nmodule DoctorCubical where\nopen import Cubical.Foundations.Prelude using (Type)\n' > "$$tmp/DoctorCubical.agda"; \
	  (cd "$$tmp" && $(AGDA) Doctor.agda) || bad="$$bad standard-library"; \
	  (cd "$$tmp" && $(AGDA) DoctorCubical.agda) || bad="$$bad cubical"; \
	  rm -rf "$$tmp"; \
	  [ -z "$$bad" ] \
	  || { echo "error: Agda could not resolve:$$bad (see above)"; exit 1; }; \
	  echo "agda libraries: standard-library and cubical resolve"

check: ## Type-check the corpus and the emitted Agda (placeholder: lands with M1-6 and M2-8)
	@echo "check: nothing to check yet.  The corpus checker lands with issue M1-6"
	@echo "       and the emitted-Agda checker with issue M2-8 (docs/GITHUB_PROJECT.md)."

test: ## Run the translator and Python test suites (placeholder: lands with M2-1)
	@echo "test: no test suites yet.  The translator's golden tests land with issue M2-1"
	@echo "      and the Python tests with the first script under scripts/python/."

corpus-check: ## Type-check every corpus entry under its declared flags (placeholder: lands with M1-6)
	@echo "corpus-check: the corpus checker lands with issue M1-6; see corpus/README.md."

atlas: ## Compute the axiom profile of the pinned Mathlib revision (placeholder: lands with M1-11)
	@echo "atlas: the atlas producer lands with issue M1-11; see atlas/README.md."

# ---- lean ----------------------------------------------------------------

# Lake runs in translator/, the package that requires Mathlib; its first
# `lake update --keep-toolchain` creates .lake/packages/ (docs/pinning.md).
# No CI job runs these targets: the cache is several gigabytes.

lean-cache: ## Fetch Mathlib's prebuilt .olean files into translator/.lake (lake exe cache get)
	cd translator && $(LAKE) exe cache get

lean-build: ## Build the translator's Lake package (lake build in translator/)
	cd translator && $(LAKE) build

# lean-smoke checks the cache two ways.  `lake build --no-build Mathlib`
# compiles nothing: it exits with status 3 if any of Mathlib's modules, or
# of its dependencies', is out of date, which is how a missing file or a
# cache built by another Lean would show; a plain `lake build` would start
# compiling Mathlib instead.  Smoke.lean then loads the files.
lean-smoke: ## Check that Mathlib's cache is complete and loads (lake build --no-build, #print axioms)
	cd translator && $(LAKE) build --no-build Mathlib
	cd translator && $(LAKE) env $(LEAN) scripts/Smoke.lean

# ---- plumbing ------------------------------------------------------------

engine-mode: ## Print which engine channel this invocation resolved (debugging)
	@echo "$(ENGINE_MODE)"

guard-engine:
ifeq ($(ENGINE_MODE),missing)
	@echo "error: the github-project engine was not found.  Provide it via one of:"; \
	echo "  - Nix: enter the dev shell (nix develop) wired by this flake's"; \
	echo "    github-project input, so the gh-project-* CLIs are on PATH"; \
	echo "  - checkout: clone https://github.com/williamdemeo/github-project"; \
	echo "    and pass GHPROJECT_DIR=/path/to/that/clone"; \
	exit 1
endif

guard-gh:
	@command -v gh >/dev/null || { \
	  echo "error: the GitHub CLI (gh) is required for this target."; \
	  echo "       https://cli.github.com/  (or: nix develop)"; \
	  exit 1; \
	}
