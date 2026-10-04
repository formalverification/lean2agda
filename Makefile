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

doctor: ## Print tool versions; fail unless Lean, Agda, Python and both Agda libraries resolve
	@echo "lean    : $$($(LEAN) --version 2>/dev/null || echo MISSING)"
	@echo "lake    : $$($(LAKE) --version 2>/dev/null || echo MISSING)"
	@echo "agda    : $$($(AGDA) --version 2>/dev/null || echo MISSING)"
	@echo "python  : $$($(PYTHON) --version 2>/dev/null || echo MISSING)"
	@echo "gh      : $$(gh --version 2>/dev/null | head -n 1 || echo MISSING)"
	@echo "engine  : $(ENGINE_MODE)"
	@command -v $(LEAN) >/dev/null 2>&1 && command -v $(AGDA) >/dev/null 2>&1 \
	  && command -v $(PYTHON) >/dev/null 2>&1 \
	  || { echo "error: a required tool is missing; enter the shell with: nix develop"; exit 1; }
	@tmp=$$(mktemp -d) \
	  && printf '{-# OPTIONS --safe --cubical-compatible #-}\nmodule Doctor where\nopen import Data.Nat using (ℕ)\n' > $$tmp/Doctor.agda \
	  && printf '{-# OPTIONS --safe --cubical --guardedness #-}\nmodule DoctorCubical where\nopen import Cubical.Foundations.Prelude using (Type)\n' > $$tmp/DoctorCubical.agda \
	  && (cd $$tmp && $(AGDA) Doctor.agda && $(AGDA) DoctorCubical.agda) \
	  && rm -rf $$tmp \
	  && echo "agda libraries: standard-library and cubical resolve" \
	  || { echo "error: Agda could not resolve the standard library or the cubical library (see above)"; exit 1; }

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
