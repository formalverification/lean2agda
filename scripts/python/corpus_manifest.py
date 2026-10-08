"""
File: scripts/python/corpus_manifest.py

Description:
  The corpus manifest (corpus/manifest.json) as typed values, and the
  rules that make an entry malformed.  corpus/SCHEMA.md states the same
  rules in prose; the two change together.

  Parsing and validation are pure.  The one edge here is
  gather_entry_files, which reads what a translated entry's directory
  holds into an EntryFiles value; entry_file_problems then judges that
  value without touching the disk.

Design Principles:
  - A problem is a sentence, and a malformed entry carries all of its
    problems, not just the first, so that one run shows everything to
    fix.
  - Parsing returns Result values whose error is a non-empty tuple of
    problems; nothing here raises on bad input.
"""
from __future__ import annotations

import json
import re
from dataclasses import dataclass
from itertools import accumulate
from pathlib import Path
from typing import Iterator, Mapping, Optional, Sequence, Union

from _utils.file_ops import file_size, ls_dir, read_text
from _utils.pipeline_types import PipelineError, Result

# ---------------------------------------------------------------------------
# The vocabulary (corpus/SCHEMA.md)
# ---------------------------------------------------------------------------

# Provisional slugs for the gap catalog's entries (issue M1-5): the ten
# rows of the README's table "What the translation has to bridge", then
# three entries the catalog's issue lists that the table does not.
FEATURES: tuple[str, ...] = (
    "impredicative-prop",
    "proof-irrelevance",
    "k-and-uip",
    "large-elimination",
    "quotients",
    "axioms",
    "universe-levels",
    "structure-eta",
    "literals",
    "trust-escape-hatches",
    "decidable-and-noncomputable",
    "nested-and-mutual-inductives",
    "projections-and-let",
)
PROFILES: tuple[str, ...] = ("K", "CC", "CU")
STATUSES: tuple[str, ...] = ("planned", "translated")
TIERS: tuple[str, ...] = ("T0", "T1", "T2", "T3")
ENTRY_FIELDS: tuple[str, ...] = (
    "id", "theme", "lean_name", "lean_module", "axioms", "tier",
    "features", "agda_files", "status", "issue",
)
FILE_FIELDS: tuple[str, ...] = ("path", "flags", "profile")
SIDECAR_FIELDS: tuple[str, ...] = ("bytes", "sha256", "command")

# An export larger than this many bytes is committed as a sidecar.
SIDECAR_THRESHOLD: int = 1_000_000

# What each profile's flags must and must not contain.
REQUIRED_FLAGS: Mapping[str, tuple[str, ...]] = {
    "K": ("--safe",),
    "CC": ("--safe", "--cubical-compatible"),
    "CU": ("--safe", "--cubical"),
}
FORBIDDEN_FLAGS: Mapping[str, tuple[str, ...]] = {
    "K": ("--cubical-compatible", "--without-K", "--cubical", "--erased-cubical"),
    "CC": ("--cubical", "--erased-cubical"),
    "CU": ("--erased-cubical",),
}

_ID = re.compile(r"[a-z0-9]+(-[a-z0-9]+)*")
_SHA256 = re.compile(r"[0-9a-f]{64}")
# The tokens that decide where an Agda file's header ends: whitespace,
# pragmas, block comments (whose ends block_comment_end finds, since they
# nest), line comments, string literals, and anything else, which is a
# declaration and ends the header.  A "--" inside a name such as "a--b"
# reads as a line comment here; that can only hide an OPTIONS pragma
# placed later on the same line, after the header, where Agda ignores it.
_TOKEN = re.compile(r"""
    (?P<space>\s+)
  | (?P<pragma>\{-\#.*?(?:\#-\}|\Z))
  | (?P<comment>\{-)
  | (?P<line>--[^\n]*)
  | (?P<string>"(?:[^"\\\n]|\\.)*"?)
  | (?P<other>[^\s"{-]+|.)
""", re.VERBOSE | re.DOTALL)
_COMMENT_BRACKET = re.compile(r"\{-|-\}")
# Agda's source files: plain, and literate in any markup (.lagda,
# .lagda.md, .lagda.tex, ...).  Interface files (.agdai) are not sources.
_AGDA_SOURCE = re.compile(r"\.(agda|lagda(\.[A-Za-z]+)?)$")


# ---------------------------------------------------------------------------
# Values
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class AgdaFile:
    """One Agda file of an entry, as the manifest lists it."""

    path: str
    flags: tuple[str, ...]
    profile: str


@dataclass(frozen=True)
class Entry:
    """A well-formed manifest entry."""

    id: str
    theme: str
    lean_name: str
    lean_module: str
    axioms: tuple[str, ...]
    tier: str
    features: tuple[str, ...]
    agda_files: tuple[AgdaFile, ...]
    status: str
    issue: int


@dataclass(frozen=True)
class Malformed:
    """A manifest entry that breaks a rule: its label (the id when the
    entry has a usable one), its status if readable, and every problem."""

    label: str
    status: str
    problems: tuple[str, ...]


Item = Union[Entry, Malformed]


@dataclass(frozen=True)
class EntryFiles:
    """What a translated entry's directory holds, read once at the edge.

    `sources` maps each listed Agda file that exists to its text;
    `present` names every Agda source file under agda/, plain or
    literate, by its path relative to agda/; `term_bytes` is the size of
    lean/term.ndjson, None when there is none; `sidecar` is the text of
    lean/term.sidecar.json if it exists.
    """

    sources: tuple[tuple[str, str], ...]
    present: tuple[str, ...]
    has_statement: bool
    has_notes: bool
    term_bytes: Optional[int]
    sidecar: Optional[str]


@dataclass(frozen=True)
class Pragmas:
    """The OPTIONS pragmas of an Agda file, each as its flags, split where
    Agda splits them: `header` holds those before the file's first
    declaration (its module header), which Agda honors; `later` holds
    those after it, which Agda ignores with a warning.  A pragma inside a
    comment is in neither, since Agda ignores it silently."""

    header: tuple[tuple[str, ...], ...]
    later: tuple[tuple[str, ...], ...]


# ---------------------------------------------------------------------------
# Pure rules
# ---------------------------------------------------------------------------

def tier_of(axioms: Sequence[str]) -> str:
    """The tier the axioms imply (corpus/SCHEMA.md, Tiers from axioms)."""
    standard = {"propext", "Quot.sound", "Classical.choice"}
    if any(axiom not in standard for axiom in axioms):
        return "T3"
    if "Classical.choice" in axioms:
        return "T2"
    return "T1" if axioms else "T0"


def profile_problems(flags: Sequence[str], profile: str) -> tuple[str, ...]:
    """The ways the flags disagree with the profile."""
    missing = tuple(
        f"profile {profile} needs {flag}, which the flags lack"
        for flag in REQUIRED_FLAGS[profile] if flag not in flags
    )
    forbidden = tuple(
        f"profile {profile} forbids {flag}"
        for flag in FORBIDDEN_FLAGS[profile] if flag in flags
    )
    return missing + forbidden


def repeats(values: Sequence[str]) -> tuple[str, ...]:
    """The values that occur more than once, each named once, in the
    order of their first occurrence."""
    return tuple(dict.fromkeys(v for v in values if values.count(v) > 1))


def _is_string_list(value: object) -> bool:
    return isinstance(value, list) and all(isinstance(v, str) for v in value)


def field_problems(raw: Mapping[str, object], fields: Sequence[str], what: str) -> tuple[str, ...]:
    """Missing and unknown fields of an object that should have exactly
    `fields`."""
    missing = tuple(f"{what} lacks the field {name!r}" for name in fields if name not in raw)
    unknown = tuple(
        f"{what} has the unknown field {name!r}" for name in raw if name not in fields
    )
    return missing + unknown


def agda_file_problems(raw: object, position: int) -> tuple[str, ...]:
    """Everything wrong with one object of agda_files."""
    what = f"agda_files[{position}]"
    if not isinstance(raw, dict):
        return (f"{what} is not an object",)
    shape = field_problems(raw, FILE_FIELDS, what)
    if shape:
        return shape
    path, flags, profile = raw["path"], raw["flags"], raw["profile"]
    path_problems = (
        ()
        if isinstance(path, str) and path.endswith(".agda") and "/" not in path
        and len(path) > len(".agda")
        else (f"{what}: path {path!r} is not a file name ending in .agda",)
    )
    flag_problems = (
        ()
        if _is_string_list(flags) and all(f.startswith("--") for f in flags)
        else (f"{what}: flags must be a list of strings beginning with --",)
    )
    profile_ok = isinstance(profile, str) and profile in PROFILES
    known_profile = (
        () if profile_ok else (f"{what}: profile {profile!r} is not one of {', '.join(PROFILES)}",)
    )
    agreement = (
        tuple(f"{what}: {p}" for p in profile_problems(flags, profile))
        if profile_ok and not flag_problems
        else ()
    )
    return path_problems + flag_problems + known_profile + agreement


def parse_agda_file(raw: object, position: int) -> Result[AgdaFile, tuple[str, ...]]:
    """One object of agda_files as an AgdaFile, or its problems."""
    problems = agda_file_problems(raw, position)
    if problems:
        return Result.err(problems)
    assert isinstance(raw, dict)
    return Result.ok(AgdaFile(raw["path"], tuple(raw["flags"]), raw["profile"]))


def id_problems(ident: object) -> tuple[str, ...]:
    """An id is lowercase kebab-case."""
    ok = isinstance(ident, str) and _ID.fullmatch(ident)
    return () if ok else (f"id {ident!r} is not lowercase kebab-case",)


def string_problems(raw: Mapping[str, object], name: str) -> tuple[str, ...]:
    """A free-text field is a non-empty string."""
    value = raw[name]
    ok = isinstance(value, str) and value.strip()
    return () if ok else (f"{name} must be a non-empty string",)


def axiom_problems(axioms: object) -> tuple[str, ...]:
    """The axioms are strings, none repeated."""
    if not _is_string_list(axioms):
        return ("axioms must be a list of strings",)
    return tuple(f"axiom {a!r} is listed twice" for a in repeats(axioms))


def tier_problems(tier: object, axioms: object) -> tuple[str, ...]:
    """The tier is one of T0 to T3, and the one the axioms imply."""
    if tier not in TIERS:
        return (f"tier {tier!r} is not one of {', '.join(TIERS)}",)
    if _is_string_list(axioms) and tier_of(axioms) != tier:
        return (f"tier is {tier} but the axioms imply {tier_of(axioms)}",)
    return ()


def feature_problems(features: object) -> tuple[str, ...]:
    """The features are known slugs, at least one, none repeated."""
    if not _is_string_list(features) or not features:
        return ("features must be a non-empty list of strings",)
    unknown = tuple(f"feature {f!r} is not in the vocabulary of corpus/SCHEMA.md"
                    for f in features if f not in FEATURES)
    return unknown + tuple(f"feature {f!r} is listed twice" for f in repeats(features))


def agda_files_problems(files: object) -> tuple[str, ...]:
    """Every object of agda_files is well formed, and no path repeats."""
    if not isinstance(files, list):
        return ("agda_files must be a list",)
    each = sum((agda_file_problems(f, i) for i, f in enumerate(files)), ())
    paths = [f["path"] for f in files if isinstance(f, dict) and isinstance(f.get("path"), str)]
    return each + tuple(f"agda file {p!r} is listed twice" for p in repeats(paths))


def status_problems(status: object, files: object) -> tuple[str, ...]:
    """The status is known, and a translated entry lists a file."""
    if status not in STATUSES:
        return (f"status {status!r} is not one of {', '.join(STATUSES)}",)
    if status == "translated" and isinstance(files, list) and not files:
        return ("a translated entry must list at least one Agda file",)
    return ()


def issue_problems(issue: object) -> tuple[str, ...]:
    """The issue is a positive integer (JSON's true is not one)."""
    ok = isinstance(issue, int) and not isinstance(issue, bool) and issue > 0
    return () if ok else (f"issue {issue!r} is not a positive integer",)


def entry_problems(raw: Mapping[str, object]) -> tuple[str, ...]:
    """Everything wrong with an entry object that has exactly the right
    fields (parse_entry checks the fields first)."""
    return (
        id_problems(raw["id"])
        + sum((string_problems(raw, name) for name in ("theme", "lean_name", "lean_module")), ())
        + axiom_problems(raw["axioms"])
        + tier_problems(raw["tier"], raw["axioms"])
        + feature_problems(raw["features"])
        + agda_files_problems(raw["agda_files"])
        + status_problems(raw["status"], raw["agda_files"])
        + issue_problems(raw["issue"])
    )


def entry_label(raw: object, position: int) -> str:
    """How a report names an entry: its id if it has a string one."""
    if isinstance(raw, dict) and isinstance(raw.get("id"), str) and raw["id"]:
        return raw["id"]
    return f"entry {position}"


def entry_status(raw: object) -> str:
    """The entry's status if it is a string, else '?'."""
    if isinstance(raw, dict) and isinstance(raw.get("status"), str):
        return raw["status"]
    return "?"


def parse_entry(raw: object, position: int) -> Item:
    """A manifest object as an Entry, or as a Malformed with every problem."""
    label, status = entry_label(raw, position), entry_status(raw)
    if not isinstance(raw, dict):
        return Malformed(label, status, ("the entry is not a JSON object",))
    problems = field_problems(raw, ENTRY_FIELDS, "the entry") or entry_problems(raw)
    if problems:
        return Malformed(label, status, problems)
    return Entry(
        id=raw["id"],
        theme=raw["theme"],
        lean_name=raw["lean_name"],
        lean_module=raw["lean_module"],
        axioms=tuple(raw["axioms"]),
        tier=raw["tier"],
        features=tuple(raw["features"]),
        agda_files=tuple(parse_agda_file(f, i).unwrap() for i, f in enumerate(raw["agda_files"])),
        status=raw["status"],
        issue=raw["issue"],
    )


def mark_duplicates(items: Sequence[Item]) -> tuple[Item, ...]:
    """Every well-formed entry whose id another entry shares becomes
    malformed; ids are directory names and must be unique."""
    ids = [item.id for item in items if isinstance(item, Entry)]
    shared = set(repeats(ids))
    return tuple(
        Malformed(item.id, item.status, (f"the id {item.id!r} is used by more than one entry",))
        if isinstance(item, Entry) and item.id in shared
        else item
        for item in items
    )


def parse_manifest(data: object) -> Result[tuple[Item, ...], str]:
    """The decoded manifest as items, or why it is unusable as a whole."""
    if not isinstance(data, list):
        return Result.err("the manifest is not a JSON array")
    return Result.ok(mark_duplicates([parse_entry(raw, i) for i, raw in enumerate(data)]))


def decode_manifest(text: str) -> Result[tuple[Item, ...], str]:
    """The manifest's text as items, or why it cannot be used."""
    try:
        data = json.loads(text)
    except json.JSONDecodeError as e:
        return Result.err(f"the manifest is not valid JSON: {e}")
    return parse_manifest(data)


def block_comment_end(text: str, start: int) -> int:
    """The index just past the block comment that opens at `start`.  Block
    comments nest, and one left open runs to the end of the text."""
    steps = (
        (m.end(), 1 if m.group() == "{-" else -1)
        for m in _COMMENT_BRACKET.finditer(text, start)
    )
    running = accumulate(steps, lambda total, step: (step[0], total[1] + step[1]))
    return next((end for end, depth in running if depth == 0), len(text))


def tokens(text: str) -> Iterator[tuple[str, str]]:
    """The file's tokens as (kind, text) pairs, in the kinds of _TOKEN."""
    position = 0
    while position < len(text):
        match = _TOKEN.match(text, position)
        assert match is not None and match.lastgroup is not None  # "other" matches any character
        end = block_comment_end(text, position) if match.lastgroup == "comment" else match.end()
        yield match.lastgroup, text[position:end]
        position = end


def options_of(span: Sequence[tuple[str, str]]) -> tuple[tuple[str, ...], ...]:
    """The flags of each OPTIONS pragma among the tokens."""
    words = (lexeme[3:].removesuffix("#-}").split() for kind, lexeme in span if kind == "pragma")
    return tuple(tuple(w[1:]) for w in words if w[:1] == ["OPTIONS"])


def scan_pragmas(text: str) -> Pragmas:
    """The OPTIONS pragmas of an Agda file, where Agda honors or ignores
    them (measured with Agda 2.8.0: one inside a block comment, nested or
    not, is ignored silently; one after the module header is ignored with
    the warning UselessPragma)."""
    found = list(tokens(text))
    first = next((i for i, (kind, _) in enumerate(found) if kind in ("string", "other")), len(found))
    return Pragmas(options_of(found[:first]), options_of(found[first:]))


def pragma_problems(agda_file: AgdaFile, text: str) -> tuple[str, ...]:
    """The ways a file's OPTIONS pragmas disagree with its manifest entry:
    the one pragma Agda honors must carry the manifest's flags, and no
    pragma may sit where Agda ignores it."""
    where = f"agda/{agda_file.path}"
    pragmas = scan_pragmas(text)
    late = (
        (f"{where} has an OPTIONS pragma after its module header, which Agda ignores; "
         "move it to the top of the file",)
        if pragmas.later else ()
    )
    if not pragmas.header:
        return (f"{where} has no OPTIONS pragma before its module declaration, the only "
                "place Agda honors one (not inside a comment)",) + late
    if len(pragmas.header) > 1:
        return (f"{where} has {len(pragmas.header)} OPTIONS pragmas; write its flags in one",) + late
    if pragmas.header[0] != agda_file.flags:
        return (f"{where} declares {' '.join(pragmas.header[0])} but the manifest lists "
                f"{' '.join(agda_file.flags)}",) + late
    return late


def is_agda_source(path: str) -> bool:
    """Whether a path names an Agda source file, plain or literate."""
    return _AGDA_SOURCE.search(path) is not None


def sidecar_problems(text: str) -> tuple[str, ...]:
    """Everything wrong with the text of lean/term.sidecar.json."""
    try:
        data = json.loads(text)
    except json.JSONDecodeError as e:
        return (f"lean/term.sidecar.json is not valid JSON: {e}",)
    if not isinstance(data, dict):
        return ("lean/term.sidecar.json is not a JSON object",)
    shape = field_problems(data, SIDECAR_FIELDS, "lean/term.sidecar.json")
    if shape:
        return shape
    size, digest, command = data["bytes"], data["sha256"], data["command"]
    return (
        (() if isinstance(size, int) and not isinstance(size, bool) and size > SIDECAR_THRESHOLD
         else (f"lean/term.sidecar.json: bytes must be an integer above {SIDECAR_THRESHOLD}; "
               "a smaller export is committed as lean/term.ndjson",))
        + (() if isinstance(digest, str) and _SHA256.fullmatch(digest)
           else ("lean/term.sidecar.json: sha256 must be 64 lowercase hexadecimal digits",))
        + (() if isinstance(command, str) and command.strip()
           else ("lean/term.sidecar.json: command must be a non-empty string",))
    )


def term_problems(term_bytes: Optional[int], sidecar: Optional[str]) -> tuple[str, ...]:
    """The exported term is either lean/term.ndjson, at most 1 MB, or the
    sidecar that stands in its place, never both."""
    if sidecar is not None and term_bytes is not None:
        return ("lean/ holds both term.ndjson and term.sidecar.json; the sidecar stands in "
                "place of an export over 1 MB, so keep one",) + sidecar_problems(sidecar)
    if sidecar is not None:
        return sidecar_problems(sidecar)
    if term_bytes is None:
        return ("lean/ holds neither term.ndjson nor term.sidecar.json",)
    if term_bytes > SIDECAR_THRESHOLD:
        return (f"lean/term.ndjson is {term_bytes:,} bytes, over the {SIDECAR_THRESHOLD:,}-byte "
                "limit; commit lean/term.sidecar.json in its place",)
    return ()


def entry_file_problems(entry: Entry, files: EntryFiles) -> tuple[str, ...]:
    """Everything wrong with a translated entry's directory."""
    sources = dict(files.sources)
    listed = tuple(f.path for f in entry.agda_files)
    agda = sum(
        (pragma_problems(f, sources[f.path]) if f.path in sources
         else (f"agda/{f.path} is listed but missing",)
         for f in entry.agda_files),
        (),
    )
    unlisted = tuple(
        f"agda/{name} is not one of the files the manifest lists (plain .agda files "
        "directly in agda/), so it would never be checked"
        for name in files.present if name not in listed
    )
    statement = () if files.has_statement else ("lean/Statement.lean is missing",)
    notes = () if files.has_notes else ("notes.md is missing",)
    return agda + unlisted + statement + notes + term_problems(files.term_bytes, files.sidecar)


def orphan_problems(directories: Sequence[str], items: Sequence[Item]) -> tuple[str, ...]:
    """Directories of corpus/ that no entry names; nothing would check them."""
    labels = {item.id if isinstance(item, Entry) else item.label for item in items}
    return tuple(
        f"corpus/{name}/ is not the id of any manifest entry"
        for name in sorted(directories)
        if name not in labels and not name.startswith((".", "_"))
    )


# ---------------------------------------------------------------------------
# The edge
# ---------------------------------------------------------------------------

def gather_entry_files(entry_dir: Path, entry: Entry) -> Result[EntryFiles, PipelineError]:
    """Read what the entry's directory holds.  A missing agda/ directory
    is not an error here: entry_file_problems reports the files as
    missing."""
    agda_dir = entry_dir / "agda"
    # Recursive, and every Agda source: a file in a subdirectory, or a
    # literate one, would otherwise sit beside the listed files unchecked.
    listing: Result[list[Path], PipelineError] = (
        ls_dir(agda_dir, "**/*") if agda_dir.is_dir() else Result.ok([])
    )
    if listing.is_err:
        return Result.err(listing.unwrap_err())
    present = tuple(
        rel for rel in (p.relative_to(agda_dir).as_posix() for p in listing.unwrap())
        if is_agda_source(rel)
    )
    readable = tuple(
        (f.path, read_text(agda_dir / f.path)) for f in entry.agda_files if f.path in present
    )
    failed = next((r for _, r in readable if r.is_err), None)
    if failed is not None:
        return Result.err(failed.unwrap_err())
    sidecar_path = entry_dir / "lean" / "term.sidecar.json"
    sidecar = read_text(sidecar_path) if sidecar_path.is_file() else None
    if sidecar is not None and sidecar.is_err:
        return Result.err(sidecar.unwrap_err())
    term_path = entry_dir / "lean" / "term.ndjson"
    term_size = file_size(term_path) if term_path.is_file() else None
    if term_size is not None and term_size.is_err:
        return Result.err(term_size.unwrap_err())
    return Result.ok(EntryFiles(
        sources=tuple((path, r.unwrap()) for path, r in readable),
        present=present,
        has_statement=(entry_dir / "lean" / "Statement.lean").is_file(),
        has_notes=(entry_dir / "notes.md").is_file(),
        term_bytes=term_size.unwrap() if term_size is not None else None,
        sidecar=sidecar.unwrap() if sidecar is not None else None,
    ))
