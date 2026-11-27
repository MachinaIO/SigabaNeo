"""The research protocol's records (docs/RESEARCH_PROTOCOL.md, sections 2-6): canonical JSON, goal
fingerprints, fenced blocks, markers, validation, digests. Standard library only: the DAG's tools
(`dag_tools.py precheck`, `index`) use it too."""

from __future__ import annotations

import hashlib
import json
import re
import uuid as _uuid
from pathlib import Path

import dag as D

MAX_BLOCK = 64 * 1024
KINDS = ("goal", "task", "plan", "candidate", "checkpoint", "summary", "progress")
PAIRS = tuple(sorted((d, o) for d in ("design", "cryptanalysis")
                     for o in ("expand", "deepen", "organize")))
OUTCOMES = ("verified_solution", "verified_refutation", "verified_partial", "candidate", "handoff",
            "inconclusive", "duplicate", "cancelled", "infra_failure")
UUID_RE = re.compile(r"[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}")
GOAL_NOTE = re.compile(r"goal-([0-9a-f]{64})")
STATUS_MARKER = "<!-- sigaba-status -->"


def canonical(obj) -> str:
    """UTF-8 canonical JSON: sorted keys, no whitespace. Floats are refused (they do not have one
    spelling)."""
    def check(x):
        if isinstance(x, float):
            raise ValueError("floats are not allowed in protocol identities")
        if isinstance(x, dict):
            for v in x.values():
                check(v)
        elif isinstance(x, list):
            for v in x:
                check(v)
    check(obj)
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def sha256(data: bytes | str) -> str:
    return hashlib.sha256(data.encode() if isinstance(data, str) else data).hexdigest()


def new_uuid() -> str:
    return str(_uuid.uuid4())


# -- goals ---------------------------------------------------------------------------------------

def goal_identity(goal: dict) -> dict:
    """The fields that make a goal's identity (title and approval excluded)."""
    return {"schema": goal["schema"], "kind": goal["kind"],
            "targets": sorted(goal.get("targets", [])),
            "definitions": sorted(goal.get("definitions", [])),
            "objective": {"kind": goal["objective"]["kind"],
                          "threshold": goal["objective"].get("threshold")},
            "policy": {"forbidden_routes": sorted(goal.get("policy", {}).get("forbidden_routes",
                                                                                [])),
                       "intent": goal.get("policy", {}).get("intent", "")},
            "parent": goal.get("parent")}


def goal_fingerprint(goal: dict) -> str:
    return sha256(canonical(goal_identity(goal)))


def goal_note(goal: dict) -> tuple[str, str]:
    """The path and text of a goal's note."""
    fp = goal_fingerprint(goal)
    refs = sorted(set(goal.get("targets", [])) | set(goal.get("definitions", [])))
    lines = ["---", f"title: {goal_title_line(goal['title'])}",
             "tags: [research-goal]", f"refs: [{', '.join(refs)}]", "---", "",
             f"# Research goal: {goal['title']}", "",
             f"Fingerprint `{fp}`. The contract below is data; the Lean nodes in `targets` and "
             "`definitions` fix its meaning. `policy` is a research policy, not a Lean-verified "
             "property.", "", render_block("goal", goal), ""]
    return f"dag/Notes/goal-{fp}.md", "\n".join(lines)


def goal_title_line(title: str) -> str:
    t = " ".join(title.split()).replace('"', "'")[:190]
    return f'"{t}"'


def goal_note_problems(path: str, text: str) -> list[str]:
    """What is wrong with a note tagged `research-goal` (the precheck's extra check)."""
    m = re.fullmatch(r"dag/Notes/(.*)\.md", path)
    try:
        meta, body = D.front_matter(text)
    except ValueError as e:
        return [str(e)]
    blocks = find_blocks(body, "goal")
    if len(blocks) != 1:
        return [f"a goal note has exactly one `sigaba-goal-v1` block (found {len(blocks)})"]
    goal, err = blocks[0]
    if err:
        return [err]
    probs = validate("goal", goal)
    if probs:
        return probs
    fp = goal_fingerprint(goal)
    if not m or m.group(1) != f"goal-{fp}":
        probs.append(f"the file of this goal is dag/Notes/goal-{fp}.md")
    refs = sorted(set(goal.get("targets", [])) | set(goal.get("definitions", [])))
    if sorted(meta.get("refs", [])) != refs:
        probs.append("`refs` must be exactly the goal's targets and definitions")
    return probs


def summary_note_problems(text: str) -> list[str]:
    try:
        _, body = D.front_matter(text)
    except ValueError as e:
        return [str(e)]
    blocks = find_blocks(body, "summary")
    if len(blocks) > 1:
        return ["at most one `sigaba-summary-v1` block"]
    if not blocks:
        return []
    obj, err = blocks[0]
    return [err] if err else validate("summary", obj)


# -- blocks --------------------------------------------------------------------------------------

def render_block(kind: str, obj: dict) -> str:
    return f"```sigaba-{kind}-v1\n{json.dumps(obj, indent=1, ensure_ascii=False)}\n```"


BLOCK = re.compile(r"^```sigaba-([a-z]+)-v1[ \t]*\n(.*?)^```[ \t]*$", re.S | re.M)


def find_blocks(text: str, kind: str) -> list[tuple[dict | None, str | None]]:
    """Every fenced `sigaba-<kind>-v1` block of `text`, parsed: (object, None) or (None, error)."""
    out = []
    for m in BLOCK.finditer(text or ""):
        if m.group(1) != kind:
            continue
        raw = m.group(2)
        if len(raw) > MAX_BLOCK:
            out.append((None, f"a sigaba-{kind}-v1 block is larger than {MAX_BLOCK} bytes"))
            continue
        try:
            obj = json.loads(raw)
        except json.JSONDecodeError as e:
            out.append((None, f"sigaba-{kind}-v1: not JSON: {e}"))
            continue
        if not isinstance(obj, dict):
            out.append((None, f"sigaba-{kind}-v1: not an object"))
            continue
        out.append((obj, None))
    return out


def one_block(text: str, kind: str) -> dict | None:
    """The single valid block of `kind` in `text`, or None."""
    blocks = find_blocks(text, kind)
    if len(blocks) != 1 or blocks[0][1]:
        return None
    obj = blocks[0][0]
    return obj if not validate(kind, obj) else None


_SCHEMAS: dict[str, dict] = {}


def validate(kind: str, obj) -> list[str]:
    if kind not in _SCHEMAS:
        _SCHEMAS[kind] = D.schema(f"research-{kind}")
    return D.validate(obj, _SCHEMAS[kind], f"sigaba-{kind}-v1")


# -- markers -------------------------------------------------------------------------------------

def task_marker(task_id: str) -> str:
    return f"<!-- sigaba-task-v1 {task_id} -->"


def checkpoint_marker(task_id: str, run_id: str | None, seq: int) -> str:
    return f"<!-- sigaba-checkpoint {task_id} {run_id or '-'} {seq} -->"


CHECKPOINT_MARKER = re.compile(r"<!-- sigaba-checkpoint (\S+) (\S+) (\d+) -->")
TASK_MARKER = re.compile(r"<!-- sigaba-task-v1 (\S+) -->")


# -- digests -------------------------------------------------------------------------------------

def bundle_digest(root: Path) -> str:
    """The digest of an authoring bundle: sha256 over the sorted (path, sha256(content)) of every
    regular file under `root/dag`. Symbolic links make it fail."""
    items = []
    base = root / "dag"
    for p in sorted(base.rglob("*")) if base.is_dir() else []:
        if p.is_symlink():
            raise ValueError(f"{p}: symbolic links are not allowed in a bundle")
        if p.is_file():
            items.append([str(p.relative_to(root)), sha256(p.read_bytes())])
    return sha256(canonical(items))


def files_digest(files: dict[str, bytes]) -> str:
    return sha256(canonical(sorted([k, sha256(v)] for k, v in files.items())))


def slugify(text: str, n: int = 50) -> str:
    s = re.sub(r"[^a-z0-9]+", "-", text.lower()).strip("-")
    return (s[:n].rstrip("-") or "summary")
