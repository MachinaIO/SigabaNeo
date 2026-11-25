"""The DAG: layout, names, hashes, records and status (docs/GITHUB_PLATFORM.md). Standard library
only, and no Lean: CI's trusted jobs (precheck, records, index) use this module without running any
code of a pull request, and so do the verifier (`dag_verify.py`) and the client (`sigaba_neo.py`).

A DAG checkout has this layout:

    env/environments.json   base environments            env/std.json   std releases
    meta/trusted.json       submission mode and lists     meta/assumptions.json   claim metadata
    meta/promotions.json    DAG node -> std declaration
    dag/Definitions/Def_<name>.lean (+ .json)
    dag/Theorems/Thm_<slug>.lean    (+ .json)
    dag/Solutions/<slug>/Sub_<id>.lean (+ .json)
    dag/Notes/<slug>.md

and verification records live on the `records` branch, one JSON object per line in
`<env id>.jsonl`.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass, field
from pathlib import Path

CORE = Path(__file__).resolve().parents[1]
STD = "SigabaNeoStd"

DEF_NAME = r"[A-Za-z_][A-Za-z0-9_]*"
THM_NAME = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
SLUG = r"[A-Za-z_][A-Za-z0-9_']*"
SUB_ID = r"[A-Za-z0-9_]{1,64}"
NOTE_SLUG = r"[a-z0-9][a-z0-9-]{0,79}"
ENV_ID = r"[a-z0-9][a-z0-9.-]{0,63}"

PATHS = {
    "definition": re.compile(rf"dag/Definitions/Def_({DEF_NAME})\.(lean|json)"),
    "theorem": re.compile(rf"dag/Theorems/Thm_({SLUG})\.(lean|json)"),
    "solution": re.compile(rf"dag/Solutions/({SLUG})/Sub_({SUB_ID})\.(lean|json)"),
    "note": re.compile(rf"dag/Notes/({NOTE_SLUG})\.md"),
}

# Modules a DAG file may import, by root (and the core's trusted definitions). Anything else is
# rejected, in particular `Solutions.*`, `SigabaNeo.Platform*` (its commands write files) and
# `Lake`.
IMPORT_ROOTS = {"Init", "Std", "Lean", "Mathlib", "Batteries", "Aesop", "Qq", "Plausible",
                "ProofWidgets", "ImportGraph", "LeanSearchClient", "Cslib", "CslibFrontier", STD,
                "Definitions", "Theorems"}
IMPORT_CORE = ("SigabaNeo.Trusted", "SigabaNeo.Assemble")

ACCEPTED = ("ACCEPTED", "SKETCH_ACCEPTED")
STATUSES = ("OK", "ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "DUPLICATE",
            "LINT", "ERROR")

LIMITS = {"files": 200, "file_bytes": 256 * 1024, "total_bytes": 2 * 1024 * 1024}


def slug(name: str) -> str:
    """Prove2Me's module slug of a theorem name."""
    return name.replace(".", "_")


def imports_of(text: str) -> list[str]:
    """Every imported module of a Lean file (comments, as in `import M -- why`, are not)."""
    out = []
    for line in strip_comments(text).splitlines():
        words = line.split()
        while words and words[0] in ("public", "meta", "private"):
            words = words[1:]
        if words and words[0] == "import":
            out += [w for w in words[1:] if w != "all"]
    return out


def _header_tokens(text: str):
    """The tokens of a Lean file from its start, skipping whitespace and comments: (token, start,
    end) for each, until the end of the file."""
    i, n = 0, len(text)
    while i < n:
        if text[i].isspace():
            i += 1
        elif text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        else:
            j = i
            while j < n and not text[j].isspace() and not text.startswith("--", j) and \
                    not text.startswith("/-", j):
                j += 1
            yield text[i:j], i, j
            i = j


def split_header(text: str) -> tuple[list[str], str]:
    """The imports of a Lean file, and the rest: its header (`module`, `prelude`, and
    `[public] [meta] import [all] M` lines, with any comments) is read token by token, and the rest
    starts right after its last token."""
    imports, end, expect_name = [], 0, False
    for tok, _, stop in _header_tokens(text):
        if expect_name:
            if tok == "all":
                end = stop
                continue
            imports.append(tok)
            end, expect_name = stop, False
        elif tok in ("module", "prelude", "public", "meta", "private"):
            end = stop
        elif tok == "import":
            end, expect_name = stop, True
        else:
            break
    return imports, text[end:]


def import_problem(module: str, disproof: bool = False) -> str | None:
    """Why a DAG file may not import `module`, or None."""
    root = module.split(".")[0]
    if module.startswith(IMPORT_CORE):
        return None
    if root not in IMPORT_ROOTS:
        return f"import {module}: not allowed (allowed roots: {', '.join(sorted(IMPORT_ROOTS))}, " \
               f"{', '.join(IMPORT_CORE)})"
    if root == "Definitions" and not re.fullmatch(rf"Definitions\.Def_{DEF_NAME}", module):
        return f"import {module}: definitions are `Definitions.Def_<name>`"
    if root == "Theorems":
        if not re.fullmatch(rf"Theorems\.Thm_{SLUG}", module):
            return f"import {module}: theorems are `Theorems.Thm_<slug>`"
        if disproof:
            return f"import {module}: a disproof may not import theorems"
    return None


def ends_in_sorry(text: str) -> bool:
    """A theorem node's statement ends in `:= by sorry` (whitespace between the tokens allowed, as
    the assembler's `p2m_apply%` rewriting allows it)."""
    return re.search(r":=\s*by\s+sorry\s*$", text) is not None


def module_of(path: str) -> str:
    """`dag/Theorems/Thm_x.lean` -> `Theorems.Thm_x`."""
    return path.removeprefix("dag/").removesuffix(".lean").replace("/", ".")


def path_of(module: str) -> str:
    return "dag/" + module.replace(".", "/") + ".lean"


def classify(path: str) -> tuple[str, re.Match] | None:
    for kind, rx in PATHS.items():
        if m := rx.fullmatch(path):
            return kind, m
    return None


# -- normalized text and hashes ------------------------------------------------------------------


def strip_comments(text: str) -> str:
    """Lean text without comments (`--` to the end of the line, nested `/- … -/`, docstrings
    included), keeping string and character literals intact."""
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i: j + 1])
            i = j + 1
        elif c == "'" and i + 2 < n and (text[i + 2] == "'" or (text[i + 1] == "\\" and
                                                               i + 3 < n and text[i + 3] == "'")):
            j = i + (3 if text[i + 2] == "'" else 4)
            out.append(text[i:j])
            i = j
        elif text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def normalize(text: str) -> str:
    """The text that identifies a Lean file: comments removed, line endings unified, trailing
    spaces and blank lines dropped. Indentation is kept (it decides the structure of tactic
    blocks), so this never identifies two files that parse differently."""
    lines = strip_comments(text.replace("\r\n", "\n").replace("\r", "\n")).split("\n")
    return "\n".join(l.rstrip() for l in lines if l.strip()) + "\n"


def sha(*parts: str) -> str:
    h = hashlib.sha256()
    for p in parts:
        b = p.encode()
        h.update(f"{len(b)}:".encode() + b)
    return h.hexdigest()


def solution_hash(text: str) -> str:
    """A solution's identity: its normalized text."""
    return sha("sigaba-neo solution v1", normalize(text))


def semantic_id(data: dict) -> str:
    """The semantic ID of a node from `#sigaba_neo_platform_semantic`'s data: a Merkle hash over its
    units (SigabaNeo/Platform/SemanticId.lean)."""
    units: dict = data["units"]
    memo: dict[str, str] = {}

    def unit(key: str) -> str:
        stack, active = [(key, False)], set()
        while stack:                         # iterative post-order (closures can be deep)
            k, children_done = stack.pop()
            if k in memo:
                continue
            u = units[k]
            if children_done:
                active.discard(k)
                memo[k] = sha("unit", k, u["form"], *[f"{r} {memo[r]}" for r in u["refs"]])
                continue
            if k in active:
                raise ValueError(f"the units form a cycle through {k}")
            active.add(k)
            stack.append((k, True))
            stack.extend((r, False) for r in u["refs"] if r not in memo)
        return memo[key]

    root = data["root"]
    return sha(f"sigaba-neo {data['kind']} node v1", root["form"],
               *[f"{r} {unit(r)}" for r in root["refs"]])


def text_fingerprint(core: Path = CORE) -> str:
    """The base environment's fingerprint as the core sees it: toolchain, package pins, and the
    core's own trusted and platform sources (not std, which `std_manifest` covers)."""
    h = hashlib.sha256(f"toolchain {(core / 'lean-toolchain').read_text().strip()}\n".encode())
    for p in json.loads((core / "lake-manifest.json").read_text())["packages"]:
        h.update(f"package {p['name']} {p.get('rev')}\n".encode())
    for f in sorted((core / "SigabaNeo").rglob("*.lean")) + [core / "SigabaNeo.lean"]:
        h.update(f"file {f.relative_to(core)} {sha(normalize(f.read_text()))}\n".encode())
    return h.hexdigest()


def std_manifest(core: Path = CORE) -> dict[str, str]:
    """Every std module and its hash: its normalized text and the hashes of the std modules it
    imports (a Merkle hash, so equal hashes mean equal meaning given the same base environment)."""
    files = {".".join(p.relative_to(core).with_suffix("").parts): p
             for p in sorted((core / STD).rglob("*.lean"))}
    files[STD] = core / f"{STD}.lean"
    texts = {m: p.read_text() for m, p in files.items()}
    deps = {m: sorted({i for i in imports_of(t) if i == STD or i.startswith(STD + ".")})
            for m, t in texts.items()}
    out: dict[str, str] = {}

    def h(m: str, path: tuple = ()) -> str:
        if m in out:
            return out[m]
        if m in path:
            raise ValueError(f"import cycle through {m}")
        if m not in texts:
            raise ValueError(f"{m} is imported but does not exist")
        ds = [f"import {d} {h(d, path + (m,))}" for d in deps[m]]
        out[m] = sha("sigaba-neo std-module v1", m, normalize(texts[m]), *ds)
        return out[m]

    for m in sorted(texts):
        h(m)
    return dict(sorted(out.items()))


def std_closure(modules: list[str], core: Path = CORE) -> list[str]:
    """The std modules `modules` import, transitively (from the core's sources)."""
    seen, todo = set(), [m for m in modules if m == STD or m.startswith(STD + ".")]
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        p = core / (m.replace(".", "/") + ".lean")
        if p.exists():
            todo += [i for i in imports_of(p.read_text()) if i == STD or i.startswith(STD + ".")]
    return sorted(seen)


# -- notes ---------------------------------------------------------------------------------------

REF = re.compile(rf"(theorem|definition):({THM_NAME})|solution:({SLUG})/Sub_({SUB_ID})|"
                 rf"note:({NOTE_SLUG})")


def front_matter(text: str) -> tuple[dict, str]:
    """A note's front matter (a small YAML subset: `key: value` and `key: [a, b]`) and body."""
    if not text.startswith("---\n"):
        raise ValueError("a note starts with front matter between `---` lines")
    end = text.find("\n---\n", 4)
    if end < 0:
        raise ValueError("the front matter is not closed by a `---` line")
    meta: dict = {}
    for line in text[4:end].split("\n"):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        m = re.fullmatch(r"([a-z_]+):\s*(.*)", line.strip())
        if not m:
            raise ValueError(f"front matter line not understood: {line!r}")
        k, v = m.group(1), m.group(2).strip()
        if v.startswith("["):
            if not v.endswith("]"):
                raise ValueError(f"{k}: a list is written `[a, b]` on one line")
            meta[k] = [x.strip().strip("\"'") for x in v[1:-1].split(",") if x.strip()]
        else:
            meta[k] = v.strip("\"'")
    return meta, text[end + 5:]


# -- schemas -------------------------------------------------------------------------------------

SCHEMA_DIR = CORE / "schemas"


def validate(obj, schema: dict, where: str = "$") -> list[str]:
    """The problems of `obj` against a JSON Schema subset (type, required, properties,
    additionalProperties, enum, pattern, maxLength, items, minItems, maxItems, minimum)."""
    errs: list[str] = []
    types = {"object": dict, "array": list, "string": str, "integer": int, "boolean": bool,
             "number": (int, float), "null": type(None)}
    t = schema.get("type")
    if t is not None:
        allowed = t if isinstance(t, list) else [t]
        if not any(isinstance(obj, types[x]) and not (x in ("integer", "number") and
                                                      isinstance(obj, bool)) for x in allowed):
            return [f"{where}: expected {'/'.join(allowed)}"]
    if "enum" in schema and obj not in schema["enum"]:
        errs.append(f"{where}: must be one of {schema['enum']}")
    if isinstance(obj, str):
        if "pattern" in schema and not re.fullmatch(schema["pattern"], obj):
            errs.append(f"{where}: does not match {schema['pattern']}")
        if "maxLength" in schema and len(obj) > schema["maxLength"]:
            errs.append(f"{where}: longer than {schema['maxLength']}")
    if isinstance(obj, (int, float)) and "minimum" in schema and obj < schema["minimum"]:
        errs.append(f"{where}: less than {schema['minimum']}")
    if isinstance(obj, dict):
        for k in schema.get("required", []):
            if k not in obj:
                errs.append(f"{where}: missing `{k}`")
        props = schema.get("properties", {})
        extra = schema.get("additionalProperties", True)
        for k, v in obj.items():
            if k in props:
                errs += validate(v, props[k], f"{where}.{k}")
            elif extra is False:
                errs.append(f"{where}: unknown key `{k}`")
            elif isinstance(extra, dict):
                errs += validate(v, extra, f"{where}.{k}")
    if isinstance(obj, list):
        if "minItems" in schema and len(obj) < schema["minItems"]:
            errs.append(f"{where}: fewer than {schema['minItems']} items")
        if "maxItems" in schema and len(obj) > schema["maxItems"]:
            errs.append(f"{where}: more than {schema['maxItems']} items")
        if "items" in schema:
            for i, v in enumerate(obj):
                errs += validate(v, schema["items"], f"{where}[{i}]")
    return errs


def schema(name: str) -> dict:
    return json.loads((SCHEMA_DIR / f"{name}.schema.json").read_text())


def node_meta_problems(kind: str, path: str, meta: dict | None, m) -> list[str]:
    if meta is None:
        return [f"{path}: its metadata file (.json) is missing"]
    probs = validate(meta, schema(kind), "metadata")
    if probs:
        return probs
    if kind == "definition" and meta["name"] != m.group(1):
        return [f"metadata: `name` is {meta['name']}, but the file is Def_{m.group(1)}"]
    if kind == "theorem" and slug(meta["name"]) != m.group(1):
        return [f"metadata: `name` {meta['name']} has the slug {slug(meta['name'])}, but the file "
                f"is Thm_{m.group(1)}"]
    if kind == "solution" and slug(meta["theorem"]) != m.group(1):
        return [f"metadata: `theorem` {meta['theorem']} has the slug {slug(meta['theorem'])}, "
                f"but the directory is {m.group(1)}"]
    return []


# -- a DAG checkout ------------------------------------------------------------------------------


@dataclass
class Node:
    kind: str                 # definition, theorem, solution, note
    path: str                 # repository path of the .lean or .md file
    name: str                 # definition name, theorem name, solution's theorem name, note slug
    text: str
    meta: dict = field(default_factory=dict)

    @property
    def module(self) -> str | None:
        return module_of(self.path) if self.path.endswith(".lean") else None

    @property
    def imports(self) -> list[str]:
        return imports_of(self.text) if self.path.endswith(".lean") else []


class Dag:
    """A DAG checkout (or any directory with its layout)."""

    def __init__(self, root: Path):
        self.root = Path(root)
        self._nodes: list[Node] | None = None

    def read_json(self, rel: str, default=None):
        p = self.root / rel
        return json.loads(p.read_text()) if p.exists() else default

    def nodes(self) -> list[Node]:
        if self._nodes is None:
            self._nodes = []
            base = self.root / "dag"
            files = sorted(p for p in base.rglob("*") if p.is_file()) if base.is_dir() else []
            for p in files:
                rel = str(p.relative_to(self.root))
                c = classify(rel)
                if c is None or rel.endswith(".json"):
                    continue
                kind, m = c
                text = p.read_text()
                meta = {}
                if kind == "note":
                    try:
                        meta = front_matter(text)[0]
                    except ValueError:
                        meta = {}
                    name = m.group(1)
                else:
                    js = p.with_suffix(".json")
                    meta = json.loads(js.read_text()) if js.exists() else {}
                    name = m.group(1) if kind == "definition" else meta.get(
                        "name" if kind == "theorem" else "theorem", m.group(1))
                self._nodes.append(Node(kind, rel, name, text, meta))
        return self._nodes

    def by_kind(self, kind: str) -> list[Node]:
        return [n for n in self.nodes() if n.kind == kind]

    def definition(self, name: str) -> Node | None:
        return next((n for n in self.by_kind("definition") if n.name == name), None)

    def theorem(self, name: str) -> Node | None:
        return next((n for n in self.by_kind("theorem") if n.name == name), None)

    def theorem_by_slug(self, s: str) -> Node | None:
        return next((n for n in self.by_kind("theorem")
                     if n.path == f"dag/Theorems/Thm_{s}.lean"), None)

    def solutions(self, theorem: Node) -> list[Node]:
        d = theorem.path.removeprefix("dag/Theorems/Thm_").removesuffix(".lean")
        return [n for n in self.by_kind("solution") if n.path.startswith(f"dag/Solutions/{d}/")]

    def theorem_of(self, solution: Node) -> Node | None:
        return self.theorem_by_slug(solution.path.split("/")[2])

    def resolve_ref(self, ref: str) -> Node | None:
        """A note's reference (`theorem:<name>`, `definition:<name>`, `solution:<slug>/Sub_<id>`,
        `note:<slug>`)."""
        m = REF.fullmatch(ref)
        if not m:
            return None
        if m.group(1) == "theorem":
            return self.theorem(m.group(2))
        if m.group(1) == "definition":
            return self.definition(m.group(2))
        if m.group(3):
            p = f"dag/Solutions/{m.group(3)}/Sub_{m.group(4)}.lean"
            return next((n for n in self.by_kind("solution") if n.path == p), None)
        return next((n for n in self.by_kind("note") if n.name == m.group(5)), None)

    def environments(self) -> list[dict]:
        return self.read_json("env/environments.json", {"environments": []})["environments"]

    def environment(self, env_id: str | None = None) -> dict | None:
        envs = self.environments()
        if env_id is None:
            return next((e for e in envs if e.get("state") == "default"), None)
        return next((e for e in envs if e["id"] == env_id), None)

    def std_release(self, tag: str | None) -> dict[str, str]:
        rel = self.read_json("env/std.json", {"releases": {}})["releases"]
        return rel.get(tag, {}) if tag else {}

    def trusted(self) -> dict:
        return self.read_json("meta/trusted.json", {"mode": "allowlist", "accept": [],
                                                     "automerge": []})


# -- records and status --------------------------------------------------------------------------


def read_records(d: Path | None) -> dict[str, list[dict]]:
    """env id -> its records, in order."""
    out: dict[str, list[dict]] = {}
    if d is None or not Path(d).is_dir():
        return out
    for p in sorted(Path(d).glob("*.jsonl")):
        out[p.stem] = [json.loads(l) for l in p.read_text().splitlines() if l.strip()]
    return out


def id_record(r: dict, kind: tuple[str, ...] = ("definition", "theorem")) -> bool:
    """A record that establishes a node's semantic ID: a definition or theorem that passed (`OK`).
    A failed attempt (a `DUPLICATE`, say) may carry an ID, but establishes nothing."""
    return r.get("kind") in kind and bool(r.get("id")) and r.get("status") == "OK"


def compatible(stds: list[dict[str, str]]) -> dict[str, tuple[str, str]]:
    """The std modules on which `stds` (records' `std` fields) disagree: module -> two hashes.
    Records that agree can be combined in one proof; the others are `INCOMPATIBLE`."""
    seen: dict[str, str] = {}
    bad: dict[str, tuple[str, str]] = {}
    for s in stds:
        for m, h in s.items():
            if m in seen and seen[m] != h:
                bad[m] = (seen[m], h)
            seen.setdefault(m, h)
    return bad


@dataclass
class EnvStatus:
    """The derived state of the DAG in one environment, under its std release."""
    env: str
    theorems: dict[str, dict]            # theorem name -> {status, solutions, id, drifted}
    solutions: dict[str, dict]           # solution path -> its valid record
    stale: list[str]                     # solutions verified only under other std hashes
    needs_port: list[str]                # solutions verified in other environments only


def status(dag: Dag, records: dict[str, list[dict]], env: dict) -> EnvStatus:
    """Statuses in `env`: a solution counts if it has an accepted record there whose std modules
    have the hashes of the environment's std release; a theorem is `Proved` when one of its counting
    proofs uses only `Proved` theorems (a cycle proves nothing), `Disproved` when a disproof counts,
    and `Open` otherwise. A theorem whose semantic ID there differs from the ID recorded when it was
    introduced is `Drifted`, and one with no `OK` record of its ID there is `Unchecked`: no
    solution counts for either, nor for the theorems that use them."""
    eid = env["id"]
    release = dag.std_release(env.get("std"))
    recs = records.get(eid, [])
    # A theorem's own ID is the one recorded when it was introduced: the earliest record that is
    # not a re-verification (the order of environments' files plays no part).
    # If the earliest such records disagree (the same time, other IDs), the baseline is ambiguous
    # and the theorem counts as drifted everywhere.
    first: dict[str, tuple[tuple, set]] = {}
    for rs in records.values():
        for r in rs:
            if id_record(r, ("theorem",)):
                key = (r.get("author") == "reverify", r.get("time") or "~")
                if r["name"] not in first or key < first[r["name"]][0]:
                    first[r["name"]] = (key, {r["id"]})
                elif key == first[r["name"]][0]:
                    first[r["name"]][1].add(r["id"])
    ambiguous = {n for n, (_, ids) in first.items() if len(ids) > 1}
    first_ids = {n: next(iter(ids)) for n, (_, ids) in first.items() if len(ids) == 1}
    env_ids = {r["name"]: r["id"] for r in recs if id_record(r, ("theorem",))}
    valid: dict[str, dict] = {}
    stale: list[str] = []
    for r in recs:
        if r.get("kind") != "solution" or r.get("status") not in ACCEPTED:
            continue
        # Every std module it used must have the same hash in the environment's release; with no
        # release (or none listed), a proof that used std does not count.
        mismatch = [m for m, h in (r.get("std") or {}).items() if release.get(m) != h]
        if mismatch:
            stale.append(r["path"])
            continue
        valid[r["path"]] = r
    stale = sorted(set(stale) - set(valid))
    others = {r["path"] for e, rs in records.items() if e != eid for r in rs
              if r.get("kind") == "solution" and r.get("status") in ACCEPTED}
    needs_port = sorted(p for p in others - set(valid) - set(stale)
                        if (dag.root / p).exists())
    thms = {t.name: t for t in dag.by_kind("theorem")}
    by_theorem: dict[str, list[dict]] = {}
    for p, r in valid.items():
        by_theorem.setdefault(r["theorem"], []).append(r)
    drifted = {n for n in thms if n in ambiguous or
               (n in env_ids and n in first_ids and env_ids[n] != first_ids[n])}
    # A theorem's proofs count only once its statement is established here: an `OK` record of
    # its semantic ID in this environment, which is its baseline (not drifted).
    checked = {n for n in thms if n in env_ids and n not in drifted}
    memo: dict[str, str] = {}

    def proved(name: str, visiting: frozenset) -> bool:
        if name in memo:
            return memo[name] == "Proved"
        if name in visiting or name not in checked:
            return False
        ok = any(r.get("proof_type", "prove") == "prove" and
                 all(proved(u, visiting | {name}) for u in r.get("uses", []))
                 for r in by_theorem.get(name, []))
        if not visiting:
            memo[name] = "Proved" if ok else memo.get(name, "Open")
        return ok

    out: dict[str, dict] = {}
    for name in sorted(thms):
        rs = by_theorem.get(name, [])
        st = "Open"
        if name in drifted:
            st = "Drifted"
        elif name not in checked:
            st = "Unchecked"
        elif any(r.get("proof_type") == "disprove" for r in rs):
            st = "Disproved"
        elif proved(name, frozenset()):
            st = "Proved"
        out[name] = {"status": st, "path": thms[name].path,
                     "solutions": sorted(r["path"] for r in rs),
                     "id": env_ids.get(name), "drifted": name in drifted}
    return EnvStatus(eid, out, valid, stale, needs_port)


def open_leaves(st: EnvStatus, name: str) -> list[str]:
    """The `Open` theorems below `name`: through its sketches, those with no counting proof."""
    seen, leaves, todo = set(), [], [name]
    by_theorem: dict[str, list[dict]] = {}
    for r in st.solutions.values():
        by_theorem.setdefault(r["theorem"], []).append(r)
    while todo:
        t = todo.pop()
        if t in seen:
            continue
        seen.add(t)
        info = st.theorems.get(t)
        if info is None or info["status"] in ("Proved", "Disproved"):
            continue
        rs = by_theorem.get(t, [])
        if not rs:
            leaves.append(t)
        for r in rs:
            todo += r.get("uses", [])
    return sorted(leaves)


def in_degrees(dag: Dag) -> dict[str, int]:
    """How many solutions, theorems and definitions import each theorem or definition module."""
    deg: dict[str, int] = {}
    for n in dag.nodes():
        for m in set(n.imports):
            if m.startswith(("Theorems.", "Definitions.")):
                deg[m] = deg.get(m, 0) + 1
    return deg
