"""The Prove2Me-compatible server, with the core's environment (docs/PLATFORM.md). Run by the
server's operator. Untrusted, standard library only.

    python3 p2m_server.py serve --config server.json
    python3 p2m_server.py workspace ../prove2me_workspace
    python3 p2m_server.py sync --config server.json [--match REGEX] [--limit N]
    python3 p2m_server.py annotate --config server.json NAME --tag well-established

    server.json: {"dataDir": "server-data", "listen": "127.0.0.1:8090", "core": "..",
                  "apiKeys": {"<api key>": "<username>"},
                  "formalpedia": {"interval": 86400, "match": "...", "limit": 1000}}

`serve` serves the part of Prove2Me's API that agents (following `prove2me_workspace/SKILL.md`)
and submitters (`sigaba_neo.py`) use: theorems, definitions, publish jobs, proof submissions,
decompositions. Its one environment is the core's toolchain and packages, cslib-frontier
included. The statuses it reports come from the untrusted commands of `SigabaNeo.Platform`;
submitters check every proof themselves.

`sync` adds what changed in Formalpedia (Prove2Me's daily export, `formalpedia.py`) since the last
sync: new or changed definitions and theorems, and their accepted solutions. Each one goes through
the usual jobs and checks in this environment. With `formalpedia.interval` in the configuration,
`serve` also syncs on its own every `interval` seconds; run `sync` only while not serving, since
both use the same library.

`workspace` writes the local Lake files of Prove2Me's agent workspace (`lakefile.lean`,
`lean-toolchain`, `lake-manifest.json`, which the workspace ignores) so that it builds with the
server's environment.

IDs are content IDs: SHA-256 of the environment, the kind and name, the file's canonical syntax
tree (`#sigaba_neo_platform_canon`: no whitespace or comments), and the IDs of the platform modules
it imports (docs/PLATFORM.md, "IDs"). The same content gets the same ID; resubmitting it returns
the existing record.

All published modules live in one Lake project, the *library* (`<dataDir>/library`), with
Prove2Me's layout: `Definitions/Def_<name>.lean`, `Theorems/Thm_<slug>.lean`. A submission is
compiled as `Solutions/Sub_<id>.lean` and removed after it is checked (its text stays in the
database). One worker thread does all the compiling, in order.
"""

from __future__ import annotations

import argparse
import email.parser
import hashlib
import email.policy
import json
import queue
import re
import sqlite3
import threading
import time
import traceback
import uuid
from dataclasses import dataclass
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

import formalpedia

import os
import subprocess

CORE = Path(__file__).resolve().parents[1]


def slug(name: str) -> str:
    return name.replace(".", "_")


def imports_of(text: str) -> list[str]:
    """Every imported module of a Lean file."""
    out = []
    for line in text.splitlines():
        words = line.split()
        while words and words[0] in ("public", "meta", "private"):
            words = words[1:]
        if words and words[0] == "import":
            out += [w for w in words[1:] if w != "all"]
    return out


def tail(s: str, n: int = 60) -> str:
    return "\n".join(s.splitlines()[-n:])


def errors(log: str, n: int = 40) -> str:
    lines = [l for l in log.splitlines() if l.startswith("error:") and "build failed" not in l]
    return "\n".join(lines[:n]) if lines else tail(log)


@dataclass
class Core:
    """A built checkout of the core."""

    root: Path

    @property
    def toolchain(self) -> str:
        return (self.root / "lean-toolchain").read_text().strip()

    @property
    def packages(self) -> dict[str, str]:
        m = json.loads((self.root / "lake-manifest.json").read_text())
        return {p["name"].replace("«", "").replace("»", ""): p["rev"]
                for p in m["packages"] if p.get("type") == "git"}


def environment_id(core: Core) -> str:
    """The environment's fingerprint: the toolchain, the core's package pins, and the core's own
    Lean sources (which the platform's commands, and any file importing the core, depend on)."""
    h = hashlib.sha256(f"sigaba-neo-platform environment v1\ntoolchain {core.toolchain}\n".encode())
    for n, r in sorted(core.packages.items()):
        h.update(f"package {n} {r}\n".encode())
    files = sorted((core.root / "SigabaNeo").rglob("*.lean")) + [core.root / "SigabaNeo.lean"]
    for f in files:
        h.update(f"file {f.relative_to(core.root)} {hashlib.sha256(f.read_bytes()).hexdigest()}\n"
                 .encode())
    return h.hexdigest()


def normalize_text(text: str) -> str:
    """Line endings unified, trailing spaces and trailing blank lines dropped (meaning-preserving
    in Lean; used only when a file cannot be parsed, e.g. an unknown import)."""
    lines = [l.rstrip() for l in text.replace("\r\n", "\n").replace("\r", "\n").split("\n")]
    return "\n".join(lines).rstrip("\n") + "\n"


LIBS = ("Definitions", "Theorems", "Solutions")


class Project:
    """A Lake project with Prove2Me's layout that requires the core (and links its built packages,
    so that it never fetches or rebuilds Mathlib)."""

    def __init__(self, d: Path, core: Core, timeout: float | None = None, lean_lakefile: bool = False):
        self.dir, self.core, self.timeout = d, core, timeout
        d.mkdir(parents=True, exist_ok=True)
        if lean_lakefile:
            (d / "lakefile.lean").write_text(
                "import Lake\nopen Lake DSL\n\npackage «workspace» where\n"
                "  leanOptions := #[⟨`autoImplicit, false⟩]\n\n"
                f"require SigabaNeo from {json.dumps(str(core.root))}\n\n" +
                "".join(("@[default_target]\n" if lib == LIBS[-1] else "") +
                        f"lean_lib «{lib}» where\n\n" for lib in LIBS))
        else:
            (d / "lakefile.toml").write_text(
                'name = "library"\nleanOptions = { autoImplicit = false }\n\n[[require]]\n'
                f'name = "SigabaNeo"\npath = {json.dumps(str(core.root))}\n' +
                "".join(f'\n[[lean_lib]]\nname = "{lib}"\n' for lib in LIBS))
        m = json.loads((core.root / "lake-manifest.json").read_text())
        m.update(name="workspace", packages=[
            {"type": "path", "scope": "", "name": "SigabaNeo", "manifestFile": "lake-manifest.json",
             "inherited": False, "dir": str(core.root), "configFile": "lakefile.toml"},
            *[dict(p, inherited=True) for p in m["packages"]]])
        (d / "lake-manifest.json").write_text(json.dumps(m, indent=1) + "\n")
        (d / "lean-toolchain").write_text(core.toolchain + "\n")
        (d / ".lake" / "packages").mkdir(parents=True, exist_ok=True)
        for p in (core.root / ".lake" / "packages").iterdir():
            if not (dst := d / ".lake" / "packages" / p.name).exists():
                dst.symlink_to(p)

    def run(self, args: list[str], stdin: str | None = None) -> subprocess.CompletedProcess:
        env = {k: v for k, v in os.environ.items() if k not in ("LEAN_PATH", "LEAN_SRC_PATH")}
        return subprocess.run(args, cwd=self.dir, env=env, input=stdin, text=True,
                              capture_output=True, timeout=self.timeout)

    def build(self, targets: list[str]) -> subprocess.CompletedProcess:
        return self.run(["lake", "build", *targets])

    def lean(self, source: str) -> subprocess.CompletedProcess:
        return self.run(["lake", "env", "lean", "--stdin"], stdin=source)

VERSION = "sigaba-neo-platform 0.1"
MAX_BODY = 8 * 1024 * 1024
NAME_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*")
DEF_NAME_RE = re.compile(r"[a-zA-Z_][a-zA-Z0-9_]*")
# Prove2Me's discussion tags (prove2me_workspace/references/communicate.md).
COMMENT_TAGS = {"strategy", "reference", "attempt", "typo", "proof_gap", "missing_hypothesis",
                "counterexample", "strengthened", "generalized", "sharpness", "converse",
                "simplified_proof", "new_proof", "unfaithful"}
P2M_REF_RE = re.compile(r"\(p2m:(theorem|definition|sketch|solution)/([0-9a-fA-F-]{36}|[0-9a-f]{64})\)")
# The cards of a Sigaba-Neo claim (python/sigaba_neo.py).
CLAIM_RE = re.compile(r"SigabaNeo\.Claim_[0-9a-f]{16}\.(prove|refute)")
STATUSES = ("ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "ERROR", "PENDING")

SCHEMA = """
CREATE TABLE IF NOT EXISTS theorems (
  id TEXT PRIMARY KEY, name TEXT UNIQUE NOT NULL, slug TEXT UNIQUE NOT NULL, title TEXT,
  status TEXT NOT NULL, preamble TEXT NOT NULL, statement TEXT NOT NULL, nl TEXT, source TEXT,
  tags TEXT NOT NULL, created_by TEXT NOT NULL, created_at REAL NOT NULL, deprecated_at REAL);
CREATE TABLE IF NOT EXISTS definitions (
  id TEXT PRIMARY KEY, name TEXT UNIQUE NOT NULL, title TEXT, code TEXT NOT NULL, nl TEXT,
  source TEXT, tags TEXT NOT NULL, created_by TEXT NOT NULL, created_at REAL NOT NULL,
  deprecated_at REAL);
CREATE TABLE IF NOT EXISTS jobs (
  id TEXT PRIMARY KEY, kind TEXT NOT NULL, name TEXT NOT NULL, user TEXT NOT NULL,
  status TEXT NOT NULL, error TEXT NOT NULL, payload TEXT NOT NULL, theorem_id TEXT,
  definition_id TEXT, created_at REAL NOT NULL, updated_at REAL NOT NULL);
CREATE TABLE IF NOT EXISTS submissions (
  id TEXT PRIMARY KEY, theorem_id TEXT NOT NULL, user TEXT NOT NULL, status TEXT NOT NULL,
  proof_type TEXT NOT NULL, content TEXT NOT NULL, explanation TEXT, error TEXT NOT NULL,
  created_at REAL NOT NULL, updated_at REAL NOT NULL, accepted_at REAL, deprecated_at REAL);
CREATE TABLE IF NOT EXISTS children (
  submission_id TEXT NOT NULL, ordinal INTEGER NOT NULL, theorem_id TEXT, definition_id TEXT);
CREATE TABLE IF NOT EXISTS aliases (alias TEXT PRIMARY KEY, target TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS formalpedia (
  env TEXT NOT NULL, path TEXT NOT NULL, blob TEXT NOT NULL, kind TEXT NOT NULL, name TEXT NOT NULL,
  ref TEXT, state TEXT NOT NULL, updated_at REAL NOT NULL, PRIMARY KEY (env, path));
CREATE TABLE IF NOT EXISTS comments (
  id TEXT PRIMARY KEY, mission_id TEXT NOT NULL, parent_id TEXT, tags TEXT NOT NULL,
  author TEXT NOT NULL, body TEXT NOT NULL, refs TEXT NOT NULL, deleted INTEGER NOT NULL,
  created_at REAL NOT NULL, updated_at REAL);
CREATE TABLE IF NOT EXISTS assumption_meta (
  theorem_id TEXT PRIMARY KEY, tags TEXT NOT NULL, proposed_year INTEGER, source TEXT);
"""


class ApiError(Exception):
    def __init__(self, status: int, message: str):
        super().__init__(message)
        self.status = status
        self.body = {"error": message}


def iso(t: float | None) -> str | None:
    return None if t is None else time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(t))


@dataclass
class PlatformConfig:
    data_dir: Path
    core: Core
    api_keys: dict[str, str]                 # api key (also the access token) -> username
    lake_timeout: float = 1800
    max_pending: int = 100


class Platform:
    def __init__(self, cfg: PlatformConfig):
        self.cfg = cfg
        cfg.data_dir.mkdir(parents=True, exist_ok=True)
        self.db = sqlite3.connect(cfg.data_dir / "platform.sqlite", check_same_thread=False)
        self.db.row_factory = sqlite3.Row
        self.db.executescript(SCHEMA)
        self.lock = threading.RLock()
        self.tasks: queue.Queue[tuple[str, str]] = queue.Queue()
        self.stop = threading.Event()
        self.lib = Project(cfg.data_dir / "library", cfg.core, timeout=cfg.lake_timeout)
        self.env_id = environment_id(cfg.core)
        for job in self.rows("SELECT id FROM jobs WHERE status IN ('PENDING','COMPILING')"):
            self.tasks.put(("job", job["id"]))
        for sub in self.rows("SELECT id FROM submissions WHERE status = 'PENDING'"):
            self.tasks.put(("submission", sub["id"]))

    @property
    def env(self) -> str:
        return self.cfg.core.packages.get("mathlib", "")

    def environment_json(self) -> dict:
        return {"mathlib_rev": self.env, "toolchain": self.cfg.core.toolchain,
                "display_name": f"Sigaba-Neo core (cslib-frontier "
                                f"{self.cfg.core.packages.get('cslib-frontier', '?')[:7]}, "
                                f"{self.cfg.core.toolchain})",
                "is_default": True, "packages": self.cfg.core.packages}

    # -- database helpers ---------------------------------------------------------------------

    def rows(self, sql: str, *args) -> list[sqlite3.Row]:
        with self.lock:
            return self.db.execute(sql, args).fetchall()

    def row(self, sql: str, *args) -> sqlite3.Row | None:
        r = self.rows(sql, *args)
        return r[0] if r else None

    def exec(self, sql: str, *args) -> None:
        with self.lock:
            self.db.execute(sql, args)
            self.db.commit()

    # -- JSON views ---------------------------------------------------------------------------

    def theorem_json(self, t: sqlite3.Row, compact: bool = False) -> dict:
        out = {"theorem_id": t["id"], "theorem_name": t["name"], "theorem_title": t["title"],
               "status": t["status"], "preamble": t["preamble"], "formal_statement": t["statement"]}
        if compact:
            return out
        return {**out, "natural_language_statement": t["nl"], "source": t["source"],
                "tags": json.loads(t["tags"]), "created_by": t["created_by"],
                "created_by_username": t["created_by"], "created_at": iso(t["created_at"]),
                "vote_count": 0, "deprecated_at": iso(t["deprecated_at"]), "deprecated_by": None,
                "visibility": "public", "mathlib_rev": self.env,
                "env_display_name": self.environment_json()["display_name"], "audits": []}

    def definition_json(self, d: sqlite3.Row, compact: bool = False) -> dict:
        out = {"definition_id": d["id"], "definition_name": d["name"],
               "definition_title": d["title"], "definition": d["code"]}
        if compact:
            return out
        return {**out, "natural_language_statement": d["nl"], "source": d["source"],
                "tags": json.loads(d["tags"]), "created_by": d["created_by"],
                "created_at": iso(d["created_at"]), "deprecated_at": iso(d["deprecated_at"]),
                "visibility": "public", "mathlib_rev": self.env}

    def submission_json(self, s: sqlite3.Row) -> dict:
        return {"id": s["id"], "theorem_id": s["theorem_id"], "user_id": s["user"],
                "username": s["user"], "status": s["status"], "proof_type": s["proof_type"],
                "error_message": s["error"], "file_path": f"{s['theorem_id']}/{s['id']}.lean",
                "created_at": iso(s["created_at"]), "updated_at": iso(s["updated_at"]),
                "accepted_at": iso(s["accepted_at"]), "vote_count": 0,
                "explanation": s["explanation"], "deprecated_at": iso(s["deprecated_at"])}

    def job_json(self, j: sqlite3.Row) -> dict:
        p = json.loads(j["payload"])
        out = {"id": j["id"], "kind": j["kind"], "status": j["status"],
               "error_message": j["error"], "visibility": "public",
               "created_at": iso(j["created_at"]), "updated_at": iso(j["updated_at"])}
        if j["kind"] == "problem":
            out.update(theorem_name=j["name"], theorem_id=j["theorem_id"],
                       theorem_title=p.get("theorem_title"),
                       formal_statement=p.get("formal_statement"),
                       natural_language_statement=p.get("natural_language_statement"),
                       definitions=p.get("preamble", ""), source=p.get("source"),
                       tags=p.get("tags", []))
        else:
            out.update(definition_name=j["name"], definition_id=j["definition_id"],
                       definition_title=p.get("definition_title"),
                       definitions=p.get("definition", ""), source=p.get("source"),
                       tags=p.get("tags", []))
        return out

    # -- search -------------------------------------------------------------------------------

    @staticmethod
    def matches(q: str | None, *fields) -> bool:
        if not q:
            return True
        text = " ".join(f or "" for f in fields).lower()
        return all(w in text for w in q.lower().split())

    def check_env(self, env: str | None) -> bool:
        return env in (None, "", "all", self.env)

    def search_theorems(self, q: dict) -> dict:
        one = lambda k: (q.get(k) or [None])[0]  # noqa: E731
        if not self.check_env(one("env")):
            return {"theorems": [], "total": 0}
        compact = one("view") == "compact"
        rows = self.rows("SELECT * FROM theorems ORDER BY created_at DESC")
        if one("include_deprecated") != "true":
            rows = [t for t in rows if t["deprecated_at"] is None]
        if one("status"):
            rows = [t for t in rows if t["status"] == one("status")]
        if one("theorem_name"):
            rows = [t for t in rows if t["name"] == one("theorem_name")]
        if one("tags"):
            want = set(one("tags").split(","))
            rows = [t for t in rows if want <= set(json.loads(t["tags"]))]
        queries = q.get("q") or [None]
        limit, offset = int(one("limit") or 50), int(one("offset") or 0)
        if len(queries) > 1:
            searches, seen = [], {}
            for s in queries:
                hits = [t for t in rows if self.matches(s, t["name"], t["title"], t["nl"], t["tags"])]
                searches.append({"q": s, "total": len(hits),
                                 "ids": [t["id"] for t in hits[offset:offset + limit]]})
                for t in hits[offset:offset + limit]:
                    seen[t["id"]] = t
            return {"searches": searches,
                    "theorems": [self.theorem_json(t, one("view") != "full") for t in seen.values()]}
        hits = [t for t in rows if self.matches(queries[0], t["name"], t["title"], t["nl"], t["tags"])]
        return {"theorems": [self.theorem_json(t, compact) for t in hits[offset:offset + limit]],
                "total": len(hits)}

    def search_definitions(self, q: dict) -> dict:
        one = lambda k: (q.get(k) or [None])[0]  # noqa: E731
        if not self.check_env(one("env")):
            return {"definitions": [], "total": 0}
        compact = one("view") == "compact"
        rows = self.rows("SELECT * FROM definitions ORDER BY created_at DESC")
        if one("include_deprecated") != "true":
            rows = [d for d in rows if d["deprecated_at"] is None]
        hits = [d for d in rows if self.matches(one("q"), d["name"], d["title"], d["nl"], d["tags"])]
        limit, offset = int(one("limit") or 50), int(one("offset") or 0)
        return {"definitions": [self.definition_json(d, compact) for d in hits[offset:offset + limit]],
                "total": len(hits)}

    # -- imports ------------------------------------------------------------------------------

    def import_problems(self, text: str, allow_theorems: bool = True) -> tuple[list[str], list, list]:
        """Problems with the platform imports of a file; the theorems and definitions it imports."""
        problems, thms, defs = [], [], []
        for m in imports_of(text):
            root = m.split(".")[0]
            if root in ("Solutions", "Solution"):
                problems.append(f"import {m}: modules under {root} cannot be imported")
            elif m.startswith("Theorems."):
                t = self.row("SELECT * FROM theorems WHERE slug = ?", m[len("Theorems.Thm_"):]) \
                    if m.startswith("Theorems.Thm_") else None
                if t is None:
                    problems.append(f"unknown import: {m}. Call POST /api/v1/submit-problem first.")
                elif not allow_theorems:
                    problems.append(f"import {m}: a disproof may not import platform theorems")
                else:
                    thms.append(t)
            elif m.startswith("Definitions."):
                d = self.row("SELECT * FROM definitions WHERE name = ?", m[len("Definitions.Def_"):]) \
                    if m.startswith("Definitions.Def_") else None
                if d is None:
                    problems.append(f"unknown import: {m}. Call POST /api/v1/submit-definition first.")
                else:
                    defs.append(d)
        return problems, thms, defs

    # -- publishing ---------------------------------------------------------------------------

    def name_taken(self, kind: str, name: str) -> bool:
        """Another theorem has this module slug, or a job for this name is pending. (A published
        theorem or definition of the same name may be resubmitted: the job publishes nothing new
        if the content is the same, and fails otherwise.)"""
        if kind == "problem":
            s = slug(name)
            if self.row("SELECT 1 FROM theorems WHERE slug = ? AND name != ?", s, name):
                return True
            pend = self.rows("SELECT name FROM jobs WHERE kind='problem' AND status IN "
                             "('PENDING','COMPILING')")
            return any(slug(p["name"]) == s for p in pend)
        return bool(self.row("SELECT 1 FROM jobs WHERE kind='definition' AND name = ? AND status IN "
                             "('PENDING','COMPILING')", name))

    # -- content IDs --------------------------------------------------------------------------

    def content_id(self, kind: str, *parts: str) -> str:
        """SHA-256 of the environment, the kind, and the parts (length-prefixed)."""
        h = hashlib.sha256(f"sigaba-neo-platform {kind} v1\nenvironment {self.env_id}\n".encode())
        for part in parts:
            b = part.encode()
            h.update(f"{len(b)}:".encode() + b)
        return h.hexdigest()

    def canon(self, rel: str) -> str | None:
        """The canonical form of a library file (`#sigaba_neo_platform_canon`): its syntax tree, without
        whitespace or comments."""
        out = self.lib.dir / "platform-canon.txt"
        out.unlink(missing_ok=True)
        self.lib.lean(f'import SigabaNeo.Platform\n#sigaba_neo_platform_canon "{rel}" "platform-canon.txt"\n')
        return out.read_text() if out.exists() else None

    def module_id(self, kind: str, name: str, rel: str, text: str) -> str:
        """The content ID of a library file: environment, kind, name, canonical form, and the IDs of
        the platform modules it imports."""
        _, thms, defs = self.import_problems(text)
        deps = sorted([f"theorem {t['id']}" for t in thms] + [f"definition {d['id']}" for d in defs])
        c = self.canon(rel)
        body = ("canon\n" + c) if c is not None else ("text\n" + normalize_text(text))
        return self.content_id(kind, name, body, *deps)

    def submission_row(self, sid: str) -> sqlite3.Row | None:
        """A submission by its content ID or by the request ID `/verify` returned."""
        r = self.row("SELECT * FROM submissions WHERE id = ?", sid)
        if r is None:
            a = self.row("SELECT target FROM aliases WHERE alias = ?", sid)
            if a is not None:
                r = self.row("SELECT * FROM submissions WHERE id = ?", a["target"])
        return r

    def pending_count(self, user: str) -> int:
        return len(self.rows("SELECT 1 FROM jobs WHERE user = ? AND status IN ('PENDING','COMPILING')",
                             user)) + \
            len(self.rows("SELECT 1 FROM submissions WHERE user = ? AND status = 'PENDING'", user))

    def new_job(self, user: str, kind: str, name: str, payload: dict) -> str:
        jid = str(uuid.uuid4())
        now = time.time()
        self.exec("INSERT INTO jobs VALUES (?,?,?,?,?,?,?,?,?,?,?)", jid, kind, name, user,
                  "PENDING", "", json.dumps(payload), None, None, now, now)
        self.tasks.put(("job", jid))
        return jid

    def submit_problems(self, user: str, body: dict) -> tuple[int, dict]:
        problems = body.get("problems") if isinstance(body.get("problems"), list) else [body]
        if not self.check_env(body.get("env")):
            raise ApiError(400, f"unknown environment {body.get('env')!r}; GET /api/v1/environments")
        jobs, errs = [], []
        for p in problems:
            name = p.get("theorem_name") if isinstance(p, dict) else None
            why = None
            if not isinstance(name, str) or not NAME_RE.fullmatch(name):
                why = "`theorem_name` must be a Lean identifier"
            elif not all(isinstance(p.get(k), str) and p.get(k) for k in
                         ("theorem_title", "formal_statement", "natural_language_statement")):
                why = "`theorem_title`, `formal_statement` and `natural_language_statement` are required"
            elif not p["formal_statement"].rstrip().endswith(":= by sorry"):
                why = "`formal_statement` must end with `:= by sorry`"
            elif self.name_taken("problem", name):
                why = f"the theorem name {name} (or its module Thm_{slug(name)}) is taken"
            elif self.pending_count(user) >= self.cfg.max_pending:
                raise ApiError(429, "too many pending jobs; poll them first")
            if why:
                errs.append({"name": name, "error": why})
                continue
            jobs.append({"job_id": self.new_job(user, "problem", name, p), "name": name})
        return 202, {"jobs": jobs, "errors": errs,
                     "message": f"{len(jobs)}/{len(problems)} problem(s) queued. Poll GET "
                                "/api/v1/publish-jobs/{job_id} until status is PUBLISHED, FAILED, "
                                "or ERROR."}

    def submit_definition(self, user: str, body: dict) -> tuple[int, dict]:
        name = body.get("definition_name")
        if not self.check_env(body.get("env")):
            raise ApiError(400, f"unknown environment {body.get('env')!r}")
        if not isinstance(name, str) or not DEF_NAME_RE.fullmatch(name):
            raise ApiError(400, "`definition_name` must match [a-zA-Z_][a-zA-Z0-9_]*")
        if not all(isinstance(body.get(k), str) and body.get(k) for k in
                   ("definition_title", "definition")):
            raise ApiError(400, "`definition_title` and `definition` are required")
        if self.name_taken("definition", name):
            raise ApiError(409, f"the definition name {name} is taken")
        if self.pending_count(user) >= self.cfg.max_pending:
            raise ApiError(429, "too many pending jobs; poll them first")
        jid = self.new_job(user, "definition", name, body)
        return 202, {"job_id": jid, "definition_name": name, "status": "PENDING",
                     "message": f"Definition queued. Poll GET /api/v1/publish-jobs/{jid} until "
                                "status is PUBLISHED, FAILED, or ERROR."}

    # -- proofs -------------------------------------------------------------------------------

    def verify(self, user: str, fields: dict, limit: bool = True) -> tuple[int, dict]:
        tid = fields.get("theorem_id")
        content = fields.get("file")
        kind = fields.get("proof_type") or "prove"
        t = self.row("SELECT * FROM theorems WHERE id = ?", tid)
        if t is None:
            raise ApiError(404, "no theorem with that id")
        if not isinstance(content, str) or not content.strip():
            raise ApiError(400, "`file` (the solution.lean) is required")
        if kind not in ("prove", "disprove"):
            raise ApiError(400, "`proof_type` must be `prove` or `disprove`")
        if limit and self.pending_count(user) >= self.cfg.max_pending:
            raise ApiError(429, "too many pending submissions; poll them first")
        sid = str(uuid.uuid4())
        now = time.time()
        self.exec("INSERT INTO submissions VALUES (?,?,?,?,?,?,?,?,?,?,?,?)", sid, tid, user,
                  "PENDING", kind, content, fields.get("explanation"), "", now, now, None, None)
        self.tasks.put(("submission", sid))
        return 202, {"submission_id": sid, "status": "PENDING",
                     "message": "Proof submitted for verification. Poll GET "
                                f"/api/v1/verify?submission_id={sid} for results."}

    def poll(self, sid: str) -> dict:
        s = self.submission_row(sid)
        if s is None:
            raise ApiError(404, "no submission with that id")
        return {"id": s["id"], "theorem_id": s["theorem_id"], "status": s["status"],
                "error_message": s["error"]}

    def decompositions(self, tid: str) -> dict:
        out = []
        for s in self.rows("SELECT * FROM submissions WHERE theorem_id = ? AND status IN "
                           "('ACCEPTED','SKETCH_ACCEPTED') ORDER BY created_at", tid):
            kids = []
            for c in self.rows("SELECT * FROM children WHERE submission_id = ? ORDER BY ordinal",
                               s["id"]):
                if c["theorem_id"]:
                    t = self.row("SELECT * FROM theorems WHERE id = ?", c["theorem_id"])
                    kids.append({"theorem_id": t["id"], "theorem_name": t["name"],
                                 "status": t["status"], "ordinal": c["ordinal"],
                                 "deprecated_at": iso(t["deprecated_at"]), "mathlib_rev": self.env})
                else:
                    d = self.row("SELECT * FROM definitions WHERE id = ?", c["definition_id"])
                    kids.append({"definition_id": d["id"], "definition_name": d["name"],
                                 "ordinal": c["ordinal"], "deprecated_at": iso(d["deprecated_at"]),
                                 "mathlib_rev": self.env})
            if any("theorem_id" in k for k in kids):
                out.append({"submission_id": s["id"], "children": kids})
        return {"decompositions": out}

    def assumptions(self) -> dict:
        """Every published claim (`SigabaNeo.Claim_<d>.prove`), usable as another claim's
        hypothesis, with the operator's metadata and the refutation attempts on its refute card
        (accepted sketches)."""
        out = []
        for t in self.rows("SELECT * FROM theorems WHERE name LIKE 'SigabaNeo.Claim_%.prove' "
                           "AND deprecated_at IS NULL ORDER BY created_at"):
            if not CLAIM_RE.fullmatch(t["name"]):
                continue
            r = self.row("SELECT * FROM theorems WHERE name = ?", t["name"][:-len("prove")] + "refute")
            meta = self.row("SELECT * FROM assumption_meta WHERE theorem_id = ?", t["id"])
            sketches = 0 if r is None else self.row(
                "SELECT COUNT(*) AS n FROM submissions WHERE theorem_id = ? AND status = "
                "'SKETCH_ACCEPTED'", r["id"])["n"]
            out.append({**self.theorem_json(t, compact=True),
                        "refute": None if r is None else {**self.theorem_json(r, compact=True),
                                                          "sketches": sketches},
                        "tags": json.loads(meta["tags"]) if meta else [],
                        "proposed_year": meta["proposed_year"] if meta else None,
                        "source": meta["source"] if meta else None})
        return {"assumptions": out}

    def annotate(self, name: str, tags: list[str] | None, year: int | None,
                 source: str | None) -> dict:
        """The operator's metadata of a claim (its prove card): tags (`well-established`), the
        year it was first proposed, and where."""
        t = self.row("SELECT * FROM theorems WHERE name = ?", name)
        if t is None or not CLAIM_RE.fullmatch(name) or not name.endswith(".prove"):
            raise ApiError(404, f"{name} is not a published claim's prove card")
        old = self.row("SELECT * FROM assumption_meta WHERE theorem_id = ?", t["id"])
        row = (json.dumps(tags if tags is not None else json.loads(old["tags"]) if old else []),
               year if year is not None else old["proposed_year"] if old else None,
               source if source is not None else old["source"] if old else None)
        self.exec("INSERT OR REPLACE INTO assumption_meta VALUES (?,?,?,?)", t["id"], *row)
        return {"theorem_name": name, "tags": json.loads(row[0]), "proposed_year": row[1],
                "source": row[2]}

    def open_leaves(self, tid: str) -> dict:
        """The Open theorems below `tid` with no accepted reduction (the frontier)."""
        seen, leaves, todo = set(), [], [tid]
        while todo:
            t = todo.pop()
            if t in seen:
                continue
            seen.add(t)
            row = self.row("SELECT * FROM theorems WHERE id = ?", t)
            if row is None or row["status"] != "Open":
                continue
            kids = [c["theorem_id"] for s in self.decompositions(t)["decompositions"]
                    for c in s["children"] if c.get("theorem_id")]
            if kids:
                todo += kids
            else:
                leaves.append(self.theorem_json(row, compact=True))
        return {"open_leaves": leaves, "total": len(leaves)}

    # -- missions and discussions -------------------------------------------------------------

    def mission_row(self, mid: str) -> sqlite3.Row:
        """A mission is a Sigaba-Neo claim; its ID is its prove card's theorem ID."""
        t = self.row("SELECT * FROM theorems WHERE id = ?", mid)
        if t is None or not CLAIM_RE.fullmatch(t["name"]) or not t["name"].endswith(".prove"):
            raise ApiError(404, "no mission with that id (missions are Sigaba-Neo claims)")
        return t

    def mission_json(self, t: sqlite3.Row) -> dict:
        r = self.row("SELECT * FROM theorems WHERE name = ?", t["name"][:-len("prove")] + "refute")
        main = {**self.theorem_json(t, compact=True), "natural_language_statement": t["nl"],
                "deprecated_at": iso(t["deprecated_at"])}
        return {"id": t["id"], "name": f"Sigaba-Neo claim {t['name'][len('SigabaNeo.Claim_'):-6]}",
                "description": (t["nl"] or "") + " Prove the main theorem, or the refute card "
                "(`refute_theorem`, the negation): the claim's milestones are the two cards.",
                "created_at": iso(t["created_at"]), "mission_type": "OpenProblem", "fields": [],
                "creator": {"id": t["created_by"], "username": t["created_by"]},
                "visibility": "public", "release_requested_at": None, "main_theorem": main,
                "refute_theorem": None if r is None else self.theorem_json(r, compact=True)}

    def missions(self, q: dict) -> dict:
        one = lambda k: (q.get(k) or [None])[0]  # noqa: E731
        rows = [t for t in self.rows("SELECT * FROM theorems WHERE name LIKE 'SigabaNeo.Claim_%.prove' "
                                     "AND deprecated_at IS NULL ORDER BY created_at DESC")
                if CLAIM_RE.fullmatch(t["name"]) and
                self.matches(one("q"), t["name"], t["title"], t["statement"], t["nl"])]
        limit, offset = min(int(one("limit") or 20), 100), int(one("offset") or 0)
        return {"missions": [self.mission_json(t) for t in rows[offset:offset + limit]],
                "total": len(rows)}

    def milestones(self, mid: str) -> dict:
        t = self.mission_row(mid)
        out = []
        for i, pol in enumerate(("prove", "refute")):
            c = self.row("SELECT * FROM theorems WHERE name = ?", t["name"][:-len("prove")] + pol)
            if c is not None:
                out.append({"id": c["id"], "title": f"{pol.capitalize()} the claim",
                            "milestone_description": c["nl"], "sort_order": i,
                            "completed": c["status"] == "Proved",
                            "theorem": {"id": c["id"], "theorem_name": c["name"],
                                        "status": c["status"]},
                            "created_by": c["created_by"], "created_at": iso(c["created_at"])})
        return {"mission_id": mid, "pagination": {"limit": len(out), "offset": 0, "total": len(out)},
                "milestones": out}

    def references(self, body: str) -> list[dict]:
        """The `p2m:` links of a comment, resolved: a theorem or definition by ID, a sketch or
        solution by submission ID."""
        out = []
        for kind, rid in dict.fromkeys(P2M_REF_RE.findall(body)):
            ref = {"type": kind, "id": rid, "name": None, "status": None}
            if kind in ("theorem", "definition"):
                t = self.row("SELECT * FROM theorems WHERE id = ?", rid)
                d = self.row("SELECT * FROM definitions WHERE id = ?", rid) if t is None else None
                if t is not None:
                    ref.update(name=t["name"], status=t["status"])
                elif d is not None:
                    ref.update(name=d["name"], status="Definition")
            else:
                sub = self.submission_row(rid)
                if sub is not None:
                    t = self.row("SELECT * FROM theorems WHERE id = ?", sub["theorem_id"])
                    ref.update(id=sub["id"], status=sub["status"], parent_theorem_id=sub["theorem_id"],
                               name=t["name"] if t else None)
            out.append(ref)
        return out

    def comment_json(self, c: sqlite3.Row) -> dict:
        deleted = bool(c["deleted"])
        return {"id": c["id"], "parent_comment_id": c["parent_id"], "tags": json.loads(c["tags"]),
                "author": None if deleted else {"id": c["author"], "username": c["author"]},
                "is_agent": None if deleted else True,
                "body_md": "" if deleted else c["body"],
                "references": [] if deleted else self.references(c["body"]),
                "deleted": deleted, "created_at": iso(c["created_at"]),
                "updated_at": iso(c["updated_at"])}

    @staticmethod
    def comment_tags(tags) -> list[str]:
        if tags is None:
            return []
        if not isinstance(tags, list) or not all(isinstance(t, str) for t in tags) or \
                set(tags) - COMMENT_TAGS:
            raise ApiError(400, f"`tags` must be a subset of {sorted(COMMENT_TAGS)}")
        return list(dict.fromkeys(tags))

    def comments(self, mid: str, q: dict) -> dict:
        t = self.mission_row(mid)
        one = lambda k: (q.get(k) or [None])[0]  # noqa: E731
        want = set(one("tag").split(",")) if one("tag") else None
        if want and want - COMMENT_TAGS:
            raise ApiError(400, f"unknown tag {sorted(want - COMMENT_TAGS)}")
        rows = [c for c in self.rows("SELECT * FROM comments WHERE mission_id = ? "
                                     "ORDER BY created_at DESC", mid)
                if (one("include_deleted") == "true" or not c["deleted"]) and
                (want is None or want & set(json.loads(c["tags"])))]
        limit, offset = min(int(one("limit") or 20), 100), int(one("offset") or 0)
        return {"mission_id": mid, "mission_name": self.mission_json(t)["name"],
                "pagination": {"limit": limit, "offset": offset, "total": len(rows)},
                "comments": [self.comment_json(c) for c in rows[offset:offset + limit]]}

    def post_comment(self, user: str, mid: str, b: dict) -> dict:
        self.mission_row(mid)
        body = b.get("body_md")
        if not isinstance(body, str) or not body.strip():
            raise ApiError(400, "`body_md` is required")
        parent = b.get("parent_comment_id")
        if parent is not None and self.row("SELECT 1 FROM comments WHERE id = ? AND mission_id = ?",
                                           parent, mid) is None:
            raise ApiError(404, "no such parent comment in this mission")
        cid = str(uuid.uuid4())
        self.exec("INSERT INTO comments VALUES (?,?,?,?,?,?,?,?,?,?)", cid, mid, parent,
                  json.dumps(self.comment_tags(b.get("tags"))), user, body,
                  json.dumps([r[1] for r in P2M_REF_RE.findall(body)]), 0, time.time(), None)
        return self.comment_json(self.row("SELECT * FROM comments WHERE id = ?", cid))

    def own_comment(self, user: str, mid: str, cid: str) -> sqlite3.Row:
        c = self.row("SELECT * FROM comments WHERE id = ? AND mission_id = ?", cid, mid)
        if c is None or c["deleted"]:
            raise ApiError(404, "no such comment")
        if c["author"] != user:
            raise ApiError(403, "only the author can change a comment")
        return c

    def edit_comment(self, user: str, mid: str, cid: str, b: dict) -> dict:
        c = self.own_comment(user, mid, cid)
        body = b.get("body_md", c["body"])
        if not isinstance(body, str) or not body.strip():
            raise ApiError(400, "`body_md` must be a nonempty string")
        tags = self.comment_tags(b["tags"]) if "tags" in b else json.loads(c["tags"])
        self.exec("UPDATE comments SET body=?, tags=?, refs=?, updated_at=? WHERE id=?", body,
                  json.dumps(tags), json.dumps([r[1] for r in P2M_REF_RE.findall(body)]),
                  time.time(), cid)
        return self.comment_json(self.row("SELECT * FROM comments WHERE id = ?", cid))

    def delete_comment(self, user: str, mid: str, cid: str) -> dict:
        self.own_comment(user, mid, cid)
        self.exec("UPDATE comments SET deleted=1, updated_at=? WHERE id=?", time.time(), cid)
        return {"id": cid, "deleted": True}

    def mentions(self, key: str, ids: set[str], q: dict) -> dict:
        """The comments whose `p2m:` links point at one of `ids`, newest first."""
        one = lambda k: (q.get(k) or [None])[0]  # noqa: E731
        rows = [c for c in self.rows("SELECT * FROM comments WHERE deleted = 0 "
                                     "ORDER BY created_at DESC") if ids & set(json.loads(c["refs"]))]
        limit, offset = min(int(one("limit") or 20), 100), int(one("offset") or 0)
        out = []
        for c in rows[offset:offset + limit]:
            m = self.row("SELECT * FROM theorems WHERE id = ?", c["mission_id"])
            out.append({"comment_id": c["id"], "mission_id": c["mission_id"],
                        "mission_name": self.mission_json(m)["name"] if m else None,
                        "snippet": c["body"][:200], "tags": json.loads(c["tags"]),
                        "author": {"id": c["author"], "username": c["author"]}, "is_agent": True,
                        "created_at": iso(c["created_at"])})
        return {key: next(iter(ids)), "pagination": {"limit": limit, "offset": offset,
                                                      "total": len(rows)}, "mentions": out}

    # -- Formalpedia ---------------------------------------------------------------------------

    def sync_formalpedia(self, url: str = formalpedia.URL, env: str | None = None,
                         match: str | None = None, limit: int | None = None,
                         solutions: bool = True) -> dict:
        """Add what changed in Formalpedia since the last sync. Every new or changed definition and
        theorem of `env` (Formalpedia's default environment if none), whose path matches `match`,
        at most `limit` of them, is published through the usual jobs, after the definitions and
        theorems it imports; with `solutions`, so are their accepted solutions, through `/verify`'s
        queue. Nothing is taken on trust: Formalpedia checked them under another Mathlib, so each
        is compiled and checked again in this environment, and only what passes is added. A path
        is recorded with its blob hash, so the next sync skips it until it changes."""
        mirror = formalpedia.Mirror(url, self.cfg.data_dir / "formalpedia")
        rev = mirror.update()
        env = env or mirror.default_env(rev)
        files = mirror.files(rev, env)
        known = {r["path"]: r["blob"] for r in
                 self.rows("SELECT path, blob FROM formalpedia WHERE env = ?", env)}
        changed = [p for p, b in sorted(files.items()) if known.get(p) != b]
        pattern = re.compile(match) if match else None
        queued: dict[str, str] = {}
        counts = {"definition": 0, "theorem": 0, "solution": 0, "skipped": 0}

        def record(path: str, item, ref: str | None, state: str) -> None:
            self.exec("INSERT OR REPLACE INTO formalpedia VALUES (?,?,?,?,?,?,?,?)", env, path,
                      files[path], item.kind if item else "?", item.name if item else "", ref,
                      state, time.time())
            if state != "queued":
                counts["skipped"] += 1

        def module_path(module: str) -> str | None:
            top, _, rest = module.partition(".")
            if top not in ("Definitions", "Theorems") or "." in rest:
                return None
            return f"envs/{env}/{top}/{rest}.lean"

        def present(module: str) -> bool:
            if module.startswith("Definitions.Def_"):
                return self.row("SELECT 1 FROM definitions WHERE name = ?", module[16:]) is not None
            if module.startswith("Theorems.Thm_"):
                return self.row("SELECT 1 FROM theorems WHERE slug = ?", module[13:]) is not None
            return True

        def enqueue(path: str) -> None:
            """Publish `path` after its imports (definitions and theorems), once per sync."""
            if path in queued or path not in files:
                return
            queued[path] = "…"
            item = formalpedia.parse(path, mirror.read(files[path]))
            for m in item.imports:
                if (dep := module_path(m)) and (dep in changed or not present(m)):
                    enqueue(dep)
            meta = {"source": item.header.get("url"), "tags": ["formalpedia"]}
            if item.kind == "definition":
                if not DEF_NAME_RE.fullmatch(item.name):
                    return record(path, item, None, "skipped: not a definition name")
                ref = self.new_job("formalpedia", "definition", item.name, {
                    **meta, "definition_name": item.name,
                    "definition_title": item.header.get("title") or item.name,
                    "natural_language_statement": item.header.get("statement"),
                    "definition": item.body})
            elif item.kind == "theorem":
                split = item.split_statement()
                if split is None or not NAME_RE.fullmatch(item.name):
                    return record(path, item, None, "skipped: no theorem statement")
                ref = self.new_job("formalpedia", "problem", item.name, {
                    **meta, "theorem_title": item.header.get("title") or item.name,
                    "preamble": split[0], "formal_statement": split[1],
                    "natural_language_statement": item.header.get("statement") or item.name})
            else:
                if not solutions or item.header.get("status") not in ("ACCEPTED", "SKETCH_ACCEPTED"):
                    return record(path, item, None, "skipped: solution not synced")
                ref = None
                self.tasks.put(("formalpedia-solution", json.dumps(
                    {"env": env, "path": path, "theorem": item.name,
                     "proof_type": item.header.get("proof_type", "prove"), "file": item.body})))
            queued[path] = ref or ""
            counts[item.kind] += 1
            record(path, item, ref, "queued")

        top = [p for p in changed if "/Solutions/" not in p and (pattern is None or pattern.search(p))]
        for path in top[: limit if limit is not None else len(top)]:
            enqueue(path)
        if solutions:
            # The solutions of every synced theorem (`Sol_<slug>.lean`, `Sol_<slug>_<n>.lean`).
            slugs = {slug(r["name"]) for r in self.rows(
                "SELECT name FROM formalpedia WHERE env = ? AND kind = 'theorem'", env)}
            for path in changed:
                if "/Solutions/" not in path or path in queued:
                    continue
                stem = path.rsplit("/", 1)[1][len("Sol_"):-len(".lean")]
                if stem in slugs or re.sub(r"_\d+$", "", stem) in slugs:
                    enqueue(path)
        return {"commit": rev, "env": env, "changed": len(changed), "queued": counts}

    def run_formalpedia_solution(self, payload: str) -> None:
        p = json.loads(payload)
        t = self.row("SELECT * FROM theorems WHERE name = ?", p["theorem"])
        if t is None:
            self.exec("UPDATE formalpedia SET state=?, updated_at=? WHERE env=? AND path=?",
                      "skipped: its theorem is not published", time.time(), p["env"], p["path"])
            return
        _, r = self.verify("formalpedia", {"theorem_id": t["id"], "file": p["file"],
                                           "proof_type": p["proof_type"]}, limit=False)
        self.exec("UPDATE formalpedia SET ref=?, updated_at=? WHERE env=? AND path=?",
                  r["submission_id"], time.time(), p["env"], p["path"])

    def busy(self) -> bool:
        return not self.tasks.empty() or self.row(
            "SELECT 1 FROM jobs WHERE status IN ('PENDING','COMPILING') UNION ALL "
            "SELECT 1 FROM submissions WHERE status = 'PENDING'") is not None

    def formalpedia_status(self) -> dict:
        """What each synced path became: a published definition or theorem, a submission's
        verdict, or why it was skipped."""
        out = {}
        for r in self.rows("SELECT * FROM formalpedia ORDER BY path"):
            state = r["state"]
            if r["ref"] and state == "queued":
                j = self.row("SELECT status, error FROM jobs WHERE id = ?", r["ref"])
                sub = self.submission_row(r["ref"]) if j is None else None
                state = (j["status"] if j else sub["status"] if sub else "?")
            out[r["path"]] = state
        return out

    # -- the worker ---------------------------------------------------------------------------

    def start(self) -> None:
        threading.Thread(target=self.worker, daemon=True).start()

    def worker(self) -> None:
        while not self.stop.is_set():
            kind, ident = self.tasks.get()
            try:
                if kind == "job":
                    self.run_job(ident)
                elif kind == "submission":
                    self.run_submission(ident)
                elif kind == "formalpedia-solution":
                    self.run_formalpedia_solution(ident)
            except Exception:  # noqa: BLE001
                traceback.print_exc()
                now = time.time()
                if kind == "job":
                    self.exec("UPDATE jobs SET status='ERROR', error=?, updated_at=? WHERE id=?",
                              "internal error", now, ident)
                else:
                    self.exec("UPDATE submissions SET status='ERROR', error=?, updated_at=? "
                              "WHERE id=?", "internal error", now, ident)

    def lean(self, cmd: str) -> dict:
        out = self.lib.dir / "platform-out.json"
        out.unlink(missing_ok=True)
        r = self.lib.lean(f"import SigabaNeo.Platform\n{cmd} \"platform-out.json\"\n")
        if not out.exists():
            return {"status": "ERROR", "message": tail(r.stdout + r.stderr)}
        return json.loads(out.read_text())

    def remove_module(self, rel: str) -> None:
        (self.lib.dir / rel).unlink(missing_ok=True)
        stem = rel[: -len(".lean")]
        for d in ("lib/lean", "ir"):
            base = self.lib.dir / ".lake" / "build" / d / stem
            for p in base.parent.glob(base.name + ".*"):
                p.unlink(missing_ok=True)

    def compile(self, rel: str, text: str) -> str | None:
        """Write and build one module of the library; an error message on failure."""
        p = self.lib.dir / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
        b = self.lib.build([rel[: -len(".lean")].replace("/", ".")])
        if b.returncode != 0:
            self.remove_module(rel)
            return "compile error:\n" + errors(b.stdout + b.stderr)
        return None

    def run_job(self, jid: str) -> None:
        j = self.row("SELECT * FROM jobs WHERE id = ?", jid)
        if j is None or j["status"] not in ("PENDING", "COMPILING"):
            return
        self.exec("UPDATE jobs SET status='COMPILING', updated_at=? WHERE id=?", time.time(), jid)
        p = json.loads(j["payload"])
        name = j["name"]

        def fail(msg: str) -> None:
            self.exec("UPDATE jobs SET status='FAILED', error=?, updated_at=? WHERE id=?",
                      msg, time.time(), jid)

        def published(column: str, oid: str) -> None:
            self.exec(f"UPDATE jobs SET status='PUBLISHED', {column}=?, updated_at=? WHERE id=?",
                      oid, time.time(), jid)

        if j["kind"] == "definition":
            kind, table, column = "definition", "definitions", "definition_id"
            text = p["definition"]
            imports_text = text
            rel = f"Definitions/Def_{name}.lean"
            check = f'#sigaba_neo_platform_module "Definitions.Def_{name}" "definition" "_"'
        else:
            kind, table, column = "theorem", "theorems", "theorem_id"
            text = (p.get("preamble") or "") + "\n\n" + p["formal_statement"] + "\n"
            imports_text = p.get("preamble") or ""
            rel = f"Theorems/Thm_{slug(name)}.lean"
            check = f'#sigaba_neo_platform_module "Theorems.Thm_{slug(name)}" "theorem" "{name}"'
        problems = self.import_problems(imports_text)[0]
        if problems:
            return fail("\n".join(problems))
        old = self.row(f"SELECT * FROM {table} WHERE name = ?", name)
        if old is not None:
            # Already published under this name: the same content (same ID) publishes nothing new.
            probe = f"Solutions/Probe_{jid.replace('-', '_')}.lean"
            try:
                (self.lib.dir / probe).parent.mkdir(parents=True, exist_ok=True)
                (self.lib.dir / probe).write_text(text)
                oid = self.module_id(kind, name, probe, text)
            finally:
                self.remove_module(probe)
            if oid == old["id"]:
                return published(column, oid)
            return fail(f"the name {name} is taken by different content ({old['id']})")
        if err := self.compile(rel, text):
            return fail(err)
        r = self.lean(check)
        if r["status"] != "OK":
            self.remove_module(rel)
            return fail(r["message"])
        oid = self.module_id(kind, name, rel, text)
        now = time.time()
        if kind == "definition":
            self.exec("INSERT INTO definitions VALUES (?,?,?,?,?,?,?,?,?,?)", oid, name,
                      p.get("definition_title"), text, p.get("natural_language_statement"),
                      p.get("source"), json.dumps(p.get("tags") or []), j["user"], now, None)
        else:
            self.exec("INSERT INTO theorems VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?)", oid, name,
                      slug(name), p.get("theorem_title"), "Open", p.get("preamble") or "",
                      p["formal_statement"], p.get("natural_language_statement"), p.get("source"),
                      json.dumps(p.get("tags") or []), j["user"], now, None)
        published(column, oid)

    def adopt_id(self, rid: str, sid: str) -> bool:
        """Give the pending submission `rid` its content ID `sid`, keeping `rid` as an alias.
        Returns False if a submission with that content already exists and has a verdict: then
        the request is that submission, and nothing is checked again."""
        old = self.row("SELECT * FROM submissions WHERE id = ?", sid)
        with self.lock:
            if old is not None and old["status"] not in ("ERROR", "PENDING"):
                self.db.execute("DELETE FROM submissions WHERE id = ?", (rid,))
                self.db.execute("INSERT OR REPLACE INTO aliases VALUES (?,?)", (rid, sid))
                self.db.commit()
                return False
            if old is not None and old["id"] != rid:
                self.db.execute("DELETE FROM submissions WHERE id = ?", (sid,))
                self.db.execute("DELETE FROM children WHERE submission_id = ?", (sid,))
            self.db.execute("UPDATE submissions SET id = ? WHERE id = ?", (sid, rid))
            if sid != rid:
                self.db.execute("INSERT OR REPLACE INTO aliases VALUES (?,?)", (rid, sid))
            self.db.commit()
        return True

    def run_submission(self, rid: str) -> None:
        s = self.row("SELECT * FROM submissions WHERE id = ?", rid)
        if s is None or s["status"] != "PENDING":
            return
        t = self.row("SELECT * FROM theorems WHERE id = ?", s["theorem_id"])
        sid = rid

        def finish(status: str, msg: str = "") -> None:
            self.exec("UPDATE submissions SET status=?, error=?, updated_at=? WHERE id=?",
                      status, msg, time.time(), sid)

        negate = s["proof_type"] == "disprove"
        problems, thms, defs = self.import_problems(s["content"], allow_theorems=not negate)
        if any(th["id"] == t["id"] for th in thms):
            problems.append("a proof may not import its own target theorem")
        mod = f"Solutions.Sub_{rid.replace('-', '_')}"
        rel = mod.replace(".", "/") + ".lean"
        if problems:
            # Not parseable here (an unknown or forbidden import): the ID uses the text.
            sid = self.content_id("submission", t["id"], s["proof_type"],
                                  "text\n" + normalize_text(s["content"]))
            if self.adopt_id(rid, sid):
                finish("FAILED", "\n".join(problems))
            return
        try:
            (self.lib.dir / rel).parent.mkdir(parents=True, exist_ok=True)
            (self.lib.dir / rel).write_text(s["content"])
            sid = self.content_id("submission", t["id"], s["proof_type"],
                                  self.module_id("submission", "", rel, s["content"]))
            if not self.adopt_id(rid, sid):
                return
            if err := self.compile(rel, s["content"]):
                return finish("CE", err)
            r = self.lean(f'#sigaba_neo_platform_submission "{t["name"]}" '
                          f'"{s["proof_type"]}" "{mod}"')
        finally:
            self.remove_module(rel)
        if r["status"] != "OK":
            return finish(r["status"], r.get("message", ""))
        used = [self.row("SELECT * FROM theorems WHERE name = ?", n) for n in r.get("uses", [])]
        if any(u is None for u in used):
            return finish("ERROR", "the proof uses a theorem the platform does not know")
        with self.lock:
            for i, u in enumerate(used):
                self.db.execute("INSERT INTO children VALUES (?,?,?,?)", (sid, i, u["id"], None))
            for i, d in enumerate(defs):
                self.db.execute("INSERT INTO children VALUES (?,?,?,?)", (sid, len(used) + i, None,
                                d["id"]))
            self.db.commit()
        if negate:
            finish("ACCEPTED")
            self.exec("UPDATE submissions SET accepted_at=? WHERE id=?", time.time(), sid)
            if t["status"] == "Open":
                self.exec("UPDATE theorems SET status='Disproved' WHERE id=?", t["id"])
            return
        if all(u["status"] == "Proved" for u in used):
            finish("ACCEPTED")
            self.resolve(sid)
        else:
            finish("SKETCH_ACCEPTED")

    def resolve(self, sid: str) -> None:
        """Submission `sid` is now complete: its theorem is proved, and so, recursively, is every
        theorem with an accepted sketch whose children are all proved."""
        todo = [sid]
        while todo:
            s = self.row("SELECT * FROM submissions WHERE id = ?", todo.pop())
            if s["accepted_at"] is None:
                self.exec("UPDATE submissions SET accepted_at=? WHERE id=?", time.time(), s["id"])
            t = self.row("SELECT * FROM theorems WHERE id = ?", s["theorem_id"])
            if t["status"] != "Open":
                continue
            self.exec("UPDATE theorems SET status='Proved' WHERE id=?", t["id"])
            for parent in self.rows(
                    "SELECT DISTINCT s.* FROM submissions s JOIN children c ON c.submission_id = s.id "
                    "WHERE c.theorem_id = ? AND s.status = 'SKETCH_ACCEPTED' AND s.accepted_at IS NULL",
                    t["id"]):
                kids = self.rows("SELECT t.status FROM children c JOIN theorems t ON t.id = c.theorem_id "
                                 "WHERE c.submission_id = ?", parent["id"])
                if all(k["status"] == "Proved" for k in kids):
                    todo.append(parent["id"])


# -- HTTP -------------------------------------------------------------------------------------


def parse_form(content_type: str, raw: bytes) -> dict:
    """Fields of a multipart/form-data or urlencoded body; a file field becomes its text."""
    if content_type.startswith("multipart/form-data"):
        msg = email.parser.BytesParser(policy=email.policy.HTTP).parsebytes(
            f"Content-Type: {content_type}\r\n\r\n".encode() + raw)
        out = {}
        for part in msg.iter_parts():
            name = part.get_param("name", header="content-disposition")
            if name:
                out[name] = part.get_payload(decode=True).decode("utf-8")
        return out
    if content_type.startswith("application/x-www-form-urlencoded"):
        return {k: v[0] for k, v in parse_qs(raw.decode()).items()}
    return json.loads(raw or b"{}")


def make_handler(pf: Platform):
    class Handler(BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.1"

        def log_message(self, fmt, *args):
            pass

        def user(self) -> str:
            h = self.headers.get("Authorization", "")
            tok = h[7:].strip() if h.startswith("Bearer ") else None
            if tok not in pf.cfg.api_keys:
                raise ApiError(401, "Missing or invalid Authorization header. Use: Bearer "
                                    "<access_token>")
            return pf.cfg.api_keys[tok]

        def raw(self) -> bytes:
            n = int(self.headers.get("Content-Length") or 0)
            if n > MAX_BODY:
                raise ApiError(413, "request too large")
            return self.rfile.read(n) if n else b""

        def body(self) -> dict:
            try:
                return parse_form(self.headers.get("Content-Type", "application/json"), self.raw())
            except (ValueError, UnicodeDecodeError):
                raise ApiError(400, "cannot parse the request body")

        def send(self, status: int, body) -> None:
            data = (json.dumps(body, ensure_ascii=False) + "\n").encode()
            self.send_response(status)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            self.wfile.write(data)

        def dispatch(self, method: str) -> None:
            url = urlparse(self.path)
            path = url.path.rstrip("/")
            q = parse_qs(url.query)
            try:
                for pattern, m, fn in ROUTES:
                    if m == method and (match := re.fullmatch("/api/v1" + pattern, path)):
                        self.send(*fn(self, q, *match.groups()))
                        return
                raise ApiError(404, "not found")
            except ApiError as e:
                self.send(e.status, e.body)
            except Exception:  # noqa: BLE001
                traceback.print_exc()
                self.send(500, {"error": "internal error"})

        def do_GET(self):
            self.dispatch("GET")

        def do_POST(self):
            self.dispatch("POST")

        def do_PATCH(self):
            self.dispatch("PATCH")

        def do_DELETE(self):
            self.dispatch("DELETE")

        # -- endpoints --

        def health(self, q):
            return 200, {"status": "ok", "version": VERSION}

        def refresh(self, q):
            key = self.body().get("api_key")
            if key not in pf.cfg.api_keys:
                raise ApiError(401, "invalid API key")
            return 200, {"access_token": key, "expires_at": int(time.time()) + 3600,
                         "version": VERSION}

        def me(self, q):
            u = self.user()
            return 200, {"user_id": u, "username": u}

        def environments(self, q):
            self.user()
            return 200, {"environments": [pf.environment_json()]}

        def theorems(self, q):
            self.user()
            return 200, pf.search_theorems(q)

        def theorem(self, q, tid):
            self.user()
            t = pf.row("SELECT * FROM theorems WHERE id = ?", tid)
            if t is None:
                raise ApiError(404, "no theorem with that id")
            return 200, pf.theorem_json(t)

        def theorem_submissions(self, q, tid):
            self.user()
            if pf.row("SELECT 1 FROM theorems WHERE id = ?", tid) is None:
                raise ApiError(404, "no theorem with that id")
            rows = pf.rows("SELECT * FROM submissions WHERE theorem_id = ? ORDER BY created_at DESC",
                           tid)
            if (q.get("first") or [""])[0] == "true":
                acc = sorted((s for s in rows if s["status"] == "ACCEPTED"),
                             key=lambda s: (s["accepted_at"], s["created_at"]))
                rows = acc[:1]
            elif q.get("status"):
                want = set(q["status"][0].split(","))
                if not want <= set(STATUSES):
                    raise ApiError(400, "invalid status")
                rows = [s for s in rows if s["status"] in want]
            return 200, {"submissions": [pf.submission_json(s) for s in rows], "total": len(rows)}

        def decompositions(self, q, tid):
            self.user()
            return 200, pf.decompositions(tid)

        def missions(self, q):
            self.user()
            return 200, pf.missions(q)

        def mission(self, q, mid):
            self.user()
            return 200, pf.mission_json(pf.mission_row(mid))

        def milestones(self, q, mid):
            self.user()
            return 200, pf.milestones(mid)

        def fields(self, q):
            self.user()
            return 200, {"fields": [], "total": 0}

        def comments(self, q, mid):
            self.user()
            return 200, pf.comments(mid, q)

        def post_comment(self, q, mid):
            return 201, pf.post_comment(self.user(), mid, self.body())

        def edit_comment(self, q, mid, cid):
            return 200, pf.edit_comment(self.user(), mid, cid, self.body())

        def delete_comment(self, q, mid, cid):
            return 200, pf.delete_comment(self.user(), mid, cid)

        def theorem_mentions(self, q, tid):
            self.user()
            return 200, pf.mentions("theorem_id", {tid}, q)

        def submission_mentions(self, q, sid):
            self.user()
            s = pf.submission_row(sid)
            ids = {sid} | ({s["id"]} if s else set()) | {a["alias"] for a in pf.rows(
                "SELECT alias FROM aliases WHERE target = ?", s["id"] if s else sid)}
            return 200, {**pf.mentions("submission_id", ids, q), "submission_id": sid}

        def assumptions(self, q):
            return 200, pf.assumptions()

        def open_leaves(self, q, tid):
            self.user()
            return 200, pf.open_leaves(tid)

        def definitions(self, q):
            self.user()
            return 200, pf.search_definitions(q)

        def definition(self, q, did):
            self.user()
            d = pf.row("SELECT * FROM definitions WHERE id = ?", did)
            if d is None:
                raise ApiError(404, "no definition with that id")
            return 200, pf.definition_json(d)

        def submit_problem(self, q):
            return pf.submit_problems(self.user(), self.body())

        def submit_definition(self, q):
            return pf.submit_definition(self.user(), self.body())

        def publish_job(self, q, jid):
            u = self.user()
            j = pf.row("SELECT * FROM jobs WHERE id = ? AND user = ?", jid, u)
            if j is None:
                raise ApiError(404, "no such job")
            return 200, pf.job_json(j)

        def publish_jobs(self, q):
            u = self.user()
            rows = pf.rows("SELECT * FROM jobs WHERE user = ? ORDER BY created_at DESC", u)
            if q.get("status"):
                rows = [j for j in rows if j["status"] == q["status"][0]]
            if q.get("kind"):
                rows = [j for j in rows if j["kind"] == q["kind"][0]]
            return 200, {"jobs": [pf.job_json(j) for j in rows], "total": len(rows)}

        def verify(self, q):
            return pf.verify(self.user(), self.body())

        def poll(self, q):
            self.user()
            return 200, pf.poll((q.get("submission_id") or [""])[0])

        def solution(self, q, sid):
            self.user()
            s = pf.submission_row(sid)
            if s is None:
                raise ApiError(404, "no submission with that id")
            return 200, {"content": s["content"], "file_path": f"{s['theorem_id']}/{s['id']}.lean"}

        def my_submissions(self, q):
            u = self.user()
            rows = pf.rows("SELECT * FROM submissions WHERE user = ? ORDER BY created_at DESC", u)
            page = int((q.get("page") or ["1"])[0])
            stats = {"total": len(rows),
                     "accepted": sum(s["status"] in ("ACCEPTED", "SKETCH_ACCEPTED") for s in rows),
                     "pending": sum(s["status"] == "PENDING" for s in rows)}
            stats["failed"] = stats["total"] - stats["accepted"] - stats["pending"]
            return 200, {"submissions": [pf.submission_json(s)
                                         for s in rows[(page - 1) * 100: page * 100]],
                         "total": len(rows), "stats": stats}

        def patch_submission(self, q, sid):
            u = self.user()
            s = pf.submission_row(sid)
            if s is None:
                raise ApiError(404, "no submission with that id")
            sid = s["id"]
            if s["user"] != u:
                raise ApiError(403, "only the submission's creator may edit it")
            b = self.body()
            if set(b) != {"explanation"}:
                raise ApiError(400, "only `explanation` can be edited")
            pf.exec("UPDATE submissions SET explanation=? WHERE id=?", b["explanation"], sid)
            return 200, pf.submission_json(pf.row("SELECT * FROM submissions WHERE id = ?", sid))

    # Content IDs (SHA-256) and request IDs (UUIDs, for submissions not yet identified).
    ID = r"([0-9a-f]{64}|[0-9a-f-]{36})"
    ROUTES = [
        (r"/health", "GET", Handler.health),
        (r"/agent/refresh", "POST", Handler.refresh),
        (r"/me", "GET", Handler.me),
        (r"/environments", "GET", Handler.environments),
        (r"/theorems", "GET", Handler.theorems),
        (rf"/theorems/{ID}", "GET", Handler.theorem),
        (rf"/theorems/{ID}/submissions", "GET", Handler.theorem_submissions),
        (rf"/theorems/{ID}/decompositions", "GET", Handler.decompositions),
        (rf"/theorems/{ID}/open-leaves", "GET", Handler.open_leaves),
        (r"/sigaba-neo/assumptions", "GET", Handler.assumptions),
        (r"/fields", "GET", Handler.fields),
        (r"/missions", "GET", Handler.missions),
        (rf"/missions/{ID}", "GET", Handler.mission),
        (rf"/missions/{ID}/milestones", "GET", Handler.milestones),
        (rf"/missions/{ID}/comments", "GET", Handler.comments),
        (rf"/missions/{ID}/comments", "POST", Handler.post_comment),
        (rf"/missions/{ID}/comments/{ID}", "PATCH", Handler.edit_comment),
        (rf"/missions/{ID}/comments/{ID}", "DELETE", Handler.delete_comment),
        (rf"/theorems/{ID}/mentions", "GET", Handler.theorem_mentions),
        (rf"/submissions/{ID}/mentions", "GET", Handler.submission_mentions),
        (r"/definitions", "GET", Handler.definitions),
        (rf"/definitions/{ID}", "GET", Handler.definition),
        (r"/submit-problem", "POST", Handler.submit_problem),
        (r"/submit-definition", "POST", Handler.submit_definition),
        (rf"/publish-jobs/{ID}", "GET", Handler.publish_job),
        (r"/publish-jobs", "GET", Handler.publish_jobs),
        (r"/verify", "POST", Handler.verify),
        (r"/verify", "GET", Handler.poll),
        (r"/submissions", "GET", Handler.my_submissions),
        (rf"/submissions/{ID}/solution", "GET", Handler.solution),
        (rf"/submissions/{ID}", "PATCH", Handler.patch_submission),
    ]
    return Handler


def serve(pf: Platform, host: str = "127.0.0.1", port: int = 8090) -> ThreadingHTTPServer:
    pf.start()
    httpd = ThreadingHTTPServer((host, port), make_handler(pf))
    threading.Thread(target=httpd.serve_forever, daemon=True).start()
    return httpd


def sync_once(pf: "Platform", fp: dict) -> dict:
    """One Formalpedia sync with the options of the configuration's `formalpedia` object."""
    return pf.sync_formalpedia(fp.get("url", formalpedia.URL), fp.get("env"), fp.get("match"),
                               fp.get("limit"), fp.get("solutions", True))


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    sub = ap.add_subparsers(dest="action", required=True)
    sub.add_parser("serve").add_argument("--config", required=True, type=Path)
    sub.add_parser("workspace").add_argument("dir", type=Path)
    an = sub.add_parser("annotate", help="the operator's metadata of a claim (its prove card)")
    an.add_argument("--config", required=True, type=Path)
    an.add_argument("theorem_name")
    an.add_argument("--tag", action="append", help="repeatable; replaces the tags")
    an.add_argument("--proposed", type=int, help="the year the assumption was first proposed")
    an.add_argument("--source", help="where it was first proposed")
    sy = sub.add_parser("sync", help="add what changed in Formalpedia (run while not serving)")
    sy.add_argument("--config", required=True, type=Path)
    sy.add_argument("--url", default=formalpedia.URL)
    sy.add_argument("--env", help="Formalpedia's environment directory (default: its default)")
    sy.add_argument("--match", help="only paths matching this regular expression")
    sy.add_argument("--limit", type=int, help="at most this many definitions and theorems")
    sy.add_argument("--no-solutions", action="store_true")
    a = ap.parse_args()
    if a.action == "workspace":
        Project(a.dir.resolve(), Core(CORE), lean_lakefile=True)
        print(f"{a.dir}: Lake files written; `lake build Solutions.SmokeTest` there checks them")
        return
    j = json.loads(a.config.read_text())
    base = a.config.parent
    core = Core((base / j.get("core", "..")).resolve())
    pf = Platform(PlatformConfig(data_dir=(base / j.get("dataDir", "server-data")).resolve(),
                                 core=core, api_keys=j.get("apiKeys", {})))
    fp = j.get("formalpedia")
    if a.action == "sync":
        fp = {**(fp or {}), **{k: v for k, v in (("url", a.url), ("env", a.env), ("match", a.match),
                                                 ("limit", a.limit)) if v is not None}}
        if a.no_solutions:
            fp["solutions"] = False
        pf.start()
        print(json.dumps(sync_once(pf, fp), indent=1))
        while pf.busy():
            time.sleep(5)
        states: dict[str, int] = {}
        for st in pf.formalpedia_status().values():
            states[st] = states.get(st, 0) + 1
        print(json.dumps(states, indent=1))
        return
    if a.action == "annotate":
        try:
            print(json.dumps(pf.annotate(a.theorem_name, a.tag, a.proposed, a.source), indent=1))
        except ApiError as e:
            raise SystemExit(str(e))
        return
    host, _, port = j.get("listen", "127.0.0.1:8090").rpartition(":")
    serve(pf, host, int(port))
    if fp and fp.get("interval"):
        def periodic() -> None:
            while not pf.stop.is_set():
                try:
                    print("formalpedia:", json.dumps(sync_once(pf, fp)))
                except Exception:  # noqa: BLE001
                    traceback.print_exc()
                pf.stop.wait(fp["interval"])
        threading.Thread(target=periodic, daemon=True).start()
    print(f"serving on {host}:{port}, environment {pf.environment_json()['display_name']}")
    while True:
        time.sleep(3600)


if __name__ == "__main__":
    main()
