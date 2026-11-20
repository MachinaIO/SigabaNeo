#!/usr/bin/env python3
"""The submitter's tool (docs/DESIGN.md). Standard library only.

    python3 sigaba_neo.py submit CLAIM
    python3 sigaba_neo.py check  CLAIM
    python3 sigaba_neo.py dev    CLAIM

`CLAIM` is the submitter's claim directory: `claim.json` (`{"target": "T", "hypotheses": [...],
"select": [...]}`) and `Definitions/Def_*.lean` (Prove2Me's format). The server is `--api` (or
`$PROVE2ME_API`), the access token `$PROVE2ME_TOKEN`.

* `submit` fixes the hypotheses (each stands for another claim's card; `select` chooses cards on
  the server) and writes them back to `claim.json`. Then it publishes the definitions and the two
  cards, as theorems ending in `:= by sorry`: `SigabaNeo.Claim_<d>.prove : T` and
  `SigabaNeo.Claim_<d>.refute : ¬ T`. The cards are the proposition's (`<d>` covers the target and
  the definitions), shared by every claim of it; reductions are sketches between cards.
* `check` asks the server about both. For each, it downloads an accepted solution or sketch, the
  platform theorems it imports with theirs (recursively, through reductions, down to the
  hypotheses' cards, which become axioms of their statements; no other card may stay unproved), and the platform definitions they import; lays them out in a
  Lake workspace that requires the core; and runs the trusted `#sigaba_neo_check` there on `CLAIM`,
  printing its report as it is.

* `dev` makes `CLAIM` a Lake project of its own (`lakefile.toml`, `lean-toolchain`,
  `lake-manifest.json`), requiring this checkout's core and sharing its built packages, with the
  libraries `Definitions` and `Solution` (`CLAIM/Solution.lean` and `CLAIM/Solution/`). An editor
  then resolves `import Definitions.…` in the claim's files, and `lake build` there builds them.
  The check never uses these files.

Nothing here can make a false claim pass: the trusted check reads `CLAIM` itself, compares the
workspace's definition files with it, and states what was established. A mistake here only makes
a build or the check fail. What this tool must get right is to run that check with this
checkout's core (`CORE`) and to show its report.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
from dataclasses import dataclass, field
from pathlib import Path

CORE = Path(__file__).resolve().parents[1]      # a built checkout of the core
SUBSCRIPT = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")


def slug(name: str) -> str:
    """Prove2Me's module slug of a theorem name."""
    return name.replace(".", "_")


def imports_of(text: str) -> list[str]:
    return [w for line in text.splitlines() if (ws := line.split())[:1] == ["import"]
            for w in ws[1:]]


def split_header(text: str) -> tuple[list[str], str]:
    """The imports of a Lean file, and the rest."""
    lines = text.split("\n")
    last = max((i for i, l in enumerate(lines) if l.strip().startswith("import ")), default=-1)
    return imports_of("\n".join(lines[: last + 1])), "\n".join(lines[last + 1:])


# -- the claim ----------------------------------------------------------------------------------


@dataclass
class Claim:
    dir: Path
    target: str
    hypotheses: list[str]                        # `H` or `¬ H`, Lean names
    definitions: dict[str, str]                  # definition name -> Lean text
    cards: dict[str, str] = field(default_factory=dict)   # hypothesis -> the card it stands for
    select: list[dict] = field(default_factory=list)      # hypotheses chosen on the server
    resolved_at: str | None = None

    @staticmethod
    def load(d: Path) -> "Claim":
        c = json.loads((d / "claim.json").read_text())
        defs = {p.stem[len("Def_"):]: p.read_text()
                for p in sorted((d / "Definitions").glob("Def_*.lean"))}
        if not defs:
            raise SystemExit(f"no Definitions/Def_*.lean in {d}")
        hyps = [normal_prop(h) for h in c.get("hypotheses", [])]
        return Claim(d.resolve(), c["target"], hyps, defs, dict(c.get("cards", {})),
                     list(c.get("select", [])), c.get("resolvedAt"))

    @property
    def resolved(self) -> bool:
        """Every hypothesis stands for a card, and the selectors were resolved."""
        return all(h in self.cards for h in self.hypotheses) and \
            (not self.select or self.resolved_at is not None)

    @property
    def digest(self) -> str:
        """The proposition: its target and definitions. The hypotheses are not part of it: every
        claim of the same proposition shares its cards, and each submitter's `check` decides which
        unproved cards it accepts as leaves."""
        h = hashlib.sha256(f"sigaba-neo proposition v4\ntarget {self.target}\n".encode())
        for n, t in sorted(self.definitions.items()):
            h.update(f"definition {n} {hashlib.sha256(t.encode()).hexdigest()}\n".encode())
        return h.hexdigest()

    def name(self, polarity: str) -> str:
        return f"SigabaNeo.Claim_{self.digest[:16]}.{polarity}"

    def card_statement(self, name: str, refute: bool) -> str:
        """A card states the target or its negation, without hypotheses. A proof may be a sketch on
        other cards (a reduction); which unproved cards count is the submitter's choice."""
        return f"theorem {name} : {'¬ ' if refute else ''}{self.target}"

    def statement(self, name: str, refute: bool, negated: bool = False) -> str:
        """`theorem name (h₀ : H₀) … : C`, `C` = `T` or `¬ T`; negated: `¬ (∀ (h₀ : H₀) …, C)`."""
        c = f"¬ {self.target}" if refute else self.target
        bs = " ".join(f"(h{str(i).translate(SUBSCRIPT)} : {h})" for i, h in enumerate(self.hypotheses))
        if negated:
            return f"theorem {name} : ¬ ({f'∀ {bs}, ' if bs else ''}{c})"
        return f"theorem {name} {bs} : {c}" if bs else f"theorem {name} : {c}"

    @property
    def preamble(self) -> str:
        return "\n".join(f"import Definitions.Def_{n}" for n in sorted(self.definitions))


def normal_prop(p: str) -> str:
    """A hypothesis, `H` or `¬ H`, as the trusted check reads it."""
    p = p.strip()
    return "¬ " + p[1:].strip() if p.startswith("¬") else p


def card_prop(statement: str) -> str | None:
    """The proposition of a claim card (`theorem X : H := by sorry`, `H` = `T` or `¬ T`)."""
    m = re.fullmatch(r"\s*theorem\s+\S+\s*:\s*(¬\s*)?([^\s()¬:]+)\s*:=\s*by\s+sorry\s*", statement)
    return None if m is None else ("¬ " if m.group(1) else "") + m.group(2)


# -- the server ---------------------------------------------------------------------------------


class Server:
    """A Prove2Me-compatible API (only what this tool uses)."""

    def __init__(self, base: str, token: str | None):
        self.base, self.token = base.rstrip("/"), token

    def call(self, method: str, path: str, data: bytes | None = None, ctype: str | None = None):
        req = urllib.request.Request(self.base + path, data=data, method=method)
        if ctype:
            req.add_header("Content-Type", ctype)
        if self.token:
            req.add_header("Authorization", f"Bearer {self.token}")
        try:
            with urllib.request.urlopen(req, timeout=60) as r:
                return json.loads(r.read())
        except urllib.error.HTTPError as e:
            if e.code == 404 and method == "GET":
                return None
            raise SystemExit(f"{method} {path}: HTTP {e.code}: {e.read()[:500]!r}")

    def get(self, path: str, **q):
        return self.call("GET", path + ("?" + urllib.parse.urlencode(q) if q else ""))

    def post(self, path: str, body: dict):
        return self.call("POST", path, json.dumps(body).encode(), "application/json")

    def post_form(self, path: str, fields: dict[str, str]):
        b = uuid.uuid4().hex
        data = b"".join(f'--{b}\r\nContent-Disposition: form-data; name="{k}"'
                        f'{"; filename=\"solution.lean\"" if k == "file" else ""}\r\n\r\n'
                        .encode() + v.encode() + b"\r\n" for k, v in fields.items())
        return self.call("POST", path, data + f"--{b}--\r\n".encode(),
                         f"multipart/form-data; boundary={b}")

    def wait(self, path: str, done):
        while not done((r := self.get(path) or {}).get("status")):
            time.sleep(2)
        return r

    def theorem(self, name: str) -> dict | None:
        rows = (self.get("/theorems", theorem_name=name, view="full") or {}).get("theorems", [])
        return next((t for t in rows if t["theorem_name"] == name), None)

    def theorem_by_slug(self, s: str) -> dict | None:
        rows = (self.get("/theorems", q=s.replace("_", " "), view="full", limit=50) or {}) \
            .get("theorems", [])
        return next((t for t in rows if slug(t["theorem_name"]) == s), None)

    def definition(self, name: str) -> dict | None:
        rows = (self.get("/definitions", q=name, view="full", limit=50) or {}).get("definitions", [])
        return next((d for d in rows if d["definition_name"] == name), None)

    def accepted(self, theorem_id: str) -> list[dict]:
        subs = (self.get(f"/theorems/{theorem_id}/submissions",
                         status="ACCEPTED,SKETCH_ACCEPTED") or {}).get("submissions", [])
        return sorted(subs, key=lambda s: (s["status"] != "ACCEPTED", s.get("accepted_at") or "~"))

    def solution(self, submission_id: str) -> str:
        return (self.get(f"/submissions/{submission_id}/solution") or {}).get("content", "")

    def publish(self, endpoint: str, body: dict) -> dict:
        r = self.post(endpoint, body)
        job = r["job_id"] if "job_id" in r else r["jobs"][0]["job_id"] if r.get("jobs") else None
        if job is None:
            raise SystemExit(f"{endpoint}: {r}")
        j = self.wait(f"/publish-jobs/{job}", lambda s: s in ("PUBLISHED", "FAILED", "ERROR"))
        if j["status"] != "PUBLISHED":
            raise SystemExit(f"{endpoint}: {j['status']}: {j.get('error_message')}")
        return j


# -- submit -------------------------------------------------------------------------------------

SELECTOR_KEYS = {"id", "tag", "minYears", "minRefuteSketches"}


def selected(server: Server, claim: Claim) -> list[dict]:
    """The cards the selectors choose. `{"id": X}` is one card (a theorem id or name, prove or
    refute). The other keys choose among the published claims' prove cards, all of the keys of one
    selector at once: `tag` (the operator's tag, such as `well-established`), `minYears` (first
    proposed at least that many years ago), `minRefuteSketches` (at least that many accepted
    sketches on its refute card). Those exclude claims that are refuted or disproved."""
    rows, out = None, []
    for sel in claim.select:
        if not isinstance(sel, dict) or not sel or set(sel) - SELECTOR_KEYS:
            raise SystemExit(f"bad selector {sel!r}: keys are {sorted(SELECTOR_KEYS)}")
        if "id" in sel:
            if len(sel) > 1:
                raise SystemExit(f"bad selector {sel!r}: `id` stands alone")
            x = str(sel["id"])
            row = server.get(f"/theorems/{x}") if re.fullmatch(r"[0-9a-f-]{36}|[0-9a-f]{64}", x) \
                else server.theorem(x)
            if row is None:
                raise SystemExit(f"selector {sel!r}: no such theorem")
            out.append(row)
            continue
        if rows is None:
            rows = (server.get("/sigaba-neo/assumptions") or {}).get("assumptions")
            if rows is None:
                raise SystemExit("the server has no /sigaba-neo/assumptions (selectors other than "
                                 "`id` need the compatible server, python/p2m_server.py)")
        year = time.gmtime().tm_year
        for r in rows:
            ref = r.get("refute") or {}
            if r["status"] == "Disproved" or ref.get("status") == "Proved":
                continue
            if "tag" in sel and sel["tag"] not in r.get("tags", []):
                continue
            if "minYears" in sel and (r.get("proposed_year") is None or
                                      year - r["proposed_year"] < sel["minYears"]):
                continue
            if "minRefuteSketches" in sel and ref.get("sketches", 0) < sel["minRefuteSketches"]:
                continue
            out.append(r)
    return out


def fetch_definitions(server: Server, claim: Claim, text: str) -> None:
    """Copy the definitions `text` imports (recursively) into the claim directory."""
    for m in imports_of(text):
        if not m.startswith("Definitions.Def_") or m[16:] in claim.definitions:
            continue
        d = server.definition(m[16:])
        if d is None:
            raise SystemExit(f"the server has no definition {m[16:]}")
        claim.definitions[m[16:]] = d["definition"]
        (claim.dir / "Definitions" / f"Def_{m[16:]}.lean").write_text(d["definition"])
        fetch_definitions(server, claim, d["definition"])


def resolve(server: Server, claim: Claim) -> Claim:
    """Fix the hypotheses: each stands for a card. A hypothesis written in `claim.json` is
    published as a claim of its own (its prove card, or for `¬ H` its refute card); a selected card
    brings its definitions into `Definitions/`. The result is written back to `claim.json`
    (`hypotheses`, `cards`, `resolvedAt`), and is not resolved again."""
    if claim.resolved:
        return claim
    cards = dict(claim.cards)
    for h in claim.hypotheses:
        if h not in cards:
            neg = h.startswith("¬ ")
            sub = Claim(claim.dir, h[2:] if neg else h, [], claim.definitions)
            submit(server, sub)
            cards[h] = sub.name("refute" if neg else "prove")
    hyps = list(claim.hypotheses)
    for row in selected(server, claim):
        prop = card_prop(row["formal_statement"])
        if prop is None:
            raise SystemExit(f"{row['theorem_name']} is not a claim card (`theorem X : H` or "
                             f"`theorem X : ¬ H`)")
        if prop in (claim.target, "¬ " + claim.target) or prop in cards:
            continue
        for m in imports_of(row["preamble"] or ""):
            if m.startswith("Definitions.Def_") and m[16:] in claim.definitions:
                d = server.definition(m[16:])
                if d is not None and d["definition"] != claim.definitions[m[16:]]:
                    raise SystemExit(f"{row['theorem_name']} imports a definition {m[16:]} that "
                                     "differs from the claim's")
        fetch_definitions(server, claim, row["preamble"] or "")
        hyps.append(prop)
        cards[prop] = row["theorem_name"]
    c = json.loads((claim.dir / "claim.json").read_text())
    c.update(hypotheses=hyps, cards=cards, resolvedAt=time.strftime("%Y-%m-%dT%H:%M:%SZ",
                                                                    time.gmtime()))
    (claim.dir / "claim.json").write_text(json.dumps(c, indent=1, ensure_ascii=False) + "\n")
    return Claim.load(claim.dir)


def submit(server: Server, claim: Claim) -> dict:
    """Fix the hypotheses (`resolve`), publish the definitions (each after those it imports) and
    the two cards; skip what is already there unchanged. Returns the cards' theorem ids."""
    if claim.hypotheses or claim.select:
        claim = resolve(server, claim)
    done: set[str] = set()

    def publish_def(n: str) -> None:
        if n in done:
            return
        done.add(n)
        for m in imports_of(claim.definitions[n]):
            if m.startswith("Definitions.Def_") and m[16:] in claim.definitions:
                publish_def(m[16:])
        old = server.definition(n)
        if old is not None:
            if old["definition"] != claim.definitions[n]:
                raise SystemExit(f"the definition {n} exists with other text")
            return
        server.publish("/submit-definition", {"definition_name": n, "definition_title": n,
                                              "definition": claim.definitions[n]})
    for n in claim.definitions:
        publish_def(n)
    ids = {}
    for pol in ("prove", "refute"):
        name = claim.name(pol)
        stmt = claim.card_statement(name, pol == "refute") + " := by sorry"
        old = server.theorem(name)
        if old is not None:
            if (old["preamble"], old["formal_statement"]) != (claim.preamble, stmt):
                raise SystemExit(f"the theorem {name} exists with another statement")
            ids[pol] = old["theorem_id"]
            continue
        what = f"`{claim.target}`" if pol == "prove" else f"the negation of `{claim.target}`"
        ids[pol] = server.publish("/submit-problem", {
            "theorem_name": name, "theorem_title": f"Sigaba-Neo claim {claim.digest[:16]} ({pol})",
            "preamble": claim.preamble, "formal_statement": stmt,
            "natural_language_statement": f"{what} holds. A proof may be a sketch that reduces "
            "it to other claims' cards (`SigabaNeo.Claim_*`): a reduction to weaker assumptions."
            })["theorem_id"]
    return ids


# -- check --------------------------------------------------------------------------------------


@dataclass
class Download:
    """A proof as the server reports it: (theorem row, solution) nodes, root first; the leaves,
    cards that are hypotheses of the claim, left unproved; and every file to lay out."""

    server: Server
    claim: Claim
    nodes: list
    files: dict[str, str]
    leaves: dict[str, dict] = field(default_factory=dict)
    visiting: set[str] = field(default_factory=set)

    @property
    def allowed(self) -> set[str]:
        return set(self.claim.cards.values())

    def definitions(self, text: str) -> None:
        for m in imports_of(text):
            if m.startswith("Definitions.Def_") and m[16:] not in self.claim.definitions and \
                    f"Definitions/{m[12:]}.lean" not in self.files:
                d = self.server.definition(m[16:])
                if d is not None:
                    self.files[f"Definitions/{m[12:]}.lean"] = d["definition"]
                    self.definitions(d["definition"])

    def proof(self, row: dict, disproof: bool = False) -> bool:
        """Find an accepted solution (or sketch) of `row` whose imported theorems are, recursively,
        proved this way or hypotheses of the claim (leaves). The graph is shared, so reductions
        recorded by different agents compose; a cycle is no proof."""
        name = row["theorem_name"]
        if name in self.visiting:
            return False
        if any(n[0]["theorem_name"] == name for n in self.nodes):
            return True
        self.visiting.add(name)
        try:
            for sub in self.server.accepted(row["theorem_id"]):
                content = self.server.solution(sub["id"])
                kids = [] if disproof else [self.server.theorem_by_slug(m[13:])
                                            for m in imports_of(content) if m.startswith("Theorems.Thm_")]
                if not all(kids):
                    continue
                saved = (list(self.nodes), dict(self.files), dict(self.leaves))
                self.nodes.append((row, content))
                self.definitions(content)
                if all(self.kid(k) for k in kids):
                    return True
                self.nodes, self.files, self.leaves = saved
            return False
        finally:
            self.visiting.discard(name)

    def kid(self, k: dict) -> bool:
        """An imported theorem: proved (recursively), or else a hypothesis of the claim."""
        self.definitions(k["preamble"] or "")
        if k["theorem_name"] in self.leaves:
            return True
        if (k["theorem_name"] not in self.allowed or k["status"] == "Proved") and self.proof(k):
            return True
        if k["theorem_name"] in self.allowed:
            self.leaves[k["theorem_name"]] = k
            return True
        return False

    def layout(self, refute: bool, disproof_of_negation: bool = False) -> dict[str, str]:
        """Prove2Me's layout, with each solution in its own namespace (all declare `solution`),
        each imported statement closed by its solution (`p2m_apply%`, SigabaNeo/Assemble.lean), each
        hypothesis card an axiom of its statement (the trusted check accepts axioms whose type is
        a hypothesis), and `Claim.proof` stating the claim `H₀ → … → C`. Untrusted: a wrong
        layout only fails to build or to check."""
        files = dict(self.files)
        files.update({f"Definitions/Def_{n}.lean": t for n, t in self.claim.definitions.items()})
        for i, (row, content) in enumerate(self.nodes):
            ns = f"Solutions.Sol_{slug(row['theorem_name'])}"
            mods, rest = split_header(content)
            files[ns.replace(".", "/") + ".lean"] = (
                "".join(f"import {m}\n" for m in mods) + f"namespace {ns}\n{rest}\nend {ns}\n")
            if i > 0:
                mods, rest = split_header(row["preamble"] or "")
                stmt = re.sub(r":=\s*by\s+sorry\s*$", f":= p2m_apply% {ns}.solution",
                              row["formal_statement"].rstrip())
                files[f"Theorems/Thm_{slug(row['theorem_name'])}.lean"] = "".join(
                    f"import {m}\n" for m in [*mods, ns, "SigabaNeo.Assemble"]) + rest + "\n\n" + stmt + "\n"
        for name, row in self.leaves.items():
            mods, rest = split_header(row["preamble"] or "")
            stmt = re.sub(r":=\s*by\s+sorry\s*$", "", row["formal_statement"].rstrip())
            files[f"Theorems/Thm_{slug(name)}.lean"] = "".join(f"import {m}\n" for m in mods) + \
                rest + "\n\n" + re.sub(r"^\s*theorem\b", "axiom", stmt) + "\n"
        root = f"Solutions.Sol_{slug(self.nodes[0][0]['theorem_name'])}"
        value = f"Classical.byContradiction {root}.solution" if disproof_of_negation \
            else f"{root}.solution"
        files["Claim.lean"] = (f"import {root}\n\n"
                               f"{self.claim.statement('Claim.proof', refute)} := {value}\n")
        return files


def verify(workdir: Path, claim: Claim, files: dict[str, str], module: str = "Claim",
           theorem: str = "Claim.proof") -> dict:
    """Lay the claim's definition files and `files` out in a Lake workspace that requires the core,
    build `module`, and run the trusted `#sigaba_neo_check` on `claim.dir`. Returns its result, with
    its printed report as `report`."""
    files = {**files, **{f"Definitions/Def_{n}.lean": t for n, t in claim.definitions.items()}}
    workdir.mkdir(parents=True, exist_ok=True)
    libs = sorted({f.split("/")[0].removesuffix(".lean") for f in files})
    (workdir / "lakefile.toml").write_text(
        f'name = "check"\n\n[[require]]\nname = "SigabaNeo"\npath = {json.dumps(str(CORE))}\n' +
        "".join(f'\n[[lean_lib]]\nname = "{lib}"\n' for lib in libs))
    manifest = json.loads((CORE / "lake-manifest.json").read_text())
    manifest.update(name="check", packages=[
        {"type": "path", "scope": "", "name": "SigabaNeo", "manifestFile": "lake-manifest.json",
         "inherited": False, "dir": str(CORE), "configFile": "lakefile.toml"},
        *[dict(p, inherited=True) for p in manifest["packages"]]])
    (workdir / "lake-manifest.json").write_text(json.dumps(manifest, indent=1))
    (workdir / "lean-toolchain").write_text((CORE / "lean-toolchain").read_text())
    (workdir / ".lake" / "packages").mkdir(parents=True, exist_ok=True)
    for p in (CORE / ".lake" / "packages").iterdir():    # the core's built packages
        if not (dst := workdir / ".lake" / "packages" / p.name).exists():
            dst.symlink_to(p)
    for rel, text in files.items():
        if ".." in Path(rel).parts or Path(rel).is_absolute():
            raise SystemExit(f"unsafe path {rel}")
        (workdir / rel).parent.mkdir(parents=True, exist_ok=True)
        (workdir / rel).write_text(text)
    env = {k: v for k, v in os.environ.items() if k not in ("LEAN_PATH", "LEAN_SRC_PATH")}
    run = lambda *a, **k: subprocess.run(a, cwd=workdir, env=env, text=True,  # noqa: E731
                                         capture_output=True, **k)
    b = run("lake", "build", module)
    if b.returncode != 0:
        errs = [l for l in (b.stdout + b.stderr).splitlines() if l.startswith("error")]
        return {"verdict": "rejected", "report": "the build failed:\n" + "\n".join(errs[:30])}
    (workdir / "result.json").unlink(missing_ok=True)
    r = run("lake", "env", "lean", "--stdin", input="import SigabaNeo.Trusted.Check\n"
            f"#sigaba_neo_check {json.dumps(str(claim.dir))} {json.dumps(module)} {json.dumps(theorem)}\n")
    if not (workdir / "result.json").exists():
        return {"verdict": "rejected", "report": (r.stdout + r.stderr)[-3000:]}
    return {**json.loads((workdir / "result.json").read_text()), "report": r.stdout.strip()}


def dev(claim_dir: Path) -> None:
    """Make the claim directory a Lake project that requires the core (paths relative to it)."""
    d = claim_dir.resolve()
    rel = os.path.relpath(CORE, d)
    (d / "lakefile.toml").write_text(
        f'name = "claim"\npackagesDir = {json.dumps(rel + "/.lake/packages")}\n\n'
        f'[[require]]\nname = "SigabaNeo"\npath = {json.dumps(rel)}\n\n'
        '[[lean_lib]]\nname = "Definitions"\n\n'
        '[[lean_lib]]\nname = "Solution"\n')
    manifest = json.loads((CORE / "lake-manifest.json").read_text())
    manifest.update(name="claim", packagesDir=rel + "/.lake/packages", packages=[
        {"type": "path", "scope": "", "name": "SigabaNeo", "manifestFile": "lake-manifest.json",
         "inherited": False, "dir": rel, "configFile": "lakefile.toml"},
        *[dict(p, inherited=True) for p in manifest["packages"]]])
    (d / "lake-manifest.json").write_text(json.dumps(manifest, indent=1) + "\n")
    (d / "lean-toolchain").write_text((CORE / "lean-toolchain").read_text())


def check(server: Server, claim: Claim, workdir: Path) -> dict:
    """The status of both cards; every proof the server reports, checked. A proof may be a sketch
    whose unproved leaves are hypotheses of the claim."""
    if not claim.resolved:
        raise SystemExit("the claim's hypotheses are not fixed yet: run `submit` first")
    cards = []
    for pol in ("prove", "refute"):
        row = server.theorem(claim.name(pol))
        card = {"polarity": pol, "theorem_name": claim.name(pol),
                "status": (row or {}).get("status", "unpublished"), "verified": False}
        if row is not None:
            disproof = row["status"] == "Disproved"
            dl = Download(server, claim, [], {})
            if not dl.proof(row, disproof=disproof):
                if row["status"] != "Open" or server.accepted(row["theorem_id"]):
                    card["problems"] = ["no complete proof could be downloaded"]
            else:
                # A disproof of a card proves the negation of its statement.
                refute = (pol == "refute") != disproof
                r = verify(workdir / pol, claim, dl.layout(refute, disproof and pol == "refute"))
                card.update(verified=r["verdict"] == "verified", outcome=r.get("outcome"),
                            report=r["report"], nodes=[n[0]["theorem_name"] for n in dl.nodes],
                            hypotheses=sorted(dl.leaves))
        cards.append(card)
    # The outcomes are the trusted check's own (see each `report`).
    outcomes = {c["outcome"] for c in cards if c["verified"]}
    outcome = "inconsistent" if len(outcomes) == 2 else outcomes.pop() if outcomes else "open"
    return {"claim": str(claim.dir), "outcome": outcome, "cards": cards}


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("action", choices=["submit", "check", "dev"])
    ap.add_argument("claim", type=Path, help="the claim directory (claim.json, Definitions/)")
    ap.add_argument("--api", default=os.environ.get("PROVE2ME_API", "http://127.0.0.1:8090/api/v1"))
    ap.add_argument("--workdir", type=Path, default=Path("sigaba-neo-work"))
    a = ap.parse_args(argv)
    if a.action == "dev":
        dev(a.claim)
        print(f"{a.claim}: Lake project written; `lake build` there builds the claim's files")
        return 0
    claim = Claim.load(a.claim)
    server = Server(a.api, os.environ.get("PROVE2ME_TOKEN"))
    if a.action == "submit":
        print(json.dumps(submit(server, claim), indent=1))
        return 0
    out = check(server, claim, a.workdir.resolve())
    for c in out["cards"]:
        print(f"== {c['theorem_name']}: {c['status']}")
        for line in [c.get("report", ""), *c.get("problems", [])]:
            if line:
                print(line)
    print(f"== outcome: {out['outcome']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
