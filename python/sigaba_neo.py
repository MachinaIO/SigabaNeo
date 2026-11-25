#!/usr/bin/env python3
"""The submitter's tool (docs/DESIGN.md, docs/GITHUB_PLATFORM.md). Standard library only.

    python3 sigaba_neo.py submit CLAIM --dag DAG [--pr]
    python3 sigaba_neo.py check  CLAIM --dag DAG [--records RECORDS] [--env ID]
    python3 sigaba_neo.py dev    CLAIM

`CLAIM` is the submitter's claim directory: `claim.json` (`{"target": "T", "hypotheses": [...],
"select": [...]}`) and `Definitions/Def_*.lean` (Prove2Me's format). `DAG` is a checkout of the DAG
repository (for `submit`, a clone of your fork); `RECORDS` a checkout of its `records` branch.

* `submit` fixes the hypotheses (each stands for another claim's card; `select` chooses cards in
  the DAG) and writes them back to `claim.json`. Then it writes the definitions and the two cards
  into `DAG` as nodes, theorems ending in `:= by sorry`: `SigabaNeo.Claim_<d>.prove : T` and
  `SigabaNeo.Claim_<d>.refute : ¬ T`. The cards are the proposition's (`<d>` covers the target and
  the definitions), shared by every claim of it; reductions are sketches between cards. With
  `--pr`, it commits them on a new branch, pushes it to `origin` and opens a pull request (`gh`).
* `check` reads both cards in `DAG`. For each, it takes a solution or sketch (those the records
  verified in the environment first), the theorems it imports with theirs (recursively, through
  reductions, down to the hypotheses' cards, which become axioms of their statements; no other card
  may stay unproved), and the definitions they import; lays them out in a Lake workspace that
  requires the core; and runs the trusted `#sigaba_neo_check` there on `CLAIM`, printing its report
  as it is. The records only order the candidates: every proof is built and checked here.

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
import shutil
import stat
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path

import dag as D

CORE = Path(__file__).resolve().parents[1]      # a built checkout of the core
SUBSCRIPT = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")


slug = D.slug
imports_of = D.imports_of
split_header = D.split_header


# -- the claim ----------------------------------------------------------------------------------


@dataclass
class Claim:
    dir: Path
    target: str
    hypotheses: list[str]                        # `H` or `¬ H`, Lean names
    definitions: dict[str, str]                  # definition name -> Lean text
    cards: dict[str, str] = field(default_factory=dict)   # hypothesis -> the card it stands for
    select: list[dict] = field(default_factory=list)      # hypotheses chosen in the DAG
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


# -- the DAG ------------------------------------------------------------------------------------


def split_statement(text: str) -> tuple[str, str]:
    """A theorem file as (preamble, statement): the statement starts at its `theorem`."""
    lines = text.split("\n")
    i = next((i for i, l in enumerate(lines) if re.match(r"(theorem|lemma)\s", l)), len(lines))
    return "\n".join(lines[:i]).rstrip() + "\n", "\n".join(lines[i:]).strip()


class DagSource:
    """A DAG checkout, as `submit` and `check` read it: theorems as rows (`theorem_name`,
    `preamble`, `formal_statement`, `status`), definitions, and solutions. With records, statuses are
    those of the environment, and the solutions verified there come first; without, every
    solution file is a candidate. Either way, every proof is built and checked."""

    def __init__(self, root: Path, records: Path | None = None, env_id: str | None = None):
        self.dag = D.Dag(root)
        recs = D.read_records(records)
        env = self.dag.environment(env_id)
        self.status = D.status(self.dag, recs, env) if env is not None and recs else None
        self.env = env

    def row(self, node: D.Node) -> dict:
        pre, stmt = split_statement(node.text)
        st = self.status.theorems.get(node.name, {}).get("status", "Open") if self.status \
            else "Unknown"
        return {"theorem_name": node.name, "theorem_id": node.path, "preamble": pre,
                "formal_statement": stmt, "status": st, "path": node.path}

    def theorem(self, name: str) -> dict | None:
        n = self.dag.theorem(name)
        return None if n is None else self.row(n)

    def theorem_by_slug(self, s: str) -> dict | None:
        n = self.dag.theorem_by_slug(s)
        return None if n is None else self.row(n)

    def definition(self, name: str) -> dict | None:
        n = self.dag.definition(name)
        return None if n is None else {"definition_name": name, "definition": n.text}

    def accepted(self, row: dict, proof_type: str | None = None) -> list[dict]:
        """The solutions of a theorem: verified ones first (complete before sketches)."""
        node = self.dag.theorem(row["theorem_name"])
        if node is None:
            return []
        out = []
        for s in self.dag.solutions(node):
            pt = s.meta.get("proof_type", "prove")
            if proof_type is not None and pt != proof_type:
                continue
            rec = self.status.solutions.get(s.path) if self.status else None
            rank = (0 if rec and rec["status"] == "ACCEPTED" else 1 if rec else 2)
            out.append({"id": s.path, "content": s.text, "proof_type": pt, "rank": rank})
        return sorted(out, key=lambda x: (x["rank"], x["id"]))

    def sketches(self, name: str) -> int:
        node = self.dag.theorem(name)
        if node is None:
            return 0
        if self.status:
            return sum(1 for r in self.status.solutions.values()
                       if r["theorem"] == name and r["status"] == "SKETCH_ACCEPTED")
        return len(self.dag.solutions(node))

    def commit(self) -> str | None:
        r = subprocess.run(["git", "-C", str(self.dag.root), "rev-parse", "HEAD"], text=True,
                           capture_output=True)
        return r.stdout.strip() if r.returncode == 0 else None


# -- submit -------------------------------------------------------------------------------------

SELECTOR_KEYS = {"id", "tag", "minYears", "minRefuteSketches"}
CLAIM_RE = re.compile(r"SigabaNeo\.Claim_[0-9a-f]{16}\.prove")


def selected(src: DagSource, claim: Claim) -> list[dict]:
    """The cards the selectors choose. `{"id": X}` is one card (a theorem name, prove or refute).
    The other keys choose among the claims' prove cards in the DAG, all of the keys of one selector
    at once: `tag` (the maintainers' tag in meta/assumptions.json, such as `well-established`),
    `minYears` (first proposed at least that many years ago), `minRefuteSketches` (at least that
    many sketches on its refute card). Those exclude claims that are refuted or disproved."""
    out = []
    meta = src.dag.read_json("meta/assumptions.json", {"claims": {}})["claims"]
    year = time.gmtime().tm_year
    for sel in claim.select:
        if not isinstance(sel, dict) or not sel or set(sel) - SELECTOR_KEYS:
            raise SystemExit(f"bad selector {sel!r}: keys are {sorted(SELECTOR_KEYS)}")
        if "id" in sel:
            if len(sel) > 1:
                raise SystemExit(f"bad selector {sel!r}: `id` stands alone")
            row = src.theorem(str(sel["id"]))
            if row is None:
                raise SystemExit(f"selector {sel!r}: no such theorem in the DAG")
            out.append(row)
            continue
        for t in src.dag.by_kind("theorem"):
            if not CLAIM_RE.fullmatch(t.name):
                continue
            row = src.row(t)
            ref = src.theorem(t.name[: -len("prove")] + "refute")
            m = meta.get(t.name, {})
            if row["status"] == "Disproved" or (ref or {}).get("status") == "Proved":
                continue
            if "tag" in sel and sel["tag"] not in m.get("tags", []):
                continue
            if "minYears" in sel and (m.get("proposed_year") is None or
                                      year - m["proposed_year"] < sel["minYears"]):
                continue
            if "minRefuteSketches" in sel and (ref is None or
                                               src.sketches(ref["theorem_name"]) <
                                               sel["minRefuteSketches"]):
                continue
            out.append(row)
    return out


def fetch_definitions(src: DagSource, claim: Claim, text: str) -> None:
    """Copy the definitions `text` imports (recursively) into the claim directory."""
    for m in imports_of(text):
        if not m.startswith("Definitions.Def_") or m[16:] in claim.definitions:
            continue
        d = src.definition(m[16:])
        if d is None:
            raise SystemExit(f"the DAG has no definition {m[16:]}")
        claim.definitions[m[16:]] = d["definition"]
        (claim.dir / "Definitions" / f"Def_{m[16:]}.lean").write_text(d["definition"])
        fetch_definitions(src, claim, d["definition"])


def resolve(src: DagSource, claim: Claim, written: list[str]) -> Claim:
    """Fix the hypotheses: each stands for a card. A hypothesis written in `claim.json` becomes a
    claim of its own (its prove card, or for `¬ H` its refute card); a selected card brings its
    definitions into `Definitions/`. The result is written back to `claim.json` (`hypotheses`,
    `cards`, `resolvedAt`, `dag`), and is not resolved again."""
    if claim.resolved:
        return claim
    cards = dict(claim.cards)
    for h in claim.hypotheses:
        if h not in cards:
            neg = h.startswith("¬ ")
            sub = Claim(claim.dir, h[2:] if neg else h, [], claim.definitions)
            written += write_claim(src, sub)
            cards[h] = sub.name("refute" if neg else "prove")
    hyps = list(claim.hypotheses)
    for row in selected(src, claim):
        prop = card_prop(row["formal_statement"])
        if prop is None:
            raise SystemExit(f"{row['theorem_name']} is not a claim card (`theorem X : H` or "
                             f"`theorem X : ¬ H`)")
        if prop in (claim.target, "¬ " + claim.target) or prop in cards:
            continue
        for m in imports_of(row["preamble"] or ""):
            if m.startswith("Definitions.Def_") and m[16:] in claim.definitions:
                d = src.definition(m[16:])
                if d is not None and d["definition"] != claim.definitions[m[16:]]:
                    raise SystemExit(f"{row['theorem_name']} imports a definition {m[16:]} that "
                                     "differs from the claim's")
        fetch_definitions(src, claim, row["preamble"] or "")
        hyps.append(prop)
        cards[prop] = row["theorem_name"]
    c = json.loads((claim.dir / "claim.json").read_text())
    c.update(hypotheses=hyps, cards=cards, dag=src.commit(),
             resolvedAt=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
    (claim.dir / "claim.json").write_text(json.dumps(c, indent=1, ensure_ascii=False) + "\n")
    return Claim.load(claim.dir)


def write_node(root: Path, path: str, text: str, meta: dict) -> bool:
    """Write a node unless it is there with the same text; False if it is there already."""
    p = root / path
    if p.exists():
        if p.read_text() != text:
            raise SystemExit(f"{path} exists in the DAG with other content")
        return False
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)
    p.with_suffix(".json").write_text(json.dumps(meta, indent=1, ensure_ascii=False) + "\n")
    return True


def write_claim(src: DagSource, claim: Claim) -> list[str]:
    """The claim's definitions and its two cards, as DAG nodes. Returns the paths written."""
    root, out = src.dag.root, []
    for n, text in sorted(claim.definitions.items()):
        if write_node(root, f"dag/Definitions/Def_{n}.lean", text, {"name": n, "title": n}):
            out.append(f"dag/Definitions/Def_{n}.lean")
    for pol in ("prove", "refute"):
        name = claim.name(pol)
        stmt = claim.card_statement(name, pol == "refute") + " := by sorry"
        what = f"`{claim.target}`" if pol == "prove" else f"the negation of `{claim.target}`"
        path = f"dag/Theorems/Thm_{slug(name)}.lean"
        if write_node(root, path, claim.preamble + "\n\n" + stmt + "\n", {
                "name": name, "title": f"Sigaba-Neo claim {claim.digest[:16]} ({pol})",
                "statement": f"{what} holds. A proof may be a sketch that reduces it to other "
                             "claims' cards (`SigabaNeo.Claim_*`): a reduction to weaker assumptions."}):
            out.append(path)
    return out


def submit(src: DagSource, claim: Claim, pr: bool = False) -> dict:
    """Fix the hypotheses (`resolve`), and write the definitions and the two cards into the DAG
    checkout; what is there already with the same text is skipped. With `pr`, commit them on a new
    branch, push it to `origin` and open a pull request."""
    written: list[str] = []
    if claim.hypotheses or claim.select:
        claim = resolve(src, claim, written)
    written += write_claim(src, claim)
    out = {"cards": {pol: claim.name(pol) for pol in ("prove", "refute")}, "written": written}
    if pr and written:
        root = str(src.dag.root)
        branch = f"claim-{claim.digest[:16]}"
        git = lambda *a: subprocess.run(["git", "-C", root, *a], check=True)  # noqa: E731
        git("checkout", "-b", branch)
        git("add", *written, *[w.removesuffix(".lean") + ".json" for w in written])
        git("commit", "-m", f"Claim {claim.digest[:16]}: definitions and cards")
        git("push", "-u", "origin", branch)
        subprocess.run(["gh", "pr", "create", "--fill", "--head", branch], cwd=root, check=True)
        out["branch"] = branch
    return out


# -- check --------------------------------------------------------------------------------------


@dataclass
class Download:
    """A proof as the DAG holds it: (theorem row, solution) nodes, root first; the leaves, cards
    that are hypotheses of the claim, left unproved; and every file to lay out."""

    src: DagSource
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
                d = self.src.definition(m[16:])
                if d is not None:
                    self.files[f"Definitions/{m[12:]}.lean"] = d["definition"]
                    self.definitions(d["definition"])

    def proof(self, row: dict, disproof: bool = False) -> bool:
        """Find a solution (or sketch) of `row` whose imported theorems are, recursively, proved
        this way or hypotheses of the claim (leaves). The graph is shared, so reductions recorded
        by different agents compose; a cycle is no proof."""
        name = row["theorem_name"]
        if name in self.visiting:
            return False
        if any(n[0]["theorem_name"] == name for n in self.nodes):
            return True
        self.visiting.add(name)
        try:
            for sub in self.src.accepted(row, "disprove" if disproof else "prove"):
                content = sub["content"]
                kids = [] if disproof else [self.src.theorem_by_slug(m[13:])
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


def sandbox_prefix(workdir: Path, read_only: list[Path], visible: list[Path] = (),
                   env: dict[str, str] | None = None) -> list[str]:
    """A bubblewrap sandbox for building untrusted Lean, built from an empty root. It holds only
    what a build needs, read only: the system's programs and libraries (`/usr`, `/etc`), the
    toolchain (elan), the core and its packages; the workspace is writable except `read_only`.
    Nothing else of the host is there: not the home directory (claims, credentials), not `/run`
    (sockets such as Docker's), not `/tmp`. No network, its own processes, killed with its parent,
    and only an allowlisted environment."""
    bwrap = shutil.which("bwrap")
    if bwrap is None:
        raise SystemExit("bubblewrap (bwrap) is needed to build untrusted proofs in a sandbox; "
                         "install it, or pass --no-sandbox to build without one (then a proof "
                         "can tamper with the check's inputs, docs/DESIGN.md)")
    elan = Path(os.environ.get("ELAN_HOME") or Path.home() / ".elan").resolve()
    args = [bwrap, "--unshare-all", "--die-with-parent", "--new-session", "--clearenv",
            "--ro-bind", "/usr", "/usr", "--ro-bind", "/etc", "/etc"]
    for top in ("/bin", "/sbin", "/lib", "/lib64", "/lib32"):
        p = Path(top)
        if p.is_symlink():
            args += ["--symlink", os.readlink(p), top]
        elif p.is_dir():
            args += ["--ro-bind", top, top]
    args += ["--dev", "/dev", "--proc", "/proc", "--tmpfs", "/tmp"]
    trees = [elan, CORE.resolve(), (CORE / ".lake" / "packages").resolve()]
    for t in dict.fromkeys(trees):
        args += ["--ro-bind", str(t), str(t)]
    for p in visible:                    # read-only inputs from elsewhere (the claim)
        args += ["--ro-bind", str(p), str(p)]
    args += ["--bind", str(workdir), str(workdir)]
    for p in read_only:
        args += ["--ro-bind", str(p), str(p)]
    for k, v in (env or {}).items():
        args += ["--setenv", k, v]
    return args + ["--setenv", "PATH", f"{elan}/bin:/usr/bin:/bin", "--setenv", "HOME", "/tmp",
                   "--setenv", "ELAN_HOME", str(elan), "--setenv", "LANG", "C.UTF-8",
                   "--chdir", str(workdir), "--"]


_TRUSTED_LEAN: tuple[str, str] | None = None


def trusted_lean() -> tuple[str, str]:
    """The Lean executable and module search path of this checkout's core: computed by Lake in the
    core itself, never in a workspace a proof was built in. The core's packages come first."""
    global _TRUSTED_LEAN
    if _TRUSTED_LEAN is None:
        env = {k: v for k, v in os.environ.items() if k not in ("LEAN_PATH", "LEAN_SRC_PATH")}
        r = subprocess.run(["lake", "env", "sh", "-c", 'command -v lean; printf "%s" "$LEAN_PATH"'],
                           cwd=CORE, env=env, text=True, capture_output=True)
        lines = r.stdout.splitlines()
        if r.returncode != 0 or len(lines) < 2 or not Path(lines[0]).is_file():
            raise SystemExit(f"cannot locate the core's Lean: {r.stderr[-1000:]}")
        _TRUSTED_LEAN = (lines[0], lines[1])
    return _TRUSTED_LEAN


def real_tree(base: Path, *parts: str) -> Path | None:
    """`base/parts…` if every component below `base` is a directory and none is a symbolic link
    (checked with lstat, so nothing is followed); None otherwise. Used once no process of a build
    is left, so nothing can change the tree in between."""
    p = base
    for part in parts:
        p = p / part
        try:
            if not stat.S_ISDIR(os.lstat(p).st_mode):
                return None
        except OSError:
            return None
    return p


def export_outputs(src: Path, dst: Path, roots: list[str], skip: set[str] = frozenset()) -> None:
    """Copy the build outputs of the workspace's own modules (the roots `roots`) as regular files:
    no symbolic link is followed or copied, nothing outside those roots is taken, and nothing of
    the modules `skip` (`Definitions/Def_X`, by path without extension) nor anything already in
    `dst` is overwritten."""
    for root in roots:
        for p in src.glob(f"{root}.*"):
            if p.is_file() and not p.is_symlink():
                shutil.copyfile(p, dst / p.name)
        top = src / root
        if top.is_symlink() or not top.is_dir():
            continue
        for d, dirs, names in os.walk(top, followlinks=False):
            dirs[:] = [x for x in dirs if not (Path(d) / x).is_symlink()]
            for n in names:
                p = Path(d) / n
                rel = p.relative_to(src)
                if str(rel.parent / rel.name.split(".")[0]) in skip:
                    continue
                if p.is_file() and not p.is_symlink():
                    out = dst / rel
                    if out.exists():
                        continue
                    out.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(p, out)


def verify(parent: Path, claim: Claim, files: dict[str, str], module: str = "Claim",
           theorem: str = "Claim.proof", sandbox: bool = True, keep: bool = False) -> dict:
    """Lay the claim's definition files and `files` out in a Lake workspace that requires the core,
    build `module`, and run the trusted `#sigaba_neo_check` on `claim.dir`. Returns its result, with
    its printed report as `report`.

    Every call builds in a new directory under `parent` and checks in another, both created here
    and removed afterwards (unless `keep`, which leaves the workspace's path in `workspace`):
    nothing a build left behind is ever reused or touched by the unsandboxed setup.

    Building runs the files' code, so it happens in a sandbox (`sandbox_prefix`), in two steps: the
    claim's definitions first, then, with their sources and build outputs read only, everything
    else.

    The check runs afterwards, outside, when no process of the builds is left, and nothing of the
    workspace's configuration is used: in the second directory, which holds only copies of the
    build outputs of the workspace's own modules, with the core's Lean executable and search path
    (the core's packages first, so that no built module can stand in for one of theirs). Its report
    counts only if it exits normally."""
    parent = parent.resolve()
    for a, b in ((parent, claim.dir), (claim.dir, parent), (parent, CORE), (CORE, parent)):
        if a == b or a in b.parents:
            raise SystemExit(f"the work directory {parent} may not contain or be inside {b}")
    parent.mkdir(parents=True, exist_ok=True)
    workdir = checkdir = None
    try:
        workdir = Path(tempfile.mkdtemp(prefix="build-", dir=parent))
        checkdir = Path(tempfile.mkdtemp(prefix="check-", dir=parent))
        r = _verify_in(workdir, checkdir, claim, files, module, theorem, sandbox)
        return {**r, "workspace": str(workdir)} if keep else r
    finally:
        if checkdir is not None:
            shutil.rmtree(checkdir, ignore_errors=True)
        if workdir is not None and not keep:
            shutil.rmtree(workdir, ignore_errors=True)


def _verify_in(workdir: Path, checkdir: Path, claim: Claim, files: dict[str, str], module: str,
               theorem: str, sandbox: bool) -> dict:
    """`verify` in two fresh directories: `workdir` to build in, `checkdir` to check in."""
    files = {**files, **{f"Definitions/Def_{n}.lean": t for n, t in claim.definitions.items()}}
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

    def run(*a: str, ro: list[Path] | None = None, **k):
        prefix = sandbox_prefix(workdir, ro or []) if sandbox else []
        return subprocess.run([*prefix, *a], cwd=workdir, env=env, text=True, capture_output=True,
                              **k)

    def failed(b) -> dict:
        errs = [l for l in (b.stdout + b.stderr).splitlines() if l.startswith("error")]
        return {"verdict": "rejected", "report": "the build failed:\n" + "\n".join(errs[:30] or
                                                 (b.stdout + b.stderr).splitlines()[-30:])}

    # The first step builds the submitter's own files only: a claim's definition may import no
    # other definition (the check would reject it anyway).
    for n, text in claim.definitions.items():
        for m in imports_of(text):
            if m.startswith("Definitions.") and m.removeprefix("Definitions.Def_") not in \
                    claim.definitions:
                return {"verdict": "rejected", "report": f"the claim's definition {n} imports {m}, "
                        "which is not one of the claim's definitions"}
    sources = [workdir / "Definitions" / f"Def_{n}.lean" for n in sorted(claim.definitions)]  # noqa
    config = [workdir / "lakefile.toml", workdir / "lake-manifest.json", workdir / "lean-toolchain",
              workdir / ".lake" / "packages", *sources]
    defs = [f"Definitions.Def_{n}" for n in sorted(claim.definitions)]
    b = run("lake", "build", *defs, ro=config)
    if b.returncode != 0:
        return failed(b)
    # The claim's definitions are taken now, from the first step, which ran only the submitter's
    # files: their build outputs and their sources (from the claim itself). Nothing the second step
    # leaves under their names is ever used.
    own = {f"Def_{n}" for n in claim.definitions}
    outputs = checkdir / ".lake" / "build" / "lib" / "lean"
    (outputs / "Definitions").mkdir(parents=True)
    defs_dir = real_tree(workdir, ".lake", "build", "lib", "lean", "Definitions")
    if defs_dir is None:
        return {"verdict": "rejected", "report": "the build outputs are not plain directories"}
    for p in defs_dir.iterdir():
        if p.name.split(".")[0] in own and p.is_file() and not p.is_symlink():
            shutil.copyfile(p, outputs / "Definitions" / p.name)
    (checkdir / "Definitions").mkdir()
    for n, text in claim.definitions.items():   # the check compares them with the claim's files
        (checkdir / "Definitions" / f"Def_{n}.lean").write_text(text)
    protected = sorted(p for p in (workdir / ".lake" / "build").rglob("*")
                       if p.is_file() and p.parent.name == "Definitions" and
                       p.name.split(".")[0] in own)
    b = run("lake", "build", module, ro=config + protected)
    if b.returncode != 0:
        return failed(b)
    # The check: the fresh directory, copies of the workspace's own other outputs, the core's Lean.
    built = real_tree(workdir, ".lake", "build", "lib", "lean")   # the build may have replaced
    if built is None:                                              # any part of the path
        return {"verdict": "rejected", "report": "the build outputs are not plain directories"}
    export_outputs(built, outputs, libs, skip={f"Definitions/{d}" for d in own})
    # The check loads build outputs the proof's code could have written: it runs in a sandbox of
    # its own too (it sees the claim, read only, and writes only its directory), so that a
    # malformed file cannot reach the host. Its verdict still rests on Lean's loader reading those
    # files faithfully (docs/DESIGN.md, "Building is sandboxed").
    lean, path = trusted_lean()
    lean_path = path + os.pathsep + str(outputs)
    prefix = sandbox_prefix(checkdir, [], visible=[claim.dir], env={"LEAN_PATH": lean_path}) \
        if sandbox else []
    r = subprocess.run([*prefix, lean, "--stdin"], cwd=checkdir, text=True, capture_output=True,
                       env={**env, "LEAN_PATH": lean_path}, input=(
        "import SigabaNeo.Trusted.Check\n"
        f"#sigaba_neo_check {json.dumps(str(claim.dir))} {json.dumps(module)} {json.dumps(theorem)}\n"))
    result = read_regular(checkdir / "result.json") if r.returncode == 0 else None
    if result is None:
        return {"verdict": "rejected", "report": (r.stdout + r.stderr)[-3000:]}
    try:
        out = json.loads(result)
    except ValueError:
        return {"verdict": "rejected", "report": "the check's result is not JSON"}
    if not isinstance(out, dict):
        return {"verdict": "rejected", "report": "the check's result is not an object"}
    return {**out, "report": r.stdout.strip()}


def read_regular(path: Path, limit: int = 1 << 20) -> str | None:
    """The contents of `path` if it is a regular file (a symbolic link is not followed: the
    directory was writable by the sandbox), at most `limit` bytes; None otherwise."""
    try:
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    except OSError:
        return None
    try:
        if not stat.S_ISREG(os.fstat(fd).st_mode):
            return None
        data = os.read(fd, limit + 1)
        return None if len(data) > limit else data.decode("utf-8", "replace")
    finally:
        os.close(fd)


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


def check(src: DagSource, claim: Claim, workdir: Path, sandbox: bool = True) -> dict:
    """The status of both cards; every proof the DAG holds for them, checked. A proof may be a
    sketch whose unproved leaves are hypotheses of the claim."""
    if not claim.resolved:
        raise SystemExit("the claim's hypotheses are not fixed yet: run `submit` first")
    cards = []
    for pol in ("prove", "refute"):
        row = src.theorem(claim.name(pol))
        card = {"polarity": pol, "theorem_name": claim.name(pol),
                "status": (row or {}).get("status", "absent"), "verified": False}
        if row is not None:
            order = [True, False] if row["status"] == "Disproved" else [False, True]
            for disproof in order:
                dl = Download(src, claim, [], {})
                if not dl.proof(row, disproof=disproof):
                    continue
                # A disproof of a card proves the negation of its statement.
                refute = (pol == "refute") != disproof
                r = verify(workdir, claim,
                           dl.layout(refute, disproof and pol == "refute"), sandbox=sandbox)
                card.update(verified=r["verdict"] == "verified", outcome=r.get("outcome"),
                            report=r["report"], nodes=[n[0]["theorem_name"] for n in dl.nodes],
                            hypotheses=sorted(dl.leaves))
                if card["verified"]:
                    break
            else:
                if src.accepted(row):
                    card["problems"] = ["no complete proof could be assembled from the DAG"]
        cards.append(card)
    # The outcomes are the trusted check's own (see each `report`).
    outcomes = {c["outcome"] for c in cards if c["verified"]}
    outcome = "inconsistent" if len(outcomes) == 2 else outcomes.pop() if outcomes else "open"
    return {"claim": str(claim.dir), "dag": src.commit(),
            "env": (src.env or {}).get("id"), "outcome": outcome, "cards": cards}


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("action", choices=["submit", "check", "dev"])
    ap.add_argument("claim", type=Path, help="the claim directory (claim.json, Definitions/)")
    ap.add_argument("--dag", type=Path, help="a checkout of the DAG (for submit: of your fork)")
    ap.add_argument("--records", type=Path, help="a checkout of the DAG's records branch")
    ap.add_argument("--env", help="the environment (default: the DAG's default)")
    ap.add_argument("--pr", action="store_true", help="submit: commit, push and open a pull request")
    ap.add_argument("--workdir", type=Path, help="where to build and check (outside the core and "
                    "the claim; default: a new temporary directory, removed afterwards)")
    ap.add_argument("--no-sandbox", action="store_true",
                    help="check: build the proofs without bubblewrap (they can then tamper with "
                         "the check's inputs)")
    a = ap.parse_args(argv)
    if a.action == "dev":
        dev(a.claim)
        print(f"{a.claim}: Lake project written; `lake build` there builds the claim's files")
        return 0
    if a.dag is None:
        ap.error("--dag is required")
    claim = Claim.load(a.claim)
    src = DagSource(a.dag.resolve(), a.records, a.env)
    if a.action == "submit":
        print(json.dumps(submit(src, claim, a.pr), indent=1))
        return 0
    work = a.workdir.resolve() if a.workdir else Path(tempfile.mkdtemp(prefix="sigaba-neo-check-"))
    try:
        out = check(src, claim, work, sandbox=not a.no_sandbox)
    finally:
        if a.workdir is None:
            shutil.rmtree(work, ignore_errors=True)
    for c in out["cards"]:
        print(f"== {c['theorem_name']}: {c['status']}")
        for line in [c.get("report", ""), *c.get("problems", [])]:
            if line:
                print(line)
    print(f"== outcome: {out['outcome']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
