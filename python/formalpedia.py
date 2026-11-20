"""A mirror of Formalpedia, Prove2Me's daily export (https://github.com/prove2me/formalpedia).

The repository is large, so the mirror is a shallow partial clone: it has the trees (every file's
path and blob hash) but fetches a file's content only when it is read. A new snapshot's changes
are then the paths whose blob hash differs from the one last synced, with no download of the
unchanged files. Standard library and `git` only.

Layout of the export (its README): `envs/<env>/Definitions/Def_<slug>.lean`,
`envs/<env>/Theorems/Thm_<slug>.lean` (preamble and statement, ending in `:= by sorry`) and
`envs/<env>/Solutions/Sol_<slug>[_<n>].lean`, each under a provenance header of `--` comments.
"""

from __future__ import annotations

import json
import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

URL = "https://github.com/prove2me/formalpedia"


class Mirror:
    def __init__(self, url: str, d: Path):
        self.url, self.dir = url, d

    def git(self, *args: str) -> str:
        r = subprocess.run(["git", "-C", str(self.dir), *args], text=True, capture_output=True)
        if r.returncode != 0:
            raise RuntimeError(f"git {' '.join(args[:3])}: {r.stderr.strip()[-500:]}")
        return r.stdout

    def update(self) -> str:
        """Fetch the latest snapshot; its commit."""
        if not (self.dir / ".git").exists():
            self.dir.mkdir(parents=True, exist_ok=True)
            subprocess.run(["git", "init", "-q", str(self.dir)], check=True)
            self.git("remote", "add", "origin", self.url)
        try:
            self.git("fetch", "-q", "--depth", "1", "--filter=blob:none", "origin", "HEAD")
        except RuntimeError:        # a server without partial clone: fetch everything
            self.git("fetch", "-q", "--depth", "1", "origin", "HEAD")
        return self.git("rev-parse", "FETCH_HEAD").strip()

    def manifest(self, rev: str) -> dict:
        return json.loads(self.git("show", f"{rev}:MANIFEST.json"))

    def default_env(self, rev: str) -> str:
        envs = self.manifest(rev).get("environments", [])
        return next((e["dir"] for e in envs if e.get("is_default")), envs[0]["dir"] if envs else "")

    def files(self, rev: str, env: str) -> dict[str, str]:
        """path -> blob hash, for the definitions, theorems and solutions of `env`."""
        out = {}
        dirs = [f"envs/{env}/{d}" for d in ("Definitions", "Theorems", "Solutions")]
        for line in self.git("ls-tree", "-r", rev, "--", *dirs).splitlines():
            meta, path = line.split("\t", 1)
            if path.endswith(".lean"):
                out[path] = meta.split()[2]
        return out

    def read(self, blob: str) -> str:
        return self.git("cat-file", "-p", blob)


@dataclass
class Item:
    """One exported file: its provenance header and its Lean text."""
    kind: str                     # definition, theorem, solution
    name: str                     # the definition's or theorem's name (a solution's theorem)
    body: str                     # the Lean text without the header
    header: dict = field(default_factory=dict)

    @property
    def imports(self) -> list[str]:
        return [w for line in self.body.splitlines() if (ws := line.split())[:1] == ["import"]
                for w in ws[1:]]

    def split_statement(self) -> tuple[str, str] | None:
        """A theorem file as (preamble, statement): the statement starts at its `theorem`."""
        lines = self.body.split("\n")
        i = next((i for i, l in enumerate(lines) if re.match(r"(theorem|lemma)\s", l)), None)
        if i is None:
            return None
        return "\n".join(lines[:i]).rstrip() + "\n", "\n".join(lines[i:]).strip() + "\n"


def parse(path: str, text: str) -> Item:
    """An exported file. Its header is the leading block of `--` lines: `-- key : value` fields,
    and multi-line fields (`-- title:` followed by indented `--   ` lines)."""
    lines = text.split("\n")
    n = 0
    while n < len(lines) and lines[n].startswith("--"):
        n += 1
    fields: dict[str, list[str]] = {}
    key = None
    for l in lines[1:n]:
        m = re.match(r"--\s?(\w+)\s*:\s?(.*)$", l)
        if m and not l.startswith("--  "):
            key = m.group(1)
            fields[key] = [m.group(2).strip()]
        elif key is not None:
            fields[key].append(l[2:].strip())
    header = {k: "\n".join(v).strip() for k, v in fields.items()}
    body = "\n".join(lines[n:]).lstrip("\n")
    first = lines[0] if lines else ""
    if "/Solutions/" in path:
        m = re.search(r"solution \d+ for (\S+)", first)
        status = header.get("status", "")
        header["proof_type"] = "disprove" if "(disprove)" in status else "prove"
        header["status"] = status.split()[0] if status else ""
        return Item("solution", m.group(1) if m else "", body, header)
    kind = "definition" if "/Definitions/" in path else "theorem"
    return Item(kind, header.get("name", ""), body, header)
