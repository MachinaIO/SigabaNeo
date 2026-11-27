"""The agent side of the certified curriculum and notebook learning extension
(docs/LEARNING.md).

The DAG repository owns everything that decides: its `ci/learning/` package (routing, generator
certification, sampling, evaluation, statistics, activation, records, reports) runs in its CI
(`.github/workflows/learning.yml`), and only an administrator's bypass changes it. The core owns
the Lean side (`SigabaNeo.Trusted.Benchmark`, the commands of `SigabaNeo.Trusted.GeneratorCheck`,
`SigabaNeoStd.Benchmarks`) and this client, which:

- runs the DAG's own `ci/learning` code (from the controller's clean checkout of `main`) for the
  local, untrusted previews of what CI will decide (`sources`, `generator-list`, `status`,
  `report`, and `certify` on a generator directory);
- publishes a generator version or a notebook revision as a draft pull request from exactly the
  given files, with the user's GitHub login (the same rules as every other PR: collaborators only,
  CI decides, a maintainer merges).

It never computes a score, a certificate or an activation itself.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

from . import notebook as NB
from .remote import Git

ROLES = NB.ROLES
IDENT = re.compile(r"[a-z0-9][a-z0-9-]{0,62}")
VERSION_DIR = re.compile(r"v(\d{4})")
GENERATOR_FILES = ("manifest.json", "Generate.lean", "Certificate.lean")


class LearningError(Exception):
    pass


def generator_files(src: Path) -> tuple[str, dict[str, bytes]]:
    """The DAG path of a generator version directory and its three files, checked for shape
    (the DAG's CI checks everything again)."""
    src = Path(src).resolve()
    if not src.is_dir():
        raise LearningError(f"{src} is not a directory")
    names = sorted(p.name for p in src.iterdir())
    if names != sorted(GENERATOR_FILES):
        raise LearningError(f"{src} must hold exactly {', '.join(GENERATOR_FILES)} (has "
                            f"{', '.join(names)})")
    for n in GENERATOR_FILES:
        if (src / n).is_symlink():
            raise LearningError(f"{src / n} is a symbolic link")
    try:
        m = json.loads((src / "manifest.json").read_text())
    except (OSError, ValueError) as e:
        raise LearningError(f"manifest.json: {e}") from e
    role, fam, gid, ver = m.get("role"), m.get("family_id"), m.get("generator_id"), m.get("version")
    if role not in ROLES:
        raise LearningError("manifest: role must be design or cryptanalysis")
    if not (isinstance(fam, str) and IDENT.fullmatch(fam) and isinstance(gid, str) and
            IDENT.fullmatch(gid)):
        raise LearningError("manifest: family_id and generator_id must match [a-z0-9][a-z0-9-]*")
    if not (isinstance(ver, int) and 1 <= ver <= 9999):
        raise LearningError("manifest: version must be an integer in 1..9999")
    base = f"generators/{role}/{fam}/{gid}/v{ver:04d}"
    return base, {f"{base}/{n}": (src / n).read_bytes() for n in GENERATOR_FILES}


class Learning:
    def __init__(self, ctl):
        self.ctl = ctl

    # -- the DAG's own CI code ------------------------------------------------------------------
    def dag_ci(self, *args: str, cwd: Path | None = None, check: bool = True) -> dict:
        """Run `python3 -m ci.learning.cli ARGS` from the clean checkout of the DAG's main (the code
        that its CI runs). Its JSON output is returned as data."""
        base = self.ctl.base
        if not (base / "ci" / "learning" / "cli.py").is_file():
            raise LearningError("the DAG's main has no ci/learning/ (the learning extension is not "
                                "deployed there): run `sync`, or ask a maintainer")
        env = {**os.environ, "PYTHONPATH": str(base), "PYTHONDONTWRITEBYTECODE": "1"}
        p = subprocess.run([sys.executable, "-m", "ci.learning.cli", *args], cwd=cwd or base,
                           env=env, capture_output=True, text=True)
        try:
            out = json.loads(p.stdout) if p.stdout.strip() else {}
        except json.JSONDecodeError:
            out = {"stdout": p.stdout[-4000:]}
        if check and p.returncode != 0:
            raise LearningError(json.dumps({"exit": p.returncode, "output": out,
                                            "stderr": p.stderr[-4000:]}))
        return out if isinstance(out, dict) else {"result": out}

    def doctor(self) -> dict:
        out = {"dag_main_has_ci": (self.ctl.base / "ci" / "learning" / "cli.py").is_file(),
               "policy": (self.ctl.base / "meta" / "learning.json").is_file(),
               "notebooks": {r: NB.pin(self.ctl.base, r, self.ctl.path("scratch", "doctor",
                                                                        f"{r}.md"))["reason"]
                             or "loadable" for r in ROLES}}
        if out["dag_main_has_ci"]:
            out["dag_doctor"] = self.dag_ci("doctor", check=False)
        return out

    def notebook_show(self, role: str) -> dict:
        rec = NB.pin(self.ctl.base, role, self.ctl.path("scratch", "notebooks", f"{role}.md"))
        return {k: rec[k] for k in ("role", "path", "sha256", "bytes", "tokens_proxy", "reason",
                                    "text")}

    # -- publication ----------------------------------------------------------------------------
    def _publish(self, files: dict[str, bytes], branch: str, title: str, body: str,
                 ready: bool, adds_only: bool) -> dict:
        ctl = self.ctl
        ctl.refresh_base()
        for f in files:
            exists = (ctl.base / f).exists()
            if adds_only and exists:
                raise LearningError(f"{f} already exists on main (versions are immutable: add "
                                    "a new version)")
        remote, prefix = ctl.push_remote()
        g = ctl.ensure_clone(fetch=False)
        wt = ctl.path("worktrees", ctl.key, branch.replace("/", "-"))
        if not (wt / ".git").exists():
            exists = g("rev-parse", "--verify", "--quiet", f"refs/heads/{branch}", check=False)
            if exists.strip():
                g("worktree", "add", "--quiet", str(wt), branch)
            else:
                g("worktree", "add", "--quiet", "-b", branch, str(wt), "origin/main")
        w = Git(wt)
        changed = False
        for f, b in files.items():
            p = wt / f
            if not p.exists() or p.read_bytes() != b:
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_bytes(b)
                changed = True
        if changed:
            w("add", "--", *files)
            w("commit", "--quiet", "-m", title)
        w("push", "--quiet", remote, f"HEAD:refs/heads/{branch}")
        pr = ctl.gh.find_pr(prefix + branch) or ctl.gh.find_pr(branch)
        if pr is None:
            pr = ctl.gh.create_pr(prefix + branch, title, body, draft=not ready)
        elif ready and pr.get("isDraft"):
            ctl.gh.ready(pr["number"])
        return {"pr": pr["number"], "url": pr.get("url"), "branch": branch,
                "files": {f: "sha256:" + hashlib.sha256(b).hexdigest() for f, b in files.items()},
                "ready": ready}

    def generator_publish(self, src: Path, ready: bool = False) -> dict:
        base, files = generator_files(src)
        branch = "learning/" + base
        body = (f"Generator version `{base}` (learning extension).\n\nFiles:\n" +
                "\n".join(f"- `{f}`" for f in files) +
                "\n\nThe DAG's `learning` workflow certifies it when it is ready for review "
                "(universal Lean certificates of the family's exact predicates, and a sandboxed "
                "smoke run). It changes no notebook, policy, family or mathematical node.\n\n"
                "Published by `sigaba_research.py learning generator publish`.\n")
        return self._publish(files, branch, f"Generator {base}", body, ready, adds_only=True)

    def notebook_propose(self, role: str, src: Path, rationale: str = "",
                         ready: bool = False) -> dict:
        if role not in ROLES:
            raise LearningError("role: design | cryptanalysis")
        data = Path(src).read_bytes()
        try:
            data.decode("utf-8")
        except UnicodeDecodeError as e:
            raise LearningError("the notebook must be UTF-8") from e
        max_bytes, max_tokens = NB.limits(self.ctl.base)
        if len(data) > max_bytes or NB.proxy_tokens(data) > max_tokens:
            raise LearningError(f"over the cap ({max_bytes} bytes, {max_tokens} proxy tokens)")
        digest = hashlib.sha256(data).hexdigest()
        path = f"notebooks/{role}.md"
        cur = self.ctl.base / path
        incumbent = hashlib.sha256(cur.read_bytes()).hexdigest() if cur.is_file() else None
        if incumbent == digest:
            raise LearningError("the candidate is the active notebook")
        branch = f"learning/notebook/{role}/{digest[:12]}"
        body = (f"Notebook candidate for `{path}`.\n\n- candidate sha256 `{digest}` "
                f"({len(data)} bytes, ~{NB.proxy_tokens(data)} proxy tokens)\n- incumbent sha256 "
                f"`{incumbent or 'none'}`\n\n" +
                (f"Rationale (data, not evidence):\n\n> " + rationale.replace("\n", "\n> ") + "\n\n"
                 if rationale else "") +
                "Only the DAG's trusted evaluator decides: paired fresh-seed screen and independent "
                "confirmation against the incumbent. Nothing in this text is a result.\n\n"
                "Published by `sigaba_research.py learning notebook propose`.\n")
        return self._publish({path: data}, branch, f"Notebook candidate ({role}) {digest[:12]}",
                             body, ready, adds_only=False)
