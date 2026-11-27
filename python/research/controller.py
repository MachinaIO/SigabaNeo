"""The research controller (docs/RESEARCH_PROTOCOL.md): every mechanical step of the protocol.
Models only supply semantic content (goals, task scopes, plans, progress, proofs); this module
allocates IDs, validates records, manages worktrees, Git and GitHub, verifies, publishes, checkpoints,
schedules and keeps local state. It never calls a model."""

from __future__ import annotations

import json
import os
import re
import shutil
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable

import dag as D
import dag_tools as T

from . import records as R
from .remote import Git, GitHub, RemoteError, run
from .state import State

CORE = Path(__file__).resolve().parents[2]
PASS = ("OK", "ACCEPTED", "SKETCH_ACCEPTED")
LIVE_STATES = ("active", "paused", "blocked", "ready", "stale")
DEFAULTS = {"max_parallel_workers": 3, "checkpoint_seconds": 600, "episode_seconds": 1800,
            "falsification_seconds": 180, "max_run_seconds": 14400, "retry_backoff_seconds": 60,
            "max_proposals": 6, "max_worker_seconds": None, "grace_seconds": 600,
            "allowed_domains": ["design", "cryptanalysis"], "backend": "interactive",
            "worker_args": []}


class ProtocolError(Exception):
    """A malformed request or a protocol rule (exit 2)."""


class VerificationError(Exception):
    """Local verification failed (exit 5)."""


def now_iso(t: float) -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(t))


def default_verifier(base: Path, new: Path, records: Path | None, out: Path) -> dict:
    """`dag_verify.py verify` of this core (cooperative local layout, D6)."""
    args = [sys.executable, str(CORE / "python" / "dag_verify.py"), "verify", "--dag", str(base),
            "--new", str(new), "--out", str(out)]
    if records is not None and records.is_dir():
        args += ["--records", str(records)]
    run(args, check=False)
    p = out / "result.json"
    if not p.exists():
        raise VerificationError(f"the verifier wrote no result (see {out})")
    return json.loads(p.read_text())


@dataclass
class Controller:
    home: Path
    repo: str
    gh: object = None
    clock: Callable[[], float] = time.time
    verifier: Callable = default_verifier
    remote_url: Callable[[str], str] = lambda repo: f"https://github.com/{repo}.git"
    is_tty: Callable[[], bool] = lambda: sys.stdin.isatty() and sys.stdout.isatty()
    _state: State | None = field(default=None, repr=False)

    def __post_init__(self):
        self.home = Path(self.home).expanduser().resolve()
        if not re.fullmatch(r"[\w.-]+/[\w.-]+", self.repo):
            raise ProtocolError(f"not a repository owner/name: {self.repo}")
        if self.gh is None:
            self.gh = GitHub(self.repo)

    # -- layout ----------------------------------------------------------------------------------
    @property
    def key(self) -> str:
        return "github.com__" + self.repo.replace("/", "__")

    @property
    def st(self) -> State:
        if self._state is None:
            self._state = State(self.home / "state" / "research.sqlite")
        return self._state

    def path(self, *parts: str) -> Path:
        p = self.home.joinpath(*parts).resolve()
        if p != self.home and self.home not in p.parents:
            raise ProtocolError(f"{p} is outside {self.home}")
        return p

    @property
    def clone(self) -> Path:
        return self.path("repositories", self.key)

    @property
    def base(self) -> Path:
        return self.path("bases", self.key)

    @property
    def records(self) -> Path:
        return self.path("records", self.key)

    def task_dir(self, task_id: str) -> Path:
        d = self.path("state", "tasks", task_id)
        d.mkdir(parents=True, exist_ok=True)
        return d

    def config(self) -> dict:
        run_ = self.active_run()
        return {**DEFAULTS, **(json.loads(run_["config"]) if run_ else {})}

    # -- authorization ---------------------------------------------------------------------------
    def authorize(self, revoke: bool = False) -> dict:
        """Public writes to this repository, granted by the user at a terminal."""
        if not self.is_tty():
            raise ProtocolError("authorize needs an interactive terminal: the user runs it, not "
                                "an agent")
        if revoke:
            self.st.put(f"authorized:{self.repo}", False)
            return {"repo": self.repo, "public_writes": False}
        print(f"Allow sigaba_research to push branches, open and update pull requests and post "
              f"comments on {self.repo} as your GitHub account? Type 'yes': ", end="",
              file=sys.stderr, flush=True)
        if sys.stdin.readline().strip() != "yes":
            raise ProtocolError("not authorized")
        self.st.put(f"authorized:{self.repo}", True)
        return {"repo": self.repo, "public_writes": True}

    def require_writes(self) -> None:
        if not self.st.get(f"authorized:{self.repo}", False):
            raise ProtocolError(f"public writes to {self.repo} are not authorized; the user runs "
                                "`sigaba_research.py authorize` once")

    # -- repositories ----------------------------------------------------------------------------
    def ensure_clone(self, fetch: bool = True) -> Git:
        g = Git(self.clone)
        if not (self.clone / ".git").exists():
            self.clone.parent.mkdir(parents=True, exist_ok=True)
            run(["git", "clone", "--quiet", self.remote_url(self.repo), str(self.clone)])
            excl = self.clone / ".git" / "info" / "exclude"
            excl.parent.mkdir(parents=True, exist_ok=True)
            with excl.open("a") as f:
                f.write("/.claude/\n/.codex/\n/.lake/\n")
        elif fetch:
            g("fetch", "--quiet", "origin", "+refs/heads/main:refs/remotes/origin/main")
        if fetch:
            g("fetch", "--quiet", "origin", "+refs/heads/records:refs/remotes/origin/records",
              check=False)
        return g

    def refresh_base(self) -> str:
        """The clean base checkout at the DAG's latest `main` (and the records branch)."""
        g = self.ensure_clone()
        sha = g("rev-parse", "origin/main").strip()
        for path, ref in ((self.base, "origin/main"), (self.records, "origin/records")):
            if not g("rev-parse", "--verify", "--quiet", ref, check=False).strip():
                continue
            if not (path / ".git").exists():
                path.parent.mkdir(parents=True, exist_ok=True)
                g("worktree", "add", "--quiet", "--detach", str(path), ref)
            else:
                Git(path)("checkout", "--quiet", "--detach", ref)
        return sha

    def push_remote(self) -> tuple[str, str]:
        """(git remote, head owner prefix) for task branches: the DAG with write access, the
        user's fork otherwise."""
        cached = self.st.get(f"push:{self.repo}")
        if cached:
            return tuple(cached)
        g = self.ensure_clone(fetch=False)
        if self.gh.can_push():
            out = ("origin", "")
        else:
            fork = self.gh.ensure_fork()
            if "fork" not in g("remote").split():
                g("remote", "add", "fork", self.remote_url(fork))
            out = ("fork", fork.split("/")[0] + ":")
        self.st.put(f"push:{self.repo}", list(out))
        return out

    def _exists_on_main(self, path: str) -> bool:
        import subprocess
        return subprocess.run(["git", "-C", str(self.clone), "cat-file", "-e",
                               f"origin/main:{path}"], capture_output=True).returncode == 0

    def dag(self) -> D.Dag:
        if not (self.base / "dag").exists() and not (self.base / ".git").exists():
            self.refresh_base()
        return D.Dag(self.base)

    # -- goals -----------------------------------------------------------------------------------
    def goals(self) -> list[dict]:
        out = []
        for n in self.dag().by_kind("note"):
            if "research-goal" not in n.meta.get("tags", []):
                continue
            probs = R.goal_note_problems(n.path, n.text)
            goal = None if probs else R.one_block(D.front_matter(n.text)[1], "goal")
            out.append({"note": n.name, "fingerprint": R.goal_fingerprint(goal) if goal else None,
                        "title": n.meta.get("title"), "goal": goal, "problems": probs})
        return out

    def goal(self, fp: str) -> dict | None:
        return next((g for g in self.goals() if g["fingerprint"] and
                     g["fingerprint"].startswith(fp)), None)

    def goal_show(self, fp: str) -> dict:
        g = self.goal(fp)
        if g is None:
            raise ProtocolError(f"no goal {fp} on main")
        ix = self.index()
        entry = next((x for x in ix.get("goals", []) if x["fingerprint"] == g["fingerprint"]), {})
        tasks = [self.task_summary(t) for t in self.st.tasks("goal=?", g["fingerprint"])]
        remote = [v for v in self.remote_tasks() if v["descriptor"]["goal"] == g["fingerprint"]]
        return {**g, "targets": entry.get("targets", {}), "summaries": entry.get("summaries", []),
                "local_tasks": tasks, "task_prs": remote,
                "plans": [p for p in self.st.get("plans", []) if p["goal"] == g["fingerprint"]]}

    def index(self) -> dict:
        return T.index(self.dag(), D.read_records(self.records if self.records.is_dir()
                                                  else None))

    def goal_prepare(self, contract: dict, dir_: Path | None = None) -> dict:
        contract = {"schema": "sigaba.goal.v1", **contract}
        contract.setdefault("policy", {})
        contract.setdefault("definitions", [])
        contract.setdefault("targets", [])
        probs = R.validate("goal", contract)
        if probs:
            raise ProtocolError("; ".join(probs))
        d = Path(dir_).resolve() if dir_ else self.path("authoring", R.new_uuid())
        rel, text = R.goal_note(contract)
        p = d / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
        return {"dir": str(d), "goal_note": rel, "fingerprint": R.goal_fingerprint(contract),
                "digest": R.bundle_digest(d)}

    def bundle_files(self, d: Path) -> dict[str, bytes]:
        R.bundle_digest(d)   # refuses symbolic links
        base = d / "dag"
        return {str(p.relative_to(d)): p.read_bytes()
                for p in sorted(base.rglob("*")) if p.is_file()} if base.is_dir() else {}

    def local_precheck(self, files: dict[str, bytes], author: str | None = None) -> dict:
        """`dag_tools.py precheck` of files as if a PR added them to the current `main`."""
        tmp = self.path("state", "precheck", R.files_digest(files)[:16])
        if tmp.exists():
            shutil.rmtree(tmp)
        rows = []
        for f, b in files.items():
            (tmp / f).parent.mkdir(parents=True, exist_ok=True)
            (tmp / f).write_bytes(b)
            exists = self._exists_on_main(f)
            rows.append({"filename": f, "status": "modified" if exists else "added",
                         "type": "blob", "mode": "100644", "size": len(b)})
        dag = self.dag()
        trusted = dag.trusted()
        who = author or (trusted.get("accept") or ["local"])[0]
        return T.precheck(dag, rows, tmp, who, permission="write")

    def verify_files(self, files: dict[str, bytes], where: Path, deps: dict[str, bytes] | None
                     = None) -> dict:
        """Precheck and `dag_verify` of `files` (plus pinned `deps`) on the current `main`."""
        every = {**(deps or {}), **files}
        pre = self.local_precheck(every)
        new = where / "new"
        if new.exists():
            shutil.rmtree(new)
        for f, b in every.items():
            (new / f).parent.mkdir(parents=True, exist_ok=True)
            (new / f).write_bytes(b)
        statuses: dict[str, str] = {}
        result = None
        if pre["ok"]:
            out = where / "out"
            out.mkdir(parents=True, exist_ok=True)
            result = self.verifier(self.base, new, self.records if self.records.is_dir()
                                   else None, out)
            statuses = {i["path"]: i["status"] for i in result.get("items", [])}
        own = {p: s for p, s in statuses.items() if p in files}
        ok = pre["ok"] and all(s in PASS for s in own.values()) and \
            all(p in statuses for p in files if p.endswith((".lean", ".md")))
        return {"ok": ok, "precheck": pre["problems"], "statuses": own,
                "dependency_statuses": {p: s for p, s in statuses.items() if p not in files},
                "messages": {i["path"]: i.get("message", "")[:2000]
                             for i in (result or {}).get("items", [])
                             if i["path"] in files and i["status"] not in PASS}}

    def goal_review(self, d: Path) -> dict:
        d = Path(d).resolve()
        files = self.bundle_files(d)
        if not files:
            raise ProtocolError(f"{d}/dag has no files")
        self.refresh_base()
        res = self.verify_files(files, d / ".review")
        digest = R.bundle_digest(d)
        findings = (d / "review-findings.md").read_text() if (d / "review-findings.md").exists() \
            else "_No independent reviewer findings were saved (review-findings.md)._"
        lines = ["# Review packet", "", f"Bundle digest: `{digest}`", "",
                 "Approve with (in your own terminal):", "",
                 f"    python3 {CORE}/python/sigaba_research.py --repo {self.repo} goal approve "
                 f"--dir {d} --digest {digest}", "", "## Files", ""]
        lines += [f"- `{f}` ({len(b)} bytes, sha256 `{R.sha256(b)[:16]}`)" for f, b in
                  files.items()]
        lines += ["", "## Mechanical checks", ""]
        lines += [f"- precheck: {p}" for p in res["precheck"]] or ["- precheck: passed"]
        lines += [f"- `{p}`: {s}" for p, s in res["statuses"].items()]
        lines += [f"  - {m.splitlines()[0] if m else ''}" for m in res["messages"].values()]
        lines += ["", "## Independent review (advisory)", "", findings, ""]
        (d / "review.md").write_text("\n".join(lines))
        return {"dir": str(d), "digest": digest, "ok": res["ok"], "review": str(d / "review.md"),
                **res}

    def goal_approve(self, d: Path, digest: str) -> dict:
        if not self.is_tty():
            raise ProtocolError("approval needs an interactive terminal: the user runs `goal "
                                "approve`, not an agent")
        d = Path(d).resolve()
        actual = R.bundle_digest(d)
        if actual != digest:
            raise ProtocolError(f"the bundle changed: its digest is {actual}, not {digest}")
        print(f"Approve publishing exactly these files of {d} to {self.repo}? Type 'approve': ",
              end="", file=sys.stderr, flush=True)
        if sys.stdin.readline().strip() != "approve":
            raise ProtocolError("not approved")
        who = os.environ.get("USER", "user")
        self.st.x("INSERT OR REPLACE INTO approvals(digest,dir,time,who) VALUES(?,?,?,?)",
                  digest, str(d), self.clock(), who)
        return {"approved": digest, "dir": str(d)}

    def goal_register(self, d: Path) -> dict:
        """Publish exactly the approved bundle as an administrative PR (ready for review)."""
        self.require_writes()
        d = Path(d).resolve()
        digest = R.bundle_digest(d)
        if not self.st.one("SELECT 1 FROM approvals WHERE digest=? AND dir=?", digest, str(d)):
            raise ProtocolError(f"the bundle {digest} has not been approved (it may have changed "
                                "since its approval)")
        files = self.bundle_files(d)
        self.refresh_base()
        for f in files:
            if self._exists_on_main(f):
                raise ProtocolError(f"{f} already exists on main")
        branch = f"register/{digest[:12]}"
        remote, prefix = self.push_remote()
        g = self.ensure_clone(fetch=False)
        wt = self.path("worktrees", self.key, f"register-{digest[:12]}")
        if not (wt / ".git").exists():
            exists = g("rev-parse", "--verify", "--quiet", f"refs/heads/{branch}", check=False)
            if exists.strip():
                g("worktree", "add", "--quiet", str(wt), branch)
            else:
                g("worktree", "add", "--quiet", "-b", branch, str(wt), "origin/main")
        w = Git(wt)
        if not w("log", "--format=%H", "origin/main..HEAD").strip():
            for f, b in files.items():
                (wt / f).parent.mkdir(parents=True, exist_ok=True)
                (wt / f).write_bytes(b)
            w("add", "--", *files)
            w("commit", "--quiet", "-m", f"Register approved bundle {digest[:12]}")
        w("push", "--quiet", remote, f"HEAD:refs/heads/{branch}")
        pr = self.gh.find_pr(branch)
        if pr is None:
            goals = [R.one_block(D.front_matter(b.decode())[1], "goal") for f, b in files.items()
                     if R.GOAL_NOTE.fullmatch(Path(f).stem)]
            title = goals[0]["title"] if goals and goals[0] else f"bundle {digest[:12]}"
            body = (f"Administrative registration (no research task).\n\nApproved bundle digest "
                    f"`{digest}`.\n\nFiles:\n" + "\n".join(f"- `{f}`" for f in files) +
                    "\n\nPublished by `sigaba_research.py goal register` from exactly the approved "
                    "bytes.\n")
            pr = self.gh.create_pr(prefix + branch, f"Register: {title}", body, draft=False)
        return {"pr": pr["number"], "url": pr["url"], "digest": digest, "files": sorted(files)}

    # -- tasks -----------------------------------------------------------------------------------
    def task_body(self, desc: dict) -> str:
        lines = [R.task_marker(desc["task_id"]), "",
                 f"**Research task** `{desc['task_id']}` ({desc['domain']} / "
                 f"{desc['operation']}) for goal `{desc['goal'][:16]}`.", "",
                 f"Scope: {desc['scope']}", ""]
        if desc.get("deliverables"):
            lines += ["Deliverables:"] + [f"- {x}" for x in desc["deliverables"]] + [""]
        if desc.get("success"):
            lines += [f"Success: {desc['success']}", ""]
        if desc.get("depends_on"):
            lines += ["Depends on unmerged work (pinned):"] + [
                f"- #{x['pr']} at `{x['head'][:12]}`" for x in desc["depends_on"]] + [""]
        lines += ["This pull request is managed by `sigaba_research.py` (docs/RESEARCH_PROTOCOL.md "
                  "in the core). It stays a draft while the work is in progress; the gate checks it "
                  "once it is ready for review. The first comment shows the latest state; every "
                  "checkpoint is a new comment.", "", R.render_block("task", desc), ""]
        return "\n".join(lines)

    def task_create(self, desc: dict) -> dict:
        desc = {"schema": "sigaba.task.v1", **desc}
        desc.setdefault("task_id", R.new_uuid())
        probs = R.validate("task", desc)
        if probs:
            raise ProtocolError("; ".join(probs))
        tid = desc["task_id"]
        t = self.st.task(tid)
        if t is None:
            self.st.x("INSERT INTO tasks(task_id,repo,goal,domain,operation,descriptor,branch,state,"
                      "created) VALUES(?,?,?,?,?,?,?,?,?)", tid, self.repo, desc["goal"],
                      desc["domain"], desc["operation"], json.dumps(desc), f"research/{tid}",
                      "planned", self.clock())
            t = self.st.task(tid)
        elif t["descriptor"] != desc and t["pr"]:
            raise ProtocolError(f"task {tid} exists with another descriptor; a new scope is a new "
                                "task (successor_of)")
        return self.task_open(tid)

    def task_open(self, tid: str) -> dict:
        """Worktree, empty start commit, push, draft PR and status comment; idempotent."""
        self.require_writes()
        t = self.st.task(tid)
        desc, branch = t["descriptor"], t["branch"]
        g = self.ensure_clone()
        wt = self.path("worktrees", self.key, tid)
        if not (wt / ".git").exists():
            wt.parent.mkdir(parents=True, exist_ok=True)
            if g("rev-parse", "--verify", "--quiet", f"refs/heads/{branch}", check=False).strip():
                g("worktree", "add", "--quiet", str(wt), branch)
            else:
                g("worktree", "add", "--quiet", "-b", branch, str(wt), "origin/main")
        w = Git(wt)
        if not w("log", "--format=%H", "origin/main..HEAD").strip():
            w("commit", "--quiet", "--allow-empty", "-m", f"Start research task {tid}")
        remote, prefix = self.push_remote()
        self.st.update_task(tid, worktree=str(wt), push_remote=remote)
        w("push", "--quiet", remote, f"HEAD:refs/heads/{branch}")
        pr = self.gh.find_pr(branch)
        if pr is None:
            pr = self.gh.create_pr(prefix + branch, f"Research: {desc['title']}",
                                   self.task_body(desc), draft=True)
        self.st.update_task(tid, pr=pr["number"], pr_url=pr["url"])
        if t["state"] == "planned":
            self.st.update_task(tid, state="active", last_checkpoint=self.clock())
        self.ensure_status_comment(tid)
        self.path("scratch", tid).mkdir(parents=True, exist_ok=True)
        return self.task_summary(self.st.task(tid))

    def ensure_status_comment(self, tid: str) -> int:
        t = self.st.task(tid)
        if t["status_comment"]:
            return t["status_comment"]
        for c in self.gh.comments(t["pr"]):
            if R.STATUS_MARKER in c.get("body", ""):
                self.st.update_task(tid, status_comment=c["id"])
                return c["id"]
        c = self.gh.comment(t["pr"], self.status_body(t, None))
        self.st.update_task(tid, status_comment=c["id"])
        return c["id"]

    def task_summary(self, t: dict) -> dict:
        return {"task_id": t["task_id"], "title": t["descriptor"]["title"], "goal": t["goal"],
                "domain": t["domain"], "operation": t["operation"], "state": t["state"],
                "reason": t["reason"], "pr": t["pr"], "url": t["pr_url"], "worktree": t["worktree"],
                "branch": t["branch"], "outcome": t["outcome"],
                "last_checkpoint": now_iso(t["last_checkpoint"]) if t["last_checkpoint"] else None}

    def need(self, tid: str) -> dict:
        t = self.st.task(tid)
        if t is None:
            raise ProtocolError(f"no task {tid}")
        return t

    def task_files(self, t: dict) -> dict[str, bytes]:
        """The task's files on its branch: what it adds to `main` (committed)."""
        w = Git(Path(t["worktree"]))
        out = {}
        names = w("diff", "--name-status", "--no-renames", "origin/main...HEAD", "--", "dag")
        for line in names.splitlines():
            st_, path = line.split("\t", 1)
            if st_ == "A":
                out[path] = run_bytes(["git", "-C", t["worktree"], "cat-file", "blob",
                                       f"HEAD:{path}"])
        return out

    def working_files(self, t: dict) -> dict[str, bytes]:
        """New files under `dag/` in the worktree that are not on the branch yet."""
        w = Git(Path(t["worktree"]))
        out = {}
        for line in w("status", "--porcelain", "-uall", "--", "dag").splitlines():
            code, path = line[:2], line[3:]
            p = Path(t["worktree"]) / path
            if code in ("??", "A ") and p.is_file() and not p.is_symlink():
                out[path] = p.read_bytes()
        return out

    def deps(self, t: dict) -> dict[str, bytes]:
        d = self.task_dir(t["task_id"]) / "deps"
        out = {}
        for x in t["descriptor"].get("depends_on", []):
            root = d / str(x["pr"]) / x["head"]
            for p in sorted(root.rglob("*")) if root.is_dir() else []:
                if p.is_file():
                    out[str(p.relative_to(root))] = p.read_bytes()
        return out

    def task_verify(self, tid: str, with_deps: bool = False, include_working: bool = True) -> dict:
        t = self.need(tid)
        self.refresh_base()
        files = self.task_files(t)
        if include_working:
            files.update(self.working_files(t))
        if not files:
            return {"ok": True, "statuses": {}, "precheck": [], "note": "no files yet"}
        res = self.verify_files(files, self.task_dir(t["task_id"]) / "verify",
                                self.deps(t) if with_deps else None)
        self.st.x("INSERT INTO verifications(task_id,time,digest,ok,statuses) VALUES(?,?,?,?,?)",
                  t["task_id"], self.clock(), R.files_digest(files), int(res["ok"]),
                  json.dumps(res["statuses"]))
        return {**res, "with_deps": with_deps}

    def artifact_propose(self, tid: str, paths: list[str]) -> dict:
        t = self.need(tid)
        wt = Path(t["worktree"]).resolve()
        chosen = []
        for p in paths:
            rel = os.path.normpath(p)
            full = (wt / rel)
            if rel.startswith("..") or os.path.isabs(rel) or not rel.startswith("dag/"):
                raise ProtocolError(f"{p}: only paths under dag/ of the task's worktree")
            if full.is_symlink() or not full.is_file():
                raise ProtocolError(f"{p}: not a regular file")
            if wt not in full.resolve().parents:
                raise ProtocolError(f"{p}: outside the worktree")
            if D.classify(rel) is None:
                raise ProtocolError(f"{p}: not a path of the DAG's layout")
            if self._exists_on_main(rel):
                raise ProtocolError(f"{p}: exists on main; nodes are never changed")
            chosen.append(rel)
            if rel.endswith(".lean"):
                js = rel.removesuffix(".lean") + ".json"
                if (wt / js).is_file() and js not in chosen and js not in paths:
                    chosen.append(js)
        self.st.x("INSERT INTO artifacts(task_id,time,paths,state) VALUES(?,?,?,?)",
                  t["task_id"], self.clock(), json.dumps(sorted(set(chosen))), "proposed")
        return {"task": t["task_id"], "proposed": sorted(set(chosen))}

    def publish(self, tid: str) -> dict:
        """Commit and push exactly the verified bytes of the latest proposed artifacts."""
        t = self.need(tid)
        a = self.st.one("SELECT * FROM artifacts WHERE task_id=? AND state='proposed' ORDER BY id "
                        "DESC LIMIT 1", t["task_id"])
        if a is None:
            return {"pushed": []}
        wt = Path(t["worktree"])
        paths = json.loads(a["paths"])
        snap = {}
        for p in paths:
            f = wt / p
            if f.is_symlink() or not f.is_file():
                self.st.x("UPDATE artifacts SET state='failed', result=? WHERE id=?",
                          json.dumps({"error": f"{p} is missing"}), a["id"])
                return {"pushed": [], "error": f"{p} is missing"}
            snap[p] = f.read_bytes()
        digest = R.files_digest(snap)
        stage = self.task_dir(t["task_id"]) / "stage" / digest[:16]
        for p, b in snap.items():
            (stage / "files" / p).parent.mkdir(parents=True, exist_ok=True)
            (stage / "files" / p).write_bytes(b)
        self.refresh_base()
        committed = self.task_files(t)
        with_deps = bool(t["descriptor"].get("depends_on"))
        res = self.verify_files({**committed, **snap}, stage,
                                self.deps(t) if with_deps else None)
        own = {p: s for p, s in res["statuses"].items() if p in snap}
        if not res["ok"]:
            self.st.x("UPDATE artifacts SET state='failed', digest=?, result=? WHERE id=?", digest,
                      json.dumps(res), a["id"])
            return {"pushed": [], "verification": res}
        self.commit_exact(t, stage / "files", snap, f"Add {len(snap)} file(s) "
                          f"({', '.join(sorted({s for s in own.values()}))})")
        self.require_writes()
        Git(wt)("push", "--quiet", t["push_remote"], f"HEAD:refs/heads/{t['branch']}")
        self.st.x("UPDATE artifacts SET state='pushed', digest=?, result=? WHERE id=?", digest,
                  json.dumps(res), a["id"])
        return {"pushed": sorted(snap), "statuses": own, "digest": digest}

    def commit_exact(self, t: dict, staged: Path, snap: dict[str, bytes], msg: str) -> str:
        """A commit on the task's branch that adds exactly `snap` (from the staged copy), whatever
        the worktree holds now. The worktree's files are not touched."""
        wt = Path(t["worktree"])
        w = Git(wt)
        idx = self.task_dir(t["task_id"]) / "index.tmp"
        if idx.exists():
            idx.unlink()
        env = {**os.environ, "GIT_INDEX_FILE": str(idx)}
        w("read-tree", "HEAD", env=env)
        for p in sorted(snap):
            blob = w("hash-object", "-w", "--no-filters", str(staged / p)).strip()
            w("update-index", "--add", "--cacheinfo", f"100644,{blob},{p}", env=env)
        tree = w("write-tree", env=env).strip()
        old = w.head()
        commit = w("commit-tree", tree, "-p", old, "-m", msg).strip()
        w("update-ref", f"refs/heads/{t['branch']}", commit, old)
        w("reset", "--quiet")          # the index follows HEAD; the working files stay
        idx.unlink()
        return commit

    # -- checkpoints -----------------------------------------------------------------------------
    def progress_record(self, tid: str, record: dict) -> dict:
        t = self.need(tid)
        probs = R.validate("progress", record)
        if probs:
            raise ProtocolError("; ".join(probs))
        self.st.x("INSERT INTO progress(task_id,time,record) VALUES(?,?,?)", t["task_id"],
                  self.clock(), json.dumps(record))
        self.st.update_task(t["task_id"], last_activity=self.clock())
        if record.get("artifacts"):
            self.artifact_propose(t["task_id"], record["artifacts"])
        return {"recorded": True, "task": t["task_id"]}

    def checkpoint(self, tid: str, kind: str = "progress", outcome: str | None = None) -> dict:
        t = self.need(tid)
        if not t["pr"]:
            raise ProtocolError(f"task {tid} has no PR yet")
        now = self.clock()
        pushed = []
        try:
            pushed = self.publish(t["task_id"]).get("pushed", [])
        except (RemoteError, VerificationError) as e:
            self.st.event(now, "publish_failed", t["task_id"], None, {"error": str(e)})
        t = self.st.task(t["task_id"])
        prog = self.st.latest_progress(t["task_id"])
        used = self.st.get(f"cp_progress:{t['task_id']}", 0)
        fresh = prog is not None and prog["id"] > used
        rec = prog["record"] if prog else {}
        if kind == "progress" and not fresh:
            kind = "heartbeat"
        ver = self.st.one("SELECT * FROM verifications WHERE task_id=? ORDER BY id DESC LIMIT 1",
                          t["task_id"])
        ep = self.st.one("SELECT * FROM episodes WHERE task_id=? ORDER BY started DESC LIMIT 1",
                         t["task_id"])
        seq = t["seq"] + 1
        run_ = self.active_run()
        cp = {"schema": "sigaba.checkpoint.v1", "task_id": t["task_id"],
              "run_id": run_["run_id"] if run_ else None,
              "episode_id": ep["episode_id"] if ep else None, "sequence": seq,
              "time": now_iso(now), "kind": kind, "state": t["state"],
              "report_time": now_iso(prog["time"]) if prog else None,
              "stale_report": not fresh,
              **{k: rec[k] for k in ("summary", "established", "attempted", "blockers",
                                      "next_steps", "falsification") if k in rec},
              "head": Git(Path(t["worktree"])).head() if t["worktree"] else None,
              "verification": json.loads(ver["statuses"]) if ver else {},
              "pushed": pushed, "dependencies": t["descriptor"].get("depends_on", []),
              "outcome": outcome or t["outcome"],
              "usage": {"wall_seconds": int(self.task_usage(t["task_id"]))}}
        probs = R.validate("checkpoint", cp)
        if probs:
            raise ProtocolError("; ".join(probs))
        marker = R.checkpoint_marker(t["task_id"], cp["run_id"], seq)
        self.outbox_add(marker, t["task_id"], "comment",
                        {"pr": t["pr"], "body": self.checkpoint_body(marker, cp, t)})
        sc = self.ensure_status_comment_safe(t)
        self.st.x("DELETE FROM outbox WHERE task_id=? AND kind='status' AND done=0", t["task_id"])
        self.outbox_add(f"status:{t['task_id']}:{seq}", t["task_id"], "status",
                        {"comment": sc, "pr": t["pr"], "body": self.status_body(t, cp)})
        self.st.update_task(t["task_id"], seq=seq, last_checkpoint=now, checkpoint_due=0)
        if prog:
            self.st.put(f"cp_progress:{t['task_id']}", prog["id"])
        sent = self.flush_outbox()
        return {"task": t["task_id"], "sequence": seq, "kind": kind, "pushed": pushed,
                "stale_report": not fresh, "outbox": sent}

    def ensure_status_comment_safe(self, t: dict) -> int | None:
        try:
            return self.ensure_status_comment(t["task_id"])
        except RemoteError:
            return None

    def task_usage(self, tid: str) -> float:
        now = self.clock()
        return sum(((e["ended"] or now) - e["started"]) for e in
                   self.st.all("SELECT * FROM episodes WHERE task_id=?", tid))

    def checkpoint_body(self, marker: str, cp: dict, t: dict) -> str:
        head = {"progress": "Checkpoint", "heartbeat": "Heartbeat", "final": "Final checkpoint"}
        lines = [marker, f"**{head[cp['kind']]} {cp['sequence']}** ({cp['time']}, state "
                 f"`{cp['state']}`)", ""]
        if cp["stale_report"]:
            lines += [f"No fresh research report since the previous checkpoint (latest report: "
                      f"{cp['report_time'] or 'none'}). Nothing new is claimed.", ""]
        if cp.get("summary"):
            lines += [cp["summary"], ""]
        for k, title in (("established", "Established"), ("attempted", "Attempted"),
                         ("blockers", "Blockers"), ("next_steps", "Next steps")):
            if cp.get(k):
                lines.append(f"{title}:")
                lines += [f"- {x['claim']} ({x.get('evidence', 'informal')})" if isinstance(x, dict)
                          else f"- {x}" for x in cp[k]]
                lines.append("")
        if cp["pushed"]:
            lines += ["Pushed (verified locally): " + ", ".join(f"`{p}`" for p in cp["pushed"]), ""]
        lines += ["<details><summary>record</summary>", "", R.render_block("checkpoint", cp), "",
                  "</details>"]
        return "\n".join(lines)

    def status_body(self, t: dict, cp: dict | None) -> str:
        lines = [R.STATUS_MARKER, "## Latest state", ""]
        if cp is None:
            lines += [f"State `{t['state']}`. Task opened; no checkpoint yet."]
            return "\n".join(lines) + "\n"
        lines.append(f"State `{cp['state']}`, checkpoint {cp['sequence']} at {cp['time']}"
                     + (f", outcome `{cp['outcome']}`" if cp.get("outcome") else "") + ".")
        if cp.get("summary"):
            lines += ["", cp["summary"]]
        if cp["stale_report"]:
            lines += ["", "No fresh research report in the last period."]
        for k, title in (("established", "Established"), ("blockers", "Blockers"),
                         ("next_steps", "Next")):
            if cp.get(k):
                items = [x["claim"] if isinstance(x, dict) else x for x in cp[k]][:5]
                lines += ["", f"{title}: " + "; ".join(items)]
        if cp.get("dependencies"):
            lines += ["", "Depends on: " + ", ".join(f"#{d['pr']}@{d['head'][:8]}"
                                                     for d in cp["dependencies"])]
        if cp.get("verification"):
            lines += ["", "Local verification: " + ", ".join(
                f"`{Path(p).name}` {s}" for p, s in list(cp["verification"].items())[:12])]
        return "\n".join(lines) + "\n"

    def outbox_add(self, key: str, tid: str, kind: str, payload: dict) -> None:
        self.st.x("INSERT OR IGNORE INTO outbox(key,task_id,kind,payload) VALUES(?,?,?,?)", key,
                  tid, kind, json.dumps(payload))

    def flush_outbox(self) -> dict:
        now = self.clock()
        sent, failed = 0, 0
        backoff = self.config()["retry_backoff_seconds"]
        cache: dict[int, list[dict]] = {}
        for o in self.st.all("SELECT * FROM outbox WHERE done=0 AND next_try<=? ORDER BY id", now):
            p = json.loads(o["payload"])
            try:
                self.require_writes()
                if o["kind"] == "comment":
                    if p["pr"] not in cache:
                        cache[p["pr"]] = self.gh.comments(p["pr"])
                    if not any(o["key"] in c.get("body", "") for c in cache[p["pr"]]):
                        self.gh.comment(p["pr"], p["body"])
                elif o["kind"] == "status":
                    cid = p.get("comment") or self.ensure_status_comment(o["task_id"])
                    self.gh.edit_comment(cid, p["body"])
                self.st.x("UPDATE outbox SET done=1 WHERE id=?", o["id"])
                sent += 1
            except (RemoteError, ProtocolError) as e:
                failed += 1
                n = o["attempts"] + 1
                self.st.x("UPDATE outbox SET attempts=?, next_try=?, error=? WHERE id=?", n,
                          now + min(backoff * 2 ** (n - 1), 3600), str(e)[:2000], o["id"])
        return {"sent": sent, "failed": failed,
                "pending": self.st.one("SELECT COUNT(*) AS n FROM outbox WHERE done=0")["n"]}

    def checkpoint_due(self) -> list[dict]:
        cfg = self.config()
        now = self.clock()
        out = []
        for t in self.st.tasks("state IN ('active','paused','blocked','stale') AND pr IS NOT NULL"):
            last = t["last_checkpoint"] or 0
            if t["checkpoint_due"] or now - last >= cfg["checkpoint_seconds"]:
                try:
                    out.append(self.checkpoint(t["task_id"]))
                except (RemoteError, ProtocolError) as e:
                    out.append({"task": t["task_id"], "error": str(e)})
        self.flush_outbox()
        return out

    # -- state changes ---------------------------------------------------------------------------
    def set_state(self, tid: str, state: str, reason: str | None = None,
                  kind: str = "progress", outcome: str | None = None) -> dict:
        t = self.need(tid)
        self.st.update_task(t["task_id"], state=state, reason=reason,
                            **({"outcome": outcome} if outcome else {}))
        return self.checkpoint(t["task_id"], kind, outcome)

    def task_pause(self, tid: str, reason: str = "paused by the user") -> dict:
        self.end_live_episodes(tid, "paused")
        return self.set_state(tid, "paused", reason)

    def task_resume(self, tid: str) -> dict:
        t = self.need(tid)
        out = self.set_state(t["task_id"], "active")
        self.enqueue_task(t)
        return out

    def task_block(self, tid: str, reason: str) -> dict:
        return self.set_state(tid, "blocked", reason)

    def task_ready(self, tid: str) -> dict:
        """D2: the AI decides; the controller refuses only when the exact files fail."""
        t = self.need(tid)
        if self.st.one("SELECT 1 FROM artifacts WHERE task_id=? AND state='proposed'",
                       t["task_id"]):
            pub = self.publish(t["task_id"])
            if pub.get("verification") and not pub["verification"]["ok"]:
                raise VerificationError(json.dumps({"refused": "the proposed files fail local "
                                                    "verification", **pub["verification"]}))
        self.refresh_base()
        files = self.task_files(t)
        if not files:
            raise ProtocolError("the task's branch adds no file yet")
        res = self.verify_files(files, self.task_dir(t["task_id"]) / "ready")
        if not res["ok"]:
            raise VerificationError(json.dumps({"refused": "local verification failed on the "
                                                "current main (imports must exist on main)",
                                                **res}))
        self.require_writes()
        self.gh.ready(t["pr"])
        out = self.set_state(t["task_id"], "ready")
        return {**out, "statuses": res["statuses"]}

    def task_draft(self, tid: str, reason: str = "back to work") -> dict:
        t = self.need(tid)
        self.require_writes()
        self.gh.to_draft(t["pr"])
        return self.set_state(t["task_id"], "active", reason)

    def task_finalize(self, tid: str, outcome: str, body: str, close: bool = False) -> dict:
        if outcome not in R.OUTCOMES:
            raise ProtocolError(f"outcome must be one of {R.OUTCOMES}")
        t = self.need(tid)
        self.end_live_episodes(t["task_id"], "finalized")
        self.publish(t["task_id"])          # pending artifacts first: the summary refers to them
        self.refresh_base()
        desc = t["descriptor"]
        refs = set()
        goal_note = f"goal-{desc['goal']}"
        if self._exists_on_main(f"dag/Notes/{goal_note}.md"):
            refs.add(f"note:{goal_note}")
        for p, b in self.task_files(t).items():
            if p.endswith(".json") and "/Notes/" not in p:
                kind = D.classify(p)[0]
                name = json.loads(b).get("name") if kind in ("theorem",) else None
                if kind == "definition":
                    refs.add(f"definition:{D.classify(p)[1].group(1)}")
                elif name:
                    refs.add(f"theorem:{name}")
        slug = f"task-{t['task_id'][:8]}-{R.slugify(desc['title'], 50)}"
        rel = f"dag/Notes/{slug}.md"
        summary = {"schema": "sigaba.summary.v1", "task_id": t["task_id"], "goal": desc["goal"],
                   "outcome": outcome, "pr": t["pr"]}
        text = "\n".join(["---", f"title: {R.goal_title_line('Task summary: ' + desc['title'])}",
                          "tags: [research-summary]", f"refs: [{', '.join(sorted(refs))}]", "---",
                          "", f"# Task summary: {desc['title']}", "",
                          f"Task `{t['task_id']}` ({desc['domain']} / {desc['operation']}), goal "
                          f"`{desc['goal']}`, outcome `{outcome}`. Mathematical status comes "
                          "from the records, not from this note.", "", body.strip(), "",
                          R.render_block("summary", summary), ""])
        probs = R.summary_note_problems(text)
        if probs:
            raise ProtocolError("; ".join(probs))
        wt = Path(t["worktree"])
        (wt / rel).parent.mkdir(parents=True, exist_ok=True)
        if not (wt / rel).exists() and not self._exists_on_main(rel):
            (wt / rel).write_text(text)
            self.artifact_propose(t["task_id"], [rel])
        pub = self.publish(t["task_id"])
        self.st.update_task(t["task_id"], outcome=outcome)
        if close:
            self.require_writes()
            out = self.set_state(t["task_id"], "closed", "finalized without merge", "final",
                                 outcome)
            self.gh.close(t["pr"], f"Closed by the research controller: outcome `{outcome}`. "
                          "The checkpoints above record what was attempted.")
            self.drop_queue(t["task_id"])
            return {**out, "published": pub}
        self.drop_queue(t["task_id"])
        try:
            ready = self.task_ready(t["task_id"])
        except VerificationError as e:
            self.set_state(t["task_id"], "blocked", "finalized but local verification failed",
                           "final", outcome)
            raise e
        self.checkpoint(t["task_id"], "final", outcome)
        return {**ready, "published": pub}

    # -- plans and candidates --------------------------------------------------------------------
    def plan_add(self, tid: str, plan: dict) -> dict:
        t = self.need(tid)
        plan = {"schema": "sigaba.plan.v1", **plan}
        plan.setdefault("plan_id", R.new_uuid())
        plan.setdefault("goal", t["goal"])
        probs = R.validate("plan", plan)
        if probs:
            raise ProtocolError("; ".join(probs))
        if len(set(plan["required"])) != len(plan["required"]):
            raise ProtocolError("required members must be distinct")
        plans = self.st.get("plans", []) + self.st.get("local_plans", [])
        graph = build_graph(plans + [plan])
        if plan["plan_id"] in graph["dropped"]:
            raise ProtocolError("this plan would close a cycle in the research graph")
        self.st.put("local_plans", self.st.get("local_plans", []) + [plan])
        body = (f"<!-- sigaba-plan {plan['plan_id']} -->\n**Plan** for {plan['target']['kind']} "
                f"`{plan['target']['id'][:16]}`: {len(plan['required'])} required task(s).\n\n"
                f"{plan['rationale']}\n\n{R.render_block('plan', plan)}\n")
        self.outbox_add(f"<!-- sigaba-plan {plan['plan_id']} -->", t["task_id"], "comment",
                        {"pr": t["pr"], "body": body})
        self.flush_outbox()
        return {"plan_id": plan["plan_id"], "posted_on": t["pr"]}

    def candidate_add(self, tid: str, cand: dict) -> dict:
        t = self.need(tid)
        cand = {"schema": "sigaba.candidate.v1", **cand}
        cand.setdefault("candidate_id", R.new_uuid())
        cand.setdefault("goal", t["goal"])
        cand.setdefault("task", t["task_id"])
        probs = R.validate("candidate", cand)
        if probs:
            raise ProtocolError("; ".join(probs))
        body = (f"<!-- sigaba-candidate {cand['candidate_id']} -->\n**Candidate** "
                f"({cand['kind']}): {cand['description'][:300]}\n\n"
                f"{R.render_block('candidate', cand)}\n")
        self.outbox_add(f"<!-- sigaba-candidate {cand['candidate_id']} -->", t["task_id"],
                        "comment", {"pr": t["pr"], "body": body})
        self.flush_outbox()
        return {"candidate_id": cand["candidate_id"], "posted_on": t["pr"]}

    # -- other PRs -------------------------------------------------------------------------------
    def pr_fetch(self, tid: str, pr: int) -> dict:
        """The source files under dag/ that PR `pr` adds, pinned at its current head, into the
        task's dependency store; the task records the dependency in its checkpoints."""
        t = self.need(tid)
        head = self.gh.view_pr(pr)["headRefOid"]
        root = self.task_dir(t["task_id"]) / "deps" / str(pr) / head
        got = []
        for f in self.gh.pr_files(pr):
            path = f["filename"]
            if f.get("status") != "added" or D.classify(path) is None:
                continue
            data = self.gh.blob(f["sha"])
            if git_blob_sha(data) != f["sha"]:
                raise ProtocolError(f"#{pr} {path}: content does not match its blob")
            (root / path).parent.mkdir(parents=True, exist_ok=True)
            (root / path).write_bytes(data)
            got.append(path)
        dep = {"pr": pr, "head": head, "paths": sorted(got)}
        local = self.st.get(f"deps:{t['task_id']}", [])
        local = [d for d in local if d["pr"] != pr] + [dep]
        self.st.put(f"deps:{t['task_id']}", local)
        return {"task": t["task_id"], **dep, "dir": str(root)}

    # -- sync and the research graph -------------------------------------------------------------
    def remote_tasks(self) -> list[dict]:
        return self.st.get("remote_tasks", [])

    def sync(self) -> dict:
        self.refresh_base()
        prs = self.gh.list_prs()
        tasks, plans, cands, problems = [], [], [], []
        for pr in prs:
            desc = R.one_block(pr.get("body") or "", "task")
            if desc is None:
                continue
            entry = {"pr": pr["number"], "state": pr["state"], "draft": pr["isDraft"],
                     "author": (pr.get("author") or {}).get("login"), "head": pr["headRefOid"],
                     "descriptor": desc, "url": pr["url"], "latest_checkpoint": None}
            if pr["state"] == "OPEN" or pr.get("mergedAt"):
                for c in self.gh.comments(pr["number"]):
                    body = c.get("body", "")
                    for kind, sink in (("plan", plans), ("candidate", cands)):
                        for obj, err in R.find_blocks(body, kind):
                            if err or R.validate(kind, obj):
                                problems.append(f"#{pr['number']}: malformed {kind}")
                            else:
                                sink.append({**obj, "_pr": pr["number"]})
                    cp = R.one_block(body, "checkpoint")
                    if cp:
                        entry["latest_checkpoint"] = {k: cp.get(k) for k in (
                            "sequence", "time", "kind", "state", "summary", "blockers",
                            "next_steps", "stale_report")}
            tasks.append(entry)
            local = self.st.task(desc["task_id"])
            if local and local["pr"] == pr["number"]:
                state = ("merged" if pr.get("mergedAt") else "closed" if pr["state"] != "OPEN"
                         else None)
                if state and local["state"] != state:
                    self.st.update_task(local["task_id"], state=state)
                    self.drop_queue(local["task_id"])
                elif not state and not pr["isDraft"] and local["state"] == "active":
                    self.st.update_task(local["task_id"], state="ready")
        graph = build_graph(plans + self.st.get("local_plans", []), {t["descriptor"]["task_id"]
                                                                       for t in tasks})
        self.st.put("remote_tasks", tasks)
        self.st.put("plans", plans)
        self.st.put("candidates", cands)
        self.st.put("graph", graph)
        self.st.put("synced", self.clock())
        derived = []
        for g in self.goals():
            if g["fingerprint"] and self.active_run():
                derived += self.work_derive(g["fingerprint"])["enqueued"]
        return {"tasks": len(tasks), "plans": len(plans), "candidates": len(cands),
                "graph_problems": graph["problems"], "problems": problems, "derived": derived}

    # -- queues ----------------------------------------------------------------------------------
    def enqueue(self, proposal: dict, key: str | None = None, task_id: str | None = None) -> bool:
        pair = f"{proposal['domain']}/{proposal['operation']}"
        key = key or R.sha256(R.canonical({k: proposal.get(k) for k in (
            "goal", "domain", "operation", "targets", "scope")}))
        if self.st.one("SELECT 1 FROM queue WHERE key=?", key):
            return False
        self.st.x("INSERT INTO queue(key,pair,goal,task_id,proposal,state) VALUES(?,?,?,?,?,?)",
                  key, pair, proposal["goal"], task_id, json.dumps(proposal), "queued")
        return True

    def enqueue_task(self, t: dict) -> None:
        """Put a task at the tail of its queue (removing any earlier entry)."""
        row = self.st.one("SELECT * FROM queue WHERE task_id=?", t["task_id"])
        key = row["key"] if row else f"task:{t['task_id']}"
        self.st.x("DELETE FROM queue WHERE task_id=?", t["task_id"])
        d = t["descriptor"]
        self.st.x("INSERT INTO queue(key,pair,goal,task_id,proposal,state) VALUES(?,?,?,?,?,?)",
                  key, f"{d['domain']}/{d['operation']}", d["goal"], t["task_id"],
                  json.dumps({k: v for k, v in d.items() if k not in ("schema", "task_id")}),
                  "queued")

    def drop_queue(self, tid: str) -> None:
        self.st.x("UPDATE queue SET state='done' WHERE task_id=?", tid)

    def work_propose(self, items: list[dict]) -> dict:
        cfg = self.config()
        accepted, rejected = [], []
        for i, it in enumerate(items):
            if len(accepted) >= cfg["max_proposals"]:
                rejected.append({"item": i, "reason": "over the per-call cap"})
                continue
            probe = {"schema": "sigaba.task.v1", "task_id": R.new_uuid(), **it}
            probs = R.validate("task", probe)
            if probs:
                rejected.append({"item": i, "reason": "; ".join(probs)})
                continue
            if it["domain"] not in cfg["allowed_domains"]:
                rejected.append({"item": i, "reason": "domain not allowed in this run"})
                continue
            if self.enqueue(it):
                accepted.append(it["title"])
            else:
                rejected.append({"item": i, "reason": "duplicate"})
        return {"enqueued": accepted, "rejected": rejected}

    def work_derive(self, goal_fp: str) -> dict:
        """One deepen item per open leaf of the goal's targets (deduplicated; leaves already
        targeted by an open task PR or local task are skipped)."""
        g = self.goal(goal_fp)
        if g is None or g["goal"] is None:
            return {"enqueued": []}
        ix = self.index()
        entry = next((x for x in ix.get("goals", []) if x["fingerprint"] == g["fingerprint"]),
                     None)
        if entry is None:
            return {"enqueued": []}
        env = self.dag().environment()
        eid = env["id"] if env else None
        busy = set()
        for t in self.remote_tasks():
            if t["state"] == "OPEN":
                busy |= set(t["descriptor"].get("targets", []))
        for t in self.st.tasks("state IN ('planned','active','paused','blocked','ready')"):
            busy |= set(t["descriptor"].get("targets", []))
        domain = "cryptanalysis" if g["goal"]["kind"] == "assumption" else "design"
        out = []
        for ref, per_env in entry["targets"].items():
            for leaf in (per_env.get(eid) or {}).get("open_leaves", []):
                tref = f"theorem:{leaf}"
                if tref in busy:
                    continue
                prop = {"goal": g["fingerprint"], "domain": domain, "operation": "deepen",
                        "title": f"Close the open leaf {leaf}"[:200],
                        "scope": f"Prove or refute {leaf}, an open leaf of {ref}, or reduce it by "
                                 "a sketch to smaller statements.",
                        "deliverables": ["a proof, a disproof or a sketch of the leaf"],
                        "success": f"{leaf} is Proved or Disproved, or has an accepted sketch",
                        "targets": [tref]}
                key = R.sha256(R.canonical([g["fingerprint"], domain, "deepen", tref]))
                if self.enqueue(prop, key=key):
                    out.append(leaf)
        return {"enqueued": out}

    def work_list(self) -> list[dict]:
        return [{**r, "proposal": json.loads(r["proposal"])} for r in
                self.st.all("SELECT * FROM queue WHERE state='queued' ORDER BY seq")]

    def live_episode(self, tid: str) -> dict | None:
        return self.st.one("SELECT * FROM episodes WHERE task_id=? AND ended IS NULL", tid)

    def next_item(self, allowed: list[str]) -> dict | None:
        """round_robin_v1: one FIFO per (domain, operation), lexicographic order, one cursor;
        empty queues and queues whose head is not eligible are skipped."""
        pairs = [f"{d}/{o}" for d, o in R.PAIRS]
        cursor = self.st.get("cursor", 0)
        for i in range(len(pairs)):
            k = (cursor + i) % len(pairs)
            pair = pairs[k]
            if pair.split("/")[0] not in allowed:
                continue
            head = self.st.one("SELECT * FROM queue WHERE pair=? AND state='queued' ORDER BY seq, "
                               "task_id LIMIT 1", pair)
            if head is None:
                continue
            if head["task_id"]:
                t = self.st.task(head["task_id"])
                if t is None or t["state"] not in ("planned", "active") or \
                        self.live_episode(head["task_id"]):
                    self.st.event(self.clock(), "skip", head["task_id"], None,
                                  {"pair": pair, "reason": "head not eligible"})
                    continue
            self.st.put("cursor", (k + 1) % len(pairs))
            self.st.x("UPDATE queue SET state='dispatched' WHERE seq=?", head["seq"])
            return head
        return None

    # -- runs and episodes -----------------------------------------------------------------------
    def active_run(self) -> dict | None:
        return self.st.one("SELECT * FROM runs WHERE state='running' ORDER BY started DESC "
                           "LIMIT 1")

    def run_start(self, cfg: dict) -> dict:
        if self.active_run():
            raise ProtocolError("a run is already active (run stop first)")
        cfg = {**DEFAULTS, **{k: v for k, v in cfg.items() if v is not None}}
        bad = [d for d in cfg["allowed_domains"] if d not in ("design", "cryptanalysis")]
        if bad or cfg["backend"] not in ("interactive", "claude", "codex"):
            raise ProtocolError("bad run configuration")
        rid = R.new_uuid()
        now = self.clock()
        self.st.x("INSERT INTO runs(run_id,config,started,deadline,state) VALUES(?,?,?,?,?)", rid,
                  json.dumps(cfg), now, now + cfg["max_run_seconds"], "running")
        d = self.path("state", "runs", rid)
        d.mkdir(parents=True, exist_ok=True)
        (d / "config.json").write_text(json.dumps(cfg, indent=1))
        return {"run_id": rid, "config": cfg, "deadline": now_iso(now + cfg["max_run_seconds"])}

    def run_status(self) -> dict:
        r = self.active_run()
        eps = self.st.all("SELECT episode_id,task_id,backend,started,deadline FROM episodes "
                          "WHERE ended IS NULL")
        return {"run": ({**r, "config": json.loads(r["config"])} if r else None),
                "live_episodes": eps,
                "queued": self.st.one("SELECT COUNT(*) AS n FROM queue WHERE state='queued'")["n"],
                "tasks": [self.task_summary(t) for t in self.st.tasks(
                    "state IN ('active','paused','blocked','ready','stale')")],
                "outbox_pending": self.st.one("SELECT COUNT(*) AS n FROM outbox WHERE done=0")
                ["n"]}

    def run_stop(self, reason: str = "stopped by the user") -> dict:
        r = self.active_run()
        if r is None:
            return {"stopped": None}
        for e in self.st.all("SELECT * FROM episodes WHERE ended IS NULL"):
            self.episode_end(e["episode_id"], "paused", {"reason": reason})
        self.st.x("UPDATE runs SET state='stopped' WHERE run_id=?", r["run_id"])
        if r["pid"] and r["pid"] != os.getpid():
            try:
                os.kill(r["pid"], 15)
            except OSError:
                pass
        for t in self.st.tasks("state='active' AND pr IS NOT NULL"):
            try:
                self.checkpoint(t["task_id"], "heartbeat")
            except (RemoteError, ProtocolError):
                pass
        return {"stopped": r["run_id"], "reason": reason}

    def budget(self) -> float:
        r = self.active_run()
        if r is None:
            raise ProtocolError("no active run (run start)")
        cfg = json.loads(r["config"])
        left = r["deadline"] - self.clock()
        b = min(cfg["episode_seconds"], left)
        if cfg.get("max_worker_seconds"):
            b = min(b, cfg["max_worker_seconds"])
        return b

    def run_next(self) -> dict:
        """Dispatch: the next eligible item (round robin) becomes a task with a draft PR and an
        episode. Returns what the orchestrator hands its worker."""
        r = self.active_run()
        if r is None:
            raise ProtocolError("no active run (run start)")
        cfg = json.loads(r["config"])
        if self.clock() >= r["deadline"]:
            self.run_stop("the run's budget is spent")
            return {"dispatch": None, "reason": "budget spent"}
        live = self.st.one("SELECT COUNT(*) AS n FROM episodes WHERE ended IS NULL")["n"]
        if live >= cfg["max_parallel_workers"]:
            return {"dispatch": None, "reason": "all worker slots are busy"}
        item = self.next_item(cfg["allowed_domains"])
        if item is None:
            return {"dispatch": None, "reason": "no eligible work: propose work (work propose) "
                    "or wait"}
        if item["task_id"] is None:
            prop = json.loads(item["proposal"])
            try:
                t = self.task_create(prop)
            except Exception:
                self.st.x("UPDATE queue SET state='queued' WHERE seq=?", item["seq"])
                raise
            self.st.x("UPDATE queue SET task_id=? WHERE seq=?", t["task_id"], item["seq"])
            tid = t["task_id"]
        else:
            tid = item["task_id"]
        ep = self.episode_start(tid, cfg["backend"])
        return {"dispatch": ep}

    def episode_start(self, tid: str, backend: str = "interactive") -> dict:
        t = self.need(tid)
        if self.live_episode(t["task_id"]):
            raise ProtocolError(f"task {tid} already has a live episode")
        r = self.active_run()
        b = self.budget() if r else DEFAULTS["episode_seconds"]
        now = self.clock()
        eid = R.new_uuid()
        self.st.x("INSERT INTO episodes(episode_id,task_id,run_id,backend,started,deadline) "
                  "VALUES(?,?,?,?,?,?)", eid, t["task_id"], r["run_id"] if r else None, backend,
                  now, now + b)
        if t["state"] == "planned":
            self.st.update_task(t["task_id"], state="active")
        from .providers import worker_prompt
        prompt = worker_prompt(self, self.st.task(t["task_id"]), eid, b)
        p = self.task_dir(t["task_id"]) / f"episode-{eid}.md"
        p.write_text(prompt)
        return {"episode_id": eid, "task": self.task_summary(self.st.task(t["task_id"])),
                "budget_seconds": int(b), "deadline": now_iso(now + b), "prompt_file": str(p)}

    def episode_end(self, eid_or_task: str, outcome: str, result: dict | None = None) -> dict:
        e = self.st.one("SELECT * FROM episodes WHERE episode_id=? AND ended IS NULL", eid_or_task)
        if e is None:
            t = self.st.task(eid_or_task)
            e = self.live_episode(t["task_id"]) if t else None
        if e is None:
            raise ProtocolError(f"no live episode {eid_or_task}")
        if outcome not in ("unresolved", "done", "blocked", "paused", "timeout", "failed",
                           "finalized", "infra_failure"):
            raise ProtocolError("outcome: unresolved | done | blocked | paused | timeout | "
                                "failed | infra_failure")
        now = self.clock()
        self.st.x("UPDATE episodes SET ended=?, outcome=?, result=?, usage=? WHERE episode_id=?",
                  now, outcome, json.dumps(result or {}),
                  json.dumps({"wall_seconds": int(now - e["started"])}), e["episode_id"])
        t = self.st.task(e["task_id"])
        if outcome == "blocked":
            self.st.update_task(t["task_id"], state="blocked",
                                reason=(result or {}).get("reason", "blocked"))
        if outcome in ("unresolved", "timeout", "failed", "infra_failure") and \
                t["state"] == "active":
            self.enqueue_task(t)       # tail of its queue, for another bounded episode
        if outcome == "done":
            self.drop_queue(t["task_id"])
        cp = None
        if t["pr"] and outcome not in ("finalized",):
            try:
                cp = self.checkpoint(t["task_id"])
            except (RemoteError, ProtocolError) as ex:
                cp = {"error": str(ex)}
        return {"episode_id": e["episode_id"], "task": t["task_id"], "outcome": outcome,
                "checkpoint": cp}

    def end_live_episodes(self, tid: str, outcome: str) -> None:
        t = self.st.task(tid)
        if t and (e := self.live_episode(t["task_id"])):
            self.st.x("UPDATE episodes SET ended=?, outcome=? WHERE episode_id=?", self.clock(),
                      outcome, e["episode_id"])

    # -- cache -----------------------------------------------------------------------------------
    def cache_lookup(self, theorem: str) -> dict:
        dag = self.dag()
        recs = D.read_records(self.records if self.records.is_dir() else None)
        envs = {}
        for env in dag.environments():
            st = D.status(dag, recs, env)
            info = st.theorems.get(theorem)
            if info is not None:
                envs[env["id"]] = {"status": info["status"],
                                   "solutions": [p for p, r in st.solutions.items()
                                                 if r["theorem"] == theorem],
                                   "open_leaves": D.open_leaves(st, theorem)}
        attempts = self.st.all("SELECT env,context,outcome,time,detail FROM cache WHERE "
                               "theorem=? ORDER BY id", theorem)
        return {"theorem": theorem, "environments": envs, "attempts": attempts,
                "note": "attempts are advisory; reuse goes through the gate and the check"}

    def cache_record(self, theorem: str, outcome: str, detail: str = "", env: str | None = None,
                     context: str | None = None) -> dict:
        self.st.x("INSERT INTO cache(theorem,env,context,outcome,time,detail) VALUES(?,?,?,?,?,?)",
                  theorem, env, context, outcome, self.clock(), detail[:4000])
        return {"recorded": theorem, "outcome": outcome}

    # -- hooks -----------------------------------------------------------------------------------
    def hook(self, event: str, data: dict) -> dict:
        cwd = data.get("cwd") or os.getcwd()
        try:
            cwd_p = Path(cwd).resolve()
        except OSError:
            return {}
        task = None
        for t in self.st.tasks("worktree IS NOT NULL"):
            wt = Path(t["worktree"]).resolve()
            if cwd_p == wt or wt in cwd_p.parents:
                task = t
                break
        sid = str(data.get("session_id", ""))[:100] or None
        tid = task["task_id"] if task else None
        self.st.event(self.clock(), f"hook:{event}", tid, sid,
                      {k: data.get(k) for k in ("hook_event_name", "tool_name") if k in data})
        if task:
            upd = {"last_activity": self.clock()}
            if event in ("Stop", "SubagentStop"):
                upd["checkpoint_due"] = 1
            self.st.update_task(tid, **upd)
        return {}

    def hooks_install(self, provider: str, where: Path) -> dict:
        events = ["SessionStart", "PostToolUse", "Stop", "SubagentStop"]
        import shlex
        cmd = (f"{shlex.quote(sys.executable)} {shlex.quote(str(CORE / 'python' / 'sigaba_research.py'))}"
               f" --home {shlex.quote(str(self.home))} --repo {shlex.quote(self.repo)} hook --event ")
        if provider == "claude":
            f = Path(where) / ".claude" / "settings.local.json"
        elif provider == "codex":
            f = Path(where) / ".codex" / "hooks.json"
            events = ["SessionStart", "PostToolUse", "Stop"]
        else:
            raise ProtocolError("provider: claude | codex")
        f.parent.mkdir(parents=True, exist_ok=True)
        cfg = json.loads(f.read_text()) if f.exists() else {}
        hooks = cfg.setdefault("hooks", {})
        added = []
        for ev in events:
            c = cmd + ev
            groups = hooks.setdefault(ev, [])
            if any(h.get("command") == c for g in groups for h in g.get("hooks", [])):
                continue
            groups.append({"hooks": [{"type": "command", "command": c, "timeout": 10}]})
            added.append(ev)
        f.write_text(json.dumps(cfg, indent=2) + "\n")
        return {"file": str(f), "added": added}

    # -- watchdog --------------------------------------------------------------------------------
    def watchdog_step(self) -> dict:
        """One pass: due checkpoints, deadlines, stale workers, the outbox, supervised dispatch."""
        r = self.active_run()
        out = {"checkpoints": [], "timeouts": [], "stale": []}
        now = self.clock()
        if r is None:
            return out
        cfg = json.loads(r["config"])
        from . import providers
        for e in self.st.all("SELECT * FROM episodes WHERE ended IS NULL"):
            if e["pid"] and not providers.alive(e["pid"]):
                res = providers.read_result(self, e)
                self.episode_end(e["episode_id"], res.get("outcome", "unresolved"), res)
                continue
            if now > e["deadline"]:
                if e["pid"]:
                    providers.terminate(e["pid"])
                    self.episode_end(e["episode_id"], "timeout", {"reason": "deadline"})
                    out["timeouts"].append(e["task_id"])
                else:
                    t = self.st.task(e["task_id"])
                    last = max(t["last_activity"] or 0, e["started"])
                    if now - max(last, e["deadline"]) > cfg["grace_seconds"] and \
                            t["state"] != "stale":
                        self.st.update_task(t["task_id"], state="stale", checkpoint_due=1,
                                            reason="no report or activity after the deadline")
                        out["stale"].append(t["task_id"])
        out["checkpoints"] = self.checkpoint_due()
        if cfg["backend"] in ("claude", "codex"):
            while True:
                d = self.run_next()
                if not d["dispatch"]:
                    break
                ep = d["dispatch"]
                pid = providers.start(self, cfg, ep)
                self.st.x("UPDATE episodes SET pid=? WHERE episode_id=?", pid, ep["episode_id"])
        if now >= r["deadline"]:
            self.run_stop("the run's budget is spent")
        return out

    def watchdog(self, interval: float = 15.0, sleep: Callable[[float], None] = time.sleep,
                 max_steps: int | None = None) -> None:
        r = self.active_run()
        if r is None:
            raise ProtocolError("no active run")
        self.st.x("UPDATE runs SET pid=? WHERE run_id=?", os.getpid(), r["run_id"])
        steps = 0
        while True:
            cur = self.st.one("SELECT * FROM runs WHERE run_id=?", r["run_id"])
            if cur["state"] != "running":
                break
            try:
                self.watchdog_step()
            except Exception as e:      # never die silently: log and keep the clock running
                self.st.event(self.clock(), "watchdog_error", None, None, {"error": repr(e)})
            steps += 1
            if max_steps is not None and steps >= max_steps:
                break
            sleep(interval)

    # -- doctor and skills -----------------------------------------------------------------------
    def doctor(self) -> dict:
        out = {"home": str(self.home), "repo": self.repo, "core": str(CORE)}
        import subprocess
        for tool in ("git", "gh", "lake", "claude", "codex"):
            p = shutil.which(tool)
            out[tool] = p or None
        try:
            out["login"] = self.gh.login()
            out["can_push"] = self.gh.can_push()
        except Exception as e:     # report, never print tokens
            out["github_error"] = str(e)[:500]
        out["public_writes_authorized"] = bool(self.st.get(f"authorized:{self.repo}", False))
        out["core_built"] = (CORE / ".lake" / "build").is_dir()
        out["lean_toolchain"] = (CORE / "lean-toolchain").read_text().strip()
        if out.get("gh"):
            r = subprocess.run(["gh", "auth", "status"], capture_output=True, text=True)
            out["gh_auth"] = r.returncode == 0
        out["skills_in_sync"] = not skills_diff()
        return out


def run_bytes(argv: list[str]) -> bytes:
    import subprocess
    p = subprocess.run(argv, capture_output=True)
    if p.returncode != 0:
        raise RemoteError(p.stderr.decode(errors="replace"), "protocol")
    return p.stdout


def git_blob_sha(data: bytes) -> str:
    import hashlib
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def build_graph(plans: list[dict], known_tasks: set[str] | None = None) -> dict:
    """The AND-OR research graph from plans: alternatives per target, unresolved members, and
    plans dropped (in plan_id order) because they would close a cycle."""
    edges: dict[str, set[str]] = {}
    kept, dropped, problems = [], [], []

    def reach(a: str, b: str) -> bool:
        seen, todo = set(), [a]
        while todo:
            x = todo.pop()
            if x == b:
                return True
            if x in seen:
                continue
            seen.add(x)
            todo += edges.get(x, ())
        return False

    seen_ids = set()
    for p in sorted(plans, key=lambda p: p["plan_id"]):
        if p["plan_id"] in seen_ids:
            continue
        seen_ids.add(p["plan_id"])
        tgt = p["target"]["id"]
        if any(reach(m, tgt) or m == tgt for m in p["required"]):
            dropped.append(p["plan_id"])
            problems.append(f"plan {p['plan_id']} would close a cycle at {tgt}")
            continue
        edges.setdefault(tgt, set()).update(p["required"])
        kept.append(p)
    alternatives: dict[str, list[str]] = {}
    unresolved: dict[str, list[str]] = {}
    for p in kept:
        alternatives.setdefault(p["target"]["id"], []).append(p["plan_id"])
        if known_tasks is not None:
            miss = [m for m in p["required"] if m not in known_tasks]
            if miss:
                unresolved[p["plan_id"]] = miss
    return {"alternatives": alternatives, "unresolved": unresolved, "dropped": dropped,
            "problems": problems}


def skills_diff() -> list[str]:
    """Skill files that differ between `.claude/skills` (the source) and `.agents/skills`."""
    src, dst = CORE / ".claude" / "skills", CORE / ".agents" / "skills"
    out = []
    files = {p.relative_to(src) for p in src.rglob("*") if p.is_file()}
    other = {p.relative_to(dst) for p in dst.rglob("*") if p.is_file()} if dst.is_dir() else set()
    for f in sorted(files | other):
        a, b = src / f, dst / f
        if not a.exists() or not b.exists() or a.read_bytes() != b.read_bytes():
            out.append(str(f))
    return out


def skills_sync() -> list[str]:
    src, dst = CORE / ".claude" / "skills", CORE / ".agents" / "skills"
    changed = skills_diff()
    if dst.exists():
        shutil.rmtree(dst)
    shutil.copytree(src, dst)
    return changed
